use crate::counterexample::Value;
use crate::ir::{ExprKind, Relation, RelationNode, ScalarFunction, SortKey, TypedExpr, TypedQuery};
use crate::schema::DataType;

pub(crate) fn normalize_query(query: &mut TypedQuery) {
    normalize_relation(&mut query.root);
}

fn normalize_relation(relation: &mut Relation) {
    match &mut relation.node {
        RelationNode::Unit | RelationNode::Scan { .. } => {}
        RelationNode::Product { left, right } => {
            normalize_relation(left);
            normalize_relation(right);
        }
        RelationNode::Join {
            left, right, on, ..
        } => {
            normalize_relation(left);
            normalize_relation(right);
            normalize_expr(on);
        }
        RelationNode::Filter { input, predicate } => {
            normalize_relation(input);
            normalize_expr(predicate);
        }
        RelationNode::Project { input, expressions } => {
            normalize_relation(input);
            expressions.iter_mut().for_each(normalize_expr);
        }
        RelationNode::Distinct { input } => normalize_relation(input),
        RelationNode::SetOperation { left, right, .. } => {
            normalize_relation(left);
            normalize_relation(right);
        }
        RelationNode::Aggregate {
            input,
            group_by,
            expressions,
            having,
        } => {
            normalize_relation(input);
            group_by.iter_mut().for_each(normalize_expr);
            expressions.iter_mut().for_each(normalize_expr);
            if let Some(having) = having {
                normalize_expr(having);
            }
        }
        RelationNode::Sort { input, keys } => {
            normalize_relation(input);
            keys.iter_mut().for_each(normalize_sort_key);
        }
        RelationNode::Slice { input, .. } => normalize_relation(input),
    }
}

fn normalize_sort_key(key: &mut SortKey) {
    normalize_expr(&mut key.expression);
}

fn normalize_expr(expression: &mut TypedExpr) {
    match &mut expression.kind {
        ExprKind::Column(_) | ExprKind::OuterColumn { .. } | ExprKind::Literal(_) => {}
        ExprKind::Compare { left, right, .. } | ExprKind::Arithmetic { left, right, .. } => {
            normalize_expr(left);
            normalize_expr(right);
        }
        ExprKind::And(left, right) | ExprKind::Or(left, right) => {
            normalize_expr(left);
            normalize_expr(right);
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner) => normalize_expr(inner),
        ExprKind::Coalesce(expressions) | ExprKind::CountDistinctRow { expressions } => {
            expressions.iter_mut().for_each(normalize_expr);
        }
        ExprKind::Case {
            branches,
            else_result,
        } => {
            for (condition, result) in branches {
                normalize_expr(condition);
                normalize_expr(result);
            }
            normalize_expr(else_result);
        }
        ExprKind::Cast {
            expression: inner, ..
        } => normalize_expr(inner),
        ExprKind::ScalarFunction { arguments, .. } => {
            arguments.iter_mut().for_each(normalize_expr);
        }
        ExprKind::Aggregate { expression, .. } => {
            if let Some(expression) = expression {
                normalize_expr(expression);
            }
        }
        ExprKind::Exists { query, .. } | ExprKind::ScalarSubquery { query } => {
            normalize_relation(query);
        }
        ExprKind::InSubquery {
            expressions, query, ..
        } => {
            expressions.iter_mut().for_each(normalize_expr);
            normalize_relation(query);
        }
        ExprKind::WindowRank {
            partition_by,
            order_by,
            ..
        } => {
            partition_by.iter_mut().for_each(normalize_expr);
            order_by.iter_mut().for_each(normalize_sort_key);
        }
        ExprKind::WindowAggregate {
            expression,
            partition_by,
            order_by,
            ..
        } => {
            if let Some(expression) = expression {
                normalize_expr(expression);
            }
            partition_by.iter_mut().for_each(normalize_expr);
            order_by.iter_mut().for_each(normalize_sort_key);
        }
        ExprKind::FirstValue {
            expression,
            partition_by,
            order_by,
        } => {
            normalize_expr(expression);
            partition_by.iter_mut().for_each(normalize_expr);
            order_by.iter_mut().for_each(normalize_sort_key);
        }
    }

    canonicalize_round_scale(expression);
    factor_round_out_of_case(expression);
}

fn canonicalize_round_scale(expression: &mut TypedExpr) {
    let ExprKind::ScalarFunction {
        function: ScalarFunction::Round,
        arguments,
    } = &mut expression.kind
    else {
        return;
    };
    if arguments.len() == 1 {
        arguments.push(round_scale_expr(0));
    }
}

fn factor_round_out_of_case(expression: &mut TypedExpr) {
    if expression.data_type != DataType::Numeric {
        return;
    }
    let ExprKind::Case {
        branches,
        else_result,
    } = &expression.kind
    else {
        return;
    };

    let results = branches
        .iter()
        .map(|(_, result)| result)
        .chain(std::iter::once(else_result.as_ref()))
        .collect::<Vec<_>>();
    let Some(scale) = common_round_scale(&results) else {
        return;
    };
    let Some(unrounded_results) = results
        .iter()
        .map(|result| unround_result(result, scale))
        .collect::<Option<Vec<_>>>()
    else {
        return;
    };

    // ROUND is deterministic and NULL-propagating, so applying one shared ROUND
    // after CASE is equivalent to applying it to each selected result. Keeping a
    // single operation avoids duplicating real-to-integer conversions under ITEs.
    let branch_count = branches.len();
    let normalized_branches = branches
        .iter()
        .zip(unrounded_results[..branch_count].iter())
        .map(|((condition, _), result)| (condition.clone(), result.clone()))
        .collect();
    let normalized_else = unrounded_results
        .last()
        .expect("CASE normalization always includes an ELSE result")
        .clone();
    let normalized_case = TypedExpr {
        data_type: expression.data_type,
        nullable: expression.nullable,
        kind: ExprKind::Case {
            branches: normalized_branches,
            else_result: Box::new(normalized_else),
        },
    };
    expression.kind = ExprKind::ScalarFunction {
        function: ScalarFunction::Round,
        arguments: vec![normalized_case, round_scale_expr(scale)],
    };
}

fn common_round_scale(results: &[&TypedExpr]) -> Option<i64> {
    let scales = results
        .iter()
        .filter_map(|result| round_parts(result).map(|(_, scale)| scale));
    let mut scales = scales.peekable();
    let common = *scales.peek()?;
    scales.all(|scale| scale == common).then_some(common)
}

fn unround_result(expression: &TypedExpr, scale: i64) -> Option<TypedExpr> {
    match round_parts(expression) {
        Some((inner, inner_scale)) if inner_scale == scale => Some(inner.clone()),
        Some(_) => None,
        None if fixed_by_round(expression, scale) => Some(expression.clone()),
        None => None,
    }
}

fn round_parts(expression: &TypedExpr) -> Option<(&TypedExpr, i64)> {
    let ExprKind::ScalarFunction {
        function: ScalarFunction::Round,
        arguments,
    } = &expression.kind
    else {
        return None;
    };
    let [inner, scale] = arguments.as_slice() else {
        return None;
    };
    typed_integer_literal(scale).map(|scale| (inner, scale))
}

fn fixed_by_round(expression: &TypedExpr, scale: i64) -> bool {
    if scale != 0 {
        return false;
    }
    match &expression.kind {
        ExprKind::Literal(Value::Null) => true,
        ExprKind::Literal(Value::Numeric(value)) => value.denominator() == 1,
        ExprKind::Cast {
            expression: inner,
            to: DataType::Numeric,
        } => inner.data_type == DataType::Integer,
        _ => false,
    }
}

fn typed_integer_literal(expression: &TypedExpr) -> Option<i64> {
    match expression.kind {
        ExprKind::Literal(Value::Integer(value)) => Some(value),
        _ => None,
    }
}

fn round_scale_expr(scale: i64) -> TypedExpr {
    TypedExpr::literal(Value::Integer(scale), DataType::Integer, false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::counterexample::ExactNumeric;

    #[test]
    fn canonicalizes_omitted_round_scale() {
        let mut expression = round(numeric_column(0), None);

        normalize_expr(&mut expression);

        let ExprKind::ScalarFunction {
            function: ScalarFunction::Round,
            arguments,
        } = &expression.kind
        else {
            panic!("ROUND should remain a scalar function");
        };
        assert_eq!(arguments.len(), 2);
        assert_eq!(typed_integer_literal(&arguments[1]), Some(0));
    }

    #[test]
    fn factors_round_out_of_case_with_integer_and_null_fixed_points() {
        let mut expression = numeric_case(
            vec![
                round(numeric_column(0), None),
                cast_integer_to_numeric(integer_column(1)),
            ],
            TypedExpr::literal(Value::Null, DataType::Numeric, true),
        );

        normalize_expr(&mut expression);

        let ExprKind::ScalarFunction {
            function: ScalarFunction::Round,
            arguments,
        } = &expression.kind
        else {
            panic!("CASE should be wrapped in ROUND");
        };
        assert_eq!(typed_integer_literal(&arguments[1]), Some(0));
        let ExprKind::Case {
            branches,
            else_result,
        } = &arguments[0].kind
        else {
            panic!("ROUND should contain the normalized CASE");
        };
        assert!(matches!(branches[0].1.kind, ExprKind::Column(0)));
        assert!(matches!(branches[1].1.kind, ExprKind::Cast { .. }));
        assert!(matches!(else_result.kind, ExprKind::Literal(Value::Null)));
    }

    #[test]
    fn treats_integral_numeric_literals_as_round_fixed_points() {
        let mut expression = numeric_case(
            vec![round(numeric_column(0), Some(0))],
            TypedExpr::literal(
                Value::Numeric(ExactNumeric::from_integer(7)),
                DataType::Numeric,
                false,
            ),
        );

        normalize_expr(&mut expression);

        assert!(matches!(
            expression.kind,
            ExprKind::ScalarFunction {
                function: ScalarFunction::Round,
                ..
            }
        ));
    }

    #[test]
    fn recursively_factors_nested_cases() {
        let inner = numeric_case(
            vec![round(numeric_column(0), None)],
            cast_integer_to_numeric(integer_column(1)),
        );
        let mut expression = numeric_case(vec![inner], round(numeric_column(2), Some(0)));

        normalize_expr(&mut expression);

        let ExprKind::ScalarFunction { arguments, .. } = &expression.kind else {
            panic!("outer CASE should be wrapped in ROUND");
        };
        let ExprKind::Case { branches, .. } = &arguments[0].kind else {
            panic!("outer ROUND should contain a CASE");
        };
        assert!(matches!(branches[0].1.kind, ExprKind::Case { .. }));
    }

    #[test]
    fn does_not_factor_rounds_with_mixed_scales() {
        let mut expression = numeric_case(
            vec![
                round(numeric_column(0), Some(0)),
                round(numeric_column(1), Some(1)),
            ],
            round(numeric_column(2), Some(0)),
        );

        normalize_expr(&mut expression);

        assert!(matches!(expression.kind, ExprKind::Case { .. }));
    }

    #[test]
    fn does_not_factor_over_arbitrary_unrounded_numeric_branch() {
        let mut expression =
            numeric_case(vec![round(numeric_column(0), Some(0))], numeric_column(1));

        normalize_expr(&mut expression);

        assert!(matches!(expression.kind, ExprKind::Case { .. }));
    }

    fn numeric_case(results: Vec<TypedExpr>, else_result: TypedExpr) -> TypedExpr {
        let nullable = else_result.nullable || results.iter().any(|result| result.nullable);
        TypedExpr {
            data_type: DataType::Numeric,
            nullable,
            kind: ExprKind::Case {
                branches: results
                    .into_iter()
                    .map(|result| {
                        (
                            TypedExpr::literal(Value::Boolean(true), DataType::Boolean, false),
                            result,
                        )
                    })
                    .collect(),
                else_result: Box::new(else_result),
            },
        }
    }

    fn round(value: TypedExpr, scale: Option<i64>) -> TypedExpr {
        let nullable = value.nullable;
        let mut arguments = vec![value];
        if let Some(scale) = scale {
            arguments.push(round_scale_expr(scale));
        }
        TypedExpr {
            data_type: DataType::Numeric,
            nullable,
            kind: ExprKind::ScalarFunction {
                function: ScalarFunction::Round,
                arguments,
            },
        }
    }

    fn numeric_column(index: usize) -> TypedExpr {
        TypedExpr {
            data_type: DataType::Numeric,
            nullable: false,
            kind: ExprKind::Column(index),
        }
    }

    fn integer_column(index: usize) -> TypedExpr {
        TypedExpr {
            data_type: DataType::Integer,
            nullable: false,
            kind: ExprKind::Column(index),
        }
    }

    fn cast_integer_to_numeric(expression: TypedExpr) -> TypedExpr {
        TypedExpr {
            data_type: DataType::Numeric,
            nullable: expression.nullable,
            kind: ExprKind::Cast {
                expression: Box::new(expression),
                to: DataType::Numeric,
            },
        }
    }
}
