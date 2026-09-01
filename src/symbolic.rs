use std::collections::BTreeSet;
use std::time::Instant;

use z3::Model;
use z3::ast::{Bool, Int, Real, String as Z3String};

use crate::concrete::ConcreteDatabase;
use crate::counterexample::{DateValue, ExactNumeric, Row, TimeValue, Value};
use crate::ir::{
    AggregateFunction, ArithmeticOp, ColumnMeta, CompareOp, ExprKind, JoinKind, Relation,
    RelationNode, ScalarFunction, SetOp, SortKey, TypedExpr, TypedQuery, WindowRankFunction,
};
use crate::metrics::{Counter, MetricsRecorder, Phase, measure};
use crate::outcome::{UnsupportedKind, UnsupportedReason};
use crate::schema::{
    ColumnRef, ConstraintComparison, ConstraintOperand, ConstraintPredicate, DataType,
    IntegrityConstraint, Schema, canonical_name, value_data_type,
};

#[derive(Clone, Debug)]
pub(crate) struct SymbolicDatabase {
    pub tables: Vec<SymbolicTable>,
}

#[derive(Clone, Debug)]
pub(crate) struct SymbolicTable {
    pub rows: Vec<SymbolicRow>,
}

#[derive(Clone, Debug)]
pub(crate) struct SymbolicRelation {
    pub rows: Vec<SymbolicRow>,
}

#[derive(Clone, Debug)]
pub(crate) struct SymbolicRow {
    pub live: Bool,
    pub values: Vec<SymbolicValue>,
}

#[derive(Clone, Debug)]
pub(crate) struct SymbolicValue {
    data_type: DataType,
    is_null: Bool,
    scalar: SymbolicScalar,
}

#[derive(Clone, Debug)]
enum SymbolicScalar {
    Integer(Int),
    Boolean(Bool),
    String(Z3String),
    Numeric(Real),
}

pub(crate) fn build_database(
    schema: &Schema,
    bound: usize,
    metrics: Option<&MetricsRecorder>,
) -> Result<(SymbolicDatabase, Vec<Bool>), UnsupportedReason> {
    let database_started = metrics.map(|_| Instant::now());
    let mut constraints = Vec::new();
    let mut tables = Vec::with_capacity(schema.tables.len());

    for (table_index, table) in schema.tables.iter().enumerate() {
        let mut rows = Vec::with_capacity(bound);
        for row_index in 0..bound {
            let live = Bool::new_const(format!("t{table_index}_r{row_index}_live"));
            let mut values = Vec::with_capacity(table.columns.len());
            for (column_index, column) in table.columns.iter().enumerate() {
                let is_null =
                    Bool::new_const(format!("t{table_index}_r{row_index}_c{column_index}_null"));
                let scalar = match column.data_type {
                    DataType::Integer => {
                        let value = Int::new_const(format!(
                            "t{table_index}_r{row_index}_c{column_index}_integer"
                        ));
                        constraints.push(value.ge(Int::from_i64(i64::MIN)));
                        constraints.push(value.le(Int::from_i64(i64::MAX)));
                        SymbolicScalar::Integer(value)
                    }
                    DataType::Boolean => SymbolicScalar::Boolean(Bool::new_const(format!(
                        "t{table_index}_r{row_index}_c{column_index}_boolean"
                    ))),
                    DataType::Text | DataType::Enum => SymbolicScalar::String(Z3String::new_const(
                        format!("t{table_index}_r{row_index}_c{column_index}_string"),
                    )),
                    DataType::Date => {
                        let value = Int::new_const(format!(
                            "t{table_index}_r{row_index}_c{column_index}_date"
                        ));
                        constraints.push(value.ge(Int::from_i64(i64::from(i32::MIN))));
                        constraints.push(value.le(Int::from_i64(i64::from(i32::MAX))));
                        SymbolicScalar::Integer(value)
                    }
                    DataType::Time => {
                        let value = Int::new_const(format!(
                            "t{table_index}_r{row_index}_c{column_index}_time"
                        ));
                        constraints.push(value.ge(Int::from_i64(0)));
                        constraints.push(value.lt(Int::from_i64(TimeValue::NANOS_PER_DAY)));
                        SymbolicScalar::Integer(value)
                    }
                    DataType::Numeric => SymbolicScalar::Numeric(Real::new_const(format!(
                        "t{table_index}_r{row_index}_c{column_index}_numeric"
                    ))),
                };
                if !column.nullable {
                    constraints.push(live.implies(is_null.not()));
                }
                values.push(SymbolicValue {
                    data_type: column.data_type,
                    is_null,
                    scalar,
                });
                if column.data_type == DataType::Enum {
                    let SymbolicScalar::String(value) =
                        &values.last().expect("the value was just pushed").scalar
                    else {
                        unreachable!("enum values use symbolic strings");
                    };
                    let in_domain = or_many(
                        column
                            .enum_values
                            .iter()
                            .map(|variant| value.eq(Z3String::from(variant.as_str()))),
                    );
                    constraints.push(
                        and_all([
                            live.clone(),
                            values
                                .last()
                                .expect("the value was just pushed")
                                .is_null
                                .not(),
                        ])
                        .implies(in_domain),
                    );
                }
            }
            rows.push(SymbolicRow { live, values });
        }
        if let Some(metrics) = metrics {
            metrics.add(Counter::BaseRows, rows.len());
        }

        // Make live row slots a prefix of the fixed slot vector. This preserves
        // every possible bag while eliminating redundant models with dead gaps.
        for adjacent in rows.windows(2) {
            constraints.push(adjacent[1].live.implies(adjacent[0].live.clone()));
        }

        if let Some(primary_key) = &table.primary_key {
            let key_indices = primary_key
                .iter()
                .map(|key| {
                    let key = canonical_name(key);
                    table
                        .columns
                        .iter()
                        .position(|column| canonical_name(&column.name) == key)
                        .ok_or_else(|| {
                            internal(format!(
                                "validated primary key for `{}` lost column `{key}`",
                                table.name
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;

            for row in &rows {
                for key_index in &key_indices {
                    constraints.push(row.live.implies(row.values[*key_index].is_null.not()));
                }
            }
            for left_index in 0..rows.len() {
                for right_index in (left_index + 1)..rows.len() {
                    let left = &rows[left_index];
                    let right = &rows[right_index];
                    let differences = key_indices
                        .iter()
                        .map(|key_index| {
                            scalar_equal(
                                &left.values[*key_index].scalar,
                                &right.values[*key_index].scalar,
                            )
                            .map(|equal| equal.not())
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    constraints.push(
                        and_all([left.live.clone(), right.live.clone()])
                            .implies(or_many(differences)),
                    );
                }
            }
        }

        tables.push(SymbolicTable { rows });
    }

    let database = SymbolicDatabase { tables };
    if let (Some(metrics), Some(started)) = (metrics, database_started) {
        metrics.add_phase(Phase::SymbolicDatabaseConstruction, started.elapsed());
    }
    measure(metrics, Phase::SchemaConstraintConstruction, || {
        encode_integrity_constraints(schema, &database, &mut constraints)
    })?;
    if let Some(metrics) = metrics {
        metrics.set(Counter::SchemaConstraints, constraints.len());
    }
    Ok((database, constraints))
}

fn encode_integrity_constraints(
    schema: &Schema,
    database: &SymbolicDatabase,
    constraints: &mut Vec<Bool>,
) -> Result<(), UnsupportedReason> {
    for constraint in &schema.constraints {
        match constraint {
            IntegrityConstraint::PrimaryKey { columns } => {
                encode_unique_key(schema, database, columns, true, constraints)?;
            }
            IntegrityConstraint::Unique { columns } => {
                encode_unique_key(schema, database, columns, false, constraints)?;
            }
            IntegrityConstraint::ForeignKey {
                columns,
                referenced_columns,
            } => encode_foreign_key(schema, database, columns, referenced_columns, constraints)?,
            IntegrityConstraint::Check { predicate } => {
                encode_check(schema, database, predicate, constraints)?;
            }
            IntegrityConstraint::AutoIncrement { column } => {
                encode_sequence(schema, database, column, false, constraints)?;
            }
            IntegrityConstraint::Consecutive { column } => {
                encode_sequence(schema, database, column, true, constraints)?;
            }
        }
    }
    Ok(())
}

fn encode_unique_key(
    schema: &Schema,
    database: &SymbolicDatabase,
    columns: &[ColumnRef],
    primary: bool,
    constraints: &mut Vec<Bool>,
) -> Result<(), UnsupportedReason> {
    let indices = columns
        .iter()
        .map(|column| {
            schema
                .resolve_column(column)
                .map(|(table, column, _)| (table, column))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let table_index = indices
        .first()
        .map(|(table, _)| *table)
        .ok_or_else(|| internal("validated key became empty"))?;
    let rows = &database
        .tables
        .get(table_index)
        .ok_or_else(|| internal("symbolic database lost a key table"))?
        .rows;

    if primary {
        for row in rows {
            for (_, column_index) in &indices {
                constraints.push(row.live.implies(row.values[*column_index].is_null.not()));
            }
        }
    }
    for left_index in 0..rows.len() {
        for right_index in (left_index + 1)..rows.len() {
            let left = &rows[left_index];
            let right = &rows[right_index];
            let both_non_null = indices.iter().flat_map(|(_, column_index)| {
                [
                    left.values[*column_index].is_null.not(),
                    right.values[*column_index].is_null.not(),
                ]
            });
            let equalities = indices
                .iter()
                .map(|(_, column_index)| {
                    scalar_equal(
                        &left.values[*column_index].scalar,
                        &right.values[*column_index].scalar,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut conflict_guard = vec![left.live.clone(), right.live.clone()];
            if !primary {
                conflict_guard.extend(both_non_null);
            }
            constraints.push(and_many(conflict_guard).implies(and_many(equalities).not()));
        }
    }
    Ok(())
}

fn encode_foreign_key(
    schema: &Schema,
    database: &SymbolicDatabase,
    columns: &[ColumnRef],
    referenced_columns: &[ColumnRef],
    constraints: &mut Vec<Bool>,
) -> Result<(), UnsupportedReason> {
    let source_indices = resolve_indices(schema, columns)?;
    let target_indices = resolve_indices(schema, referenced_columns)?;
    let source_table = source_indices
        .first()
        .map(|(table, _)| *table)
        .ok_or_else(|| internal("validated foreign key became empty"))?;
    let target_table = target_indices
        .first()
        .map(|(table, _)| *table)
        .ok_or_else(|| internal("validated referenced key became empty"))?;
    let source_rows = &database.tables[source_table].rows;
    let target_rows = &database.tables[target_table].rows;
    for source in source_rows {
        let all_non_null = and_many(
            source_indices
                .iter()
                .map(|(_, column)| source.values[*column].is_null.not()),
        );
        let matches = target_rows
            .iter()
            .map(|target| {
                let equalities = source_indices
                    .iter()
                    .zip(&target_indices)
                    .map(|((_, source_column), (_, target_column))| {
                        Ok(and_all([
                            target.values[*target_column].is_null.not(),
                            scalar_equal(
                                &source.values[*source_column].scalar,
                                &target.values[*target_column].scalar,
                            )?,
                        ]))
                    })
                    .collect::<Result<Vec<_>, UnsupportedReason>>()?;
                Ok(and_many(
                    std::iter::once(target.live.clone()).chain(equalities),
                ))
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        constraints.push(and_all([source.live.clone(), all_non_null]).implies(or_many(matches)));
    }
    Ok(())
}

fn encode_check(
    schema: &Schema,
    database: &SymbolicDatabase,
    predicate: &ConstraintPredicate,
    constraints: &mut Vec<Bool>,
) -> Result<(), UnsupportedReason> {
    let mut table_indices = BTreeSet::new();
    collect_predicate_tables(schema, predicate, &mut table_indices)?;
    let table_indices = table_indices.into_iter().collect::<Vec<_>>();
    for assignment in row_assignments(database, &table_indices) {
        let guard = and_many(
            assignment
                .iter()
                .map(|(table, row)| database.tables[*table].rows[*row].live.clone()),
        );
        let value = eval_constraint_predicate(schema, database, predicate, &assignment)?;
        constraints.push(guard.implies(value.is_false()?.not()));
    }
    Ok(())
}

fn encode_sequence(
    schema: &Schema,
    database: &SymbolicDatabase,
    column: &ColumnRef,
    consecutive: bool,
    constraints: &mut Vec<Bool>,
) -> Result<(), UnsupportedReason> {
    let (table_index, column_index, _) = schema.resolve_column(column)?;
    let rows = &database.tables[table_index].rows;
    for row in rows {
        constraints.push(row.live.implies(row.values[column_index].is_null.not()));
    }
    for adjacent in rows.windows(2) {
        let [left, right] = adjacent else {
            unreachable!("windows of two always contain two rows");
        };
        let (SymbolicScalar::Integer(left_value), SymbolicScalar::Integer(right_value)) = (
            &left.values[column_index].scalar,
            &right.values[column_index].scalar,
        ) else {
            return Err(internal("validated sequence column is not an integer"));
        };
        let relation = if consecutive {
            right_value.eq(left_value + Int::from_i64(1))
        } else {
            right_value.gt(left_value)
        };
        constraints.push(and_all([left.live.clone(), right.live.clone()]).implies(relation));
    }
    Ok(())
}

fn resolve_indices(
    schema: &Schema,
    columns: &[ColumnRef],
) -> Result<Vec<(usize, usize)>, UnsupportedReason> {
    columns
        .iter()
        .map(|column| {
            schema
                .resolve_column(column)
                .map(|(table, column, _)| (table, column))
        })
        .collect()
}

fn collect_predicate_tables(
    schema: &Schema,
    predicate: &ConstraintPredicate,
    tables: &mut BTreeSet<usize>,
) -> Result<(), UnsupportedReason> {
    match predicate {
        ConstraintPredicate::Compare { left, right, .. } => {
            collect_operand_table(schema, left, tables)?;
            collect_operand_table(schema, right, tables)?;
        }
        ConstraintPredicate::Between {
            value,
            lower,
            upper,
        } => {
            for operand in [value, lower, upper] {
                collect_operand_table(schema, operand, tables)?;
            }
        }
        ConstraintPredicate::In { value, choices } => {
            collect_operand_table(schema, value, tables)?;
            for choice in choices {
                collect_operand_table(schema, choice, tables)?;
            }
        }
        ConstraintPredicate::Implies {
            premise,
            conclusion,
        } => {
            collect_predicate_tables(schema, premise, tables)?;
            collect_predicate_tables(schema, conclusion, tables)?;
        }
    }
    Ok(())
}

fn collect_operand_table(
    schema: &Schema,
    operand: &ConstraintOperand,
    tables: &mut BTreeSet<usize>,
) -> Result<(), UnsupportedReason> {
    if let ConstraintOperand::Column(column) = operand {
        tables.insert(schema.resolve_column(column)?.0);
    }
    Ok(())
}

fn row_assignments(
    database: &SymbolicDatabase,
    table_indices: &[usize],
) -> Vec<Vec<(usize, usize)>> {
    let mut assignments = vec![Vec::new()];
    for table_index in table_indices {
        let mut expanded = Vec::new();
        for assignment in &assignments {
            for row_index in 0..database.tables[*table_index].rows.len() {
                let mut next = assignment.clone();
                next.push((*table_index, row_index));
                expanded.push(next);
            }
        }
        assignments = expanded;
    }
    assignments
}

fn eval_constraint_predicate(
    schema: &Schema,
    database: &SymbolicDatabase,
    predicate: &ConstraintPredicate,
    assignment: &[(usize, usize)],
) -> Result<SymbolicValue, UnsupportedReason> {
    match predicate {
        ConstraintPredicate::Compare { op, left, right } => {
            let data_type = constraint_operand_type(schema, left)?
                .or(constraint_operand_type(schema, right)?)
                .ok_or_else(|| internal("validated comparison lost its operand type"))?;
            let left = eval_constraint_operand(schema, database, left, data_type, assignment)?;
            let right = eval_constraint_operand(schema, database, right, data_type, assignment)?;
            let op = match op {
                ConstraintComparison::Equal => CompareOp::Equal,
                ConstraintComparison::NotEqual => CompareOp::NotEqual,
                ConstraintComparison::Less => CompareOp::Less,
                ConstraintComparison::LessOrEqual => CompareOp::LessOrEqual,
                ConstraintComparison::Greater => CompareOp::Greater,
                ConstraintComparison::GreaterOrEqual => CompareOp::GreaterOrEqual,
            };
            let scalar = compare_scalars(op, &left.scalar, &right.scalar)?;
            Ok(SymbolicValue {
                data_type: DataType::Boolean,
                is_null: or_all([left.is_null, right.is_null]),
                scalar: SymbolicScalar::Boolean(scalar),
            })
        }
        ConstraintPredicate::Between {
            value,
            lower,
            upper,
        } => {
            let lower = eval_constraint_predicate(
                schema,
                database,
                &ConstraintPredicate::Compare {
                    op: ConstraintComparison::GreaterOrEqual,
                    left: value.clone(),
                    right: lower.clone(),
                },
                assignment,
            )?;
            let upper = eval_constraint_predicate(
                schema,
                database,
                &ConstraintPredicate::Compare {
                    op: ConstraintComparison::LessOrEqual,
                    left: value.clone(),
                    right: upper.clone(),
                },
                assignment,
            )?;
            symbolic_and(lower, upper)
        }
        ConstraintPredicate::In { value, choices } => {
            let mut result = symbolic_boolean(false);
            for choice in choices {
                let equal = eval_constraint_predicate(
                    schema,
                    database,
                    &ConstraintPredicate::Compare {
                        op: ConstraintComparison::Equal,
                        left: value.clone(),
                        right: choice.clone(),
                    },
                    assignment,
                )?;
                result = symbolic_or(result, equal)?;
            }
            Ok(result)
        }
        ConstraintPredicate::Implies {
            premise,
            conclusion,
        } => {
            let premise = eval_constraint_predicate(schema, database, premise, assignment)?;
            let conclusion = eval_constraint_predicate(schema, database, conclusion, assignment)?;
            symbolic_or(symbolic_not(premise)?, conclusion)
        }
    }
}

fn eval_constraint_operand(
    schema: &Schema,
    database: &SymbolicDatabase,
    operand: &ConstraintOperand,
    expected: DataType,
    assignment: &[(usize, usize)],
) -> Result<SymbolicValue, UnsupportedReason> {
    match operand {
        ConstraintOperand::Column(column) => {
            let (table_index, column_index, _) = schema.resolve_column(column)?;
            let row_index = assignment
                .iter()
                .find_map(|(table, row)| (*table == table_index).then_some(*row))
                .ok_or_else(|| internal("constraint row assignment is missing a table"))?;
            Ok(database.tables[table_index].rows[row_index].values[column_index].clone())
        }
        ConstraintOperand::Literal(value) => Ok(symbolic_literal(value, expected)),
    }
}

fn constraint_operand_type(
    schema: &Schema,
    operand: &ConstraintOperand,
) -> Result<Option<DataType>, UnsupportedReason> {
    Ok(match operand {
        ConstraintOperand::Column(column) => Some(schema.resolve_column(column)?.2.data_type),
        ConstraintOperand::Literal(value) => value_data_type(value),
    })
}

pub(crate) fn encode_query(
    query: &TypedQuery,
    database: &SymbolicDatabase,
    metrics: Option<&MetricsRecorder>,
) -> Result<SymbolicRelation, UnsupportedReason> {
    if let Some(metrics) = metrics {
        metrics.add(
            Counter::InvariantSubquerySubtrees,
            count_invariant_subqueries(&query.root),
        );
    }
    let context = SymbolicEvalContext {
        database,
        outer_rows: Vec::new(),
        metrics,
        nesting_depth: 0,
    };
    encode_relation(&query.root, &context)
}

#[derive(Clone)]
struct SymbolicEvalContext<'database> {
    database: &'database SymbolicDatabase,
    outer_rows: Vec<Vec<SymbolicValue>>,
    metrics: Option<&'database MetricsRecorder>,
    nesting_depth: usize,
}

fn count_invariant_subqueries(relation: &Relation) -> usize {
    let mut count = 0;
    collect_invariant_subqueries(relation, &mut count);
    count
}

fn collect_invariant_subqueries(relation: &Relation, count: &mut usize) {
    match &relation.node {
        RelationNode::Unit | RelationNode::Scan { .. } => {}
        RelationNode::Product { left, right } => {
            collect_invariant_subqueries(left, count);
            collect_invariant_subqueries(right, count);
        }
        RelationNode::Join {
            left, right, on, ..
        } => {
            collect_invariant_subqueries(left, count);
            collect_invariant_subqueries(right, count);
            collect_invariant_subqueries_from_expr(on, count);
        }
        RelationNode::Filter { input, predicate } => {
            collect_invariant_subqueries(input, count);
            collect_invariant_subqueries_from_expr(predicate, count);
        }
        RelationNode::Project { input, expressions } => {
            collect_invariant_subqueries(input, count);
            for expression in expressions {
                collect_invariant_subqueries_from_expr(expression, count);
            }
        }
        RelationNode::Distinct { input } | RelationNode::Slice { input, .. } => {
            collect_invariant_subqueries(input, count);
        }
        RelationNode::SetOperation { left, right, .. } => {
            collect_invariant_subqueries(left, count);
            collect_invariant_subqueries(right, count);
        }
        RelationNode::Aggregate {
            input,
            group_by,
            expressions,
            having,
        } => {
            collect_invariant_subqueries(input, count);
            for expression in group_by.iter().chain(expressions) {
                collect_invariant_subqueries_from_expr(expression, count);
            }
            if let Some(having) = having {
                collect_invariant_subqueries_from_expr(having, count);
            }
        }
        RelationNode::Sort { input, keys } => {
            collect_invariant_subqueries(input, count);
            for key in keys {
                collect_invariant_subqueries_from_expr(&key.expression, count);
            }
        }
    }
}

fn collect_invariant_subqueries_from_expr(expression: &TypedExpr, count: &mut usize) {
    match &expression.kind {
        ExprKind::Column(_) | ExprKind::OuterColumn { .. } | ExprKind::Literal(_) => {}
        ExprKind::Compare { left, right, .. }
        | ExprKind::Arithmetic { left, right, .. }
        | ExprKind::And(left, right)
        | ExprKind::Or(left, right) => {
            collect_invariant_subqueries_from_expr(left, count);
            collect_invariant_subqueries_from_expr(right, count);
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => collect_invariant_subqueries_from_expr(inner, count),
        ExprKind::Coalesce(expressions)
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        }
        | ExprKind::CountDistinctRow { expressions } => {
            for expression in expressions {
                collect_invariant_subqueries_from_expr(expression, count);
            }
        }
        ExprKind::Case {
            branches,
            else_result,
        } => {
            for (condition, result) in branches {
                collect_invariant_subqueries_from_expr(condition, count);
                collect_invariant_subqueries_from_expr(result, count);
            }
            collect_invariant_subqueries_from_expr(else_result, count);
        }
        ExprKind::Aggregate { expression, .. } => {
            if let Some(expression) = expression {
                collect_invariant_subqueries_from_expr(expression, count);
            }
        }
        ExprKind::Exists { query, .. } | ExprKind::ScalarSubquery { query } => {
            collect_subquery_candidate(query, count);
        }
        ExprKind::InSubquery {
            expressions, query, ..
        } => {
            for expression in expressions {
                collect_invariant_subqueries_from_expr(expression, count);
            }
            collect_subquery_candidate(query, count);
        }
        ExprKind::WindowRank {
            partition_by,
            order_by,
            ..
        } => {
            for expression in partition_by {
                collect_invariant_subqueries_from_expr(expression, count);
            }
            for key in order_by {
                collect_invariant_subqueries_from_expr(&key.expression, count);
            }
        }
        ExprKind::WindowAggregate {
            expression,
            partition_by,
            order_by,
            ..
        } => {
            if let Some(expression) = expression {
                collect_invariant_subqueries_from_expr(expression, count);
            }
            for expression in partition_by {
                collect_invariant_subqueries_from_expr(expression, count);
            }
            for key in order_by {
                collect_invariant_subqueries_from_expr(&key.expression, count);
            }
        }
        ExprKind::FirstValue {
            expression,
            partition_by,
            order_by,
        } => {
            collect_invariant_subqueries_from_expr(expression, count);
            for expression in partition_by {
                collect_invariant_subqueries_from_expr(expression, count);
            }
            for key in order_by {
                collect_invariant_subqueries_from_expr(&key.expression, count);
            }
        }
    }
}

fn collect_subquery_candidate(query: &Relation, count: &mut usize) {
    if relation_references_external_outer_column(query, 0) {
        collect_invariant_subqueries(query, count);
    } else {
        *count = count.saturating_add(1);
    }
}

fn relation_references_external_outer_column(relation: &Relation, nested_scopes: usize) -> bool {
    match &relation.node {
        RelationNode::Unit | RelationNode::Scan { .. } => false,
        RelationNode::Product { left, right } => {
            relation_references_external_outer_column(left, nested_scopes)
                || relation_references_external_outer_column(right, nested_scopes)
        }
        RelationNode::Join {
            left, right, on, ..
        } => {
            relation_references_external_outer_column(left, nested_scopes)
                || relation_references_external_outer_column(right, nested_scopes)
                || expression_references_external_outer_column(on, nested_scopes)
        }
        RelationNode::Filter { input, predicate } => {
            relation_references_external_outer_column(input, nested_scopes)
                || expression_references_external_outer_column(predicate, nested_scopes)
        }
        RelationNode::Project { input, expressions } => {
            relation_references_external_outer_column(input, nested_scopes)
                || expressions.iter().any(|expression| {
                    expression_references_external_outer_column(expression, nested_scopes)
                })
        }
        RelationNode::Distinct { input } | RelationNode::Slice { input, .. } => {
            relation_references_external_outer_column(input, nested_scopes)
        }
        RelationNode::SetOperation { left, right, .. } => {
            relation_references_external_outer_column(left, nested_scopes)
                || relation_references_external_outer_column(right, nested_scopes)
        }
        RelationNode::Aggregate {
            input,
            group_by,
            expressions,
            having,
        } => {
            relation_references_external_outer_column(input, nested_scopes)
                || group_by.iter().any(|expression| {
                    expression_references_external_outer_column(expression, nested_scopes)
                })
                || expressions.iter().any(|expression| {
                    expression_references_external_outer_column(expression, nested_scopes)
                })
                || having.as_ref().is_some_and(|expression| {
                    expression_references_external_outer_column(expression, nested_scopes)
                })
        }
        RelationNode::Sort { input, keys } => {
            relation_references_external_outer_column(input, nested_scopes)
                || keys.iter().any(|key| {
                    expression_references_external_outer_column(&key.expression, nested_scopes)
                })
        }
    }
}

fn expression_references_external_outer_column(
    expression: &TypedExpr,
    nested_scopes: usize,
) -> bool {
    match &expression.kind {
        ExprKind::Column(_) | ExprKind::Literal(_) => false,
        ExprKind::OuterColumn { depth, .. } => *depth >= nested_scopes,
        ExprKind::Compare { left, right, .. }
        | ExprKind::Arithmetic { left, right, .. }
        | ExprKind::And(left, right)
        | ExprKind::Or(left, right) => {
            expression_references_external_outer_column(left, nested_scopes)
                || expression_references_external_outer_column(right, nested_scopes)
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => expression_references_external_outer_column(inner, nested_scopes),
        ExprKind::Coalesce(expressions)
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        }
        | ExprKind::CountDistinctRow { expressions } => expressions.iter().any(|expression| {
            expression_references_external_outer_column(expression, nested_scopes)
        }),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            branches.iter().any(|(condition, result)| {
                expression_references_external_outer_column(condition, nested_scopes)
                    || expression_references_external_outer_column(result, nested_scopes)
            }) || expression_references_external_outer_column(else_result, nested_scopes)
        }
        ExprKind::Aggregate { expression, .. } => expression.as_ref().is_some_and(|expression| {
            expression_references_external_outer_column(expression, nested_scopes)
        }),
        ExprKind::Exists { query, .. } | ExprKind::ScalarSubquery { query } => {
            relation_references_external_outer_column(query, nested_scopes.saturating_add(1))
        }
        ExprKind::InSubquery {
            expressions, query, ..
        } => {
            expressions.iter().any(|expression| {
                expression_references_external_outer_column(expression, nested_scopes)
            }) || relation_references_external_outer_column(query, nested_scopes.saturating_add(1))
        }
        ExprKind::WindowRank {
            partition_by,
            order_by,
            ..
        } => {
            partition_by.iter().any(|expression| {
                expression_references_external_outer_column(expression, nested_scopes)
            }) || order_by.iter().any(|key| {
                expression_references_external_outer_column(&key.expression, nested_scopes)
            })
        }
        ExprKind::WindowAggregate {
            expression,
            partition_by,
            order_by,
            ..
        } => {
            expression.as_ref().is_some_and(|expression| {
                expression_references_external_outer_column(expression, nested_scopes)
            }) || partition_by.iter().any(|expression| {
                expression_references_external_outer_column(expression, nested_scopes)
            }) || order_by.iter().any(|key| {
                expression_references_external_outer_column(&key.expression, nested_scopes)
            })
        }
        ExprKind::FirstValue {
            expression,
            partition_by,
            order_by,
        } => {
            expression_references_external_outer_column(expression, nested_scopes)
                || partition_by.iter().any(|expression| {
                    expression_references_external_outer_column(expression, nested_scopes)
                })
                || order_by.iter().any(|key| {
                    expression_references_external_outer_column(&key.expression, nested_scopes)
                })
        }
    }
}

fn encode_relation(
    relation: &Relation,
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicRelation, UnsupportedReason> {
    let rows = match &relation.node {
        RelationNode::Unit => vec![SymbolicRow {
            live: Bool::from_bool(true),
            values: Vec::new(),
        }],
        RelationNode::Scan { table_index } => context
            .database
            .tables
            .get(*table_index)
            .ok_or_else(|| {
                internal(format!(
                    "symbolic database is missing table index {table_index}"
                ))
            })?
            .rows
            .clone(),
        RelationNode::Product { left, right } => {
            let left = encode_relation(left, context)?;
            let right = encode_relation(right, context)?;
            if let Some(metrics) = context.metrics {
                metrics.add(
                    Counter::CartesianProductPairs,
                    left.rows.len().saturating_mul(right.rows.len()),
                );
            }
            symbolic_product(&left.rows, &right.rows)
        }
        RelationNode::Join {
            kind,
            left,
            right,
            on,
        } => symbolic_join(
            &encode_relation(left, context)?.rows,
            &encode_relation(right, context)?.rows,
            &left.columns,
            &right.columns,
            on,
            *kind,
            context,
        )?,
        RelationNode::Filter { input, predicate } => {
            let mut rows = encode_relation(input, context)?.rows;
            for row in &mut rows {
                let predicate = eval_expr(predicate, &row.values, context)?;
                row.live = and_all([row.live.clone(), predicate.is_true()?]);
            }
            rows
        }
        RelationNode::Project { input, expressions } => {
            let input_rows = encode_relation(input, context)?.rows;
            let mut rows = Vec::with_capacity(input_rows.len());
            for (row_index, row) in input_rows.iter().enumerate() {
                let values = expressions
                    .iter()
                    .map(|expression| match &expression.kind {
                        ExprKind::WindowRank {
                            function,
                            partition_by,
                            order_by,
                        } => symbolic_window_rank(
                            &input_rows,
                            row_index,
                            *function,
                            partition_by,
                            order_by,
                            context,
                        ),
                        ExprKind::WindowAggregate {
                            function,
                            expression: argument,
                            distinct,
                            partition_by,
                            order_by,
                        } => symbolic_window_aggregate(
                            &input_rows,
                            row_index,
                            SymbolicWindowAggregate {
                                function: *function,
                                expression: argument.as_deref(),
                                distinct: *distinct,
                                partition_by,
                                order_by,
                                data_type: expression.data_type,
                            },
                            context,
                        ),
                        ExprKind::FirstValue {
                            expression: argument,
                            partition_by,
                            order_by,
                        } => symbolic_first_value(
                            &input_rows,
                            row_index,
                            argument,
                            partition_by,
                            order_by,
                            context,
                        ),
                        _ => eval_expr(expression, &row.values, context),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                rows.push(SymbolicRow {
                    live: row.live.clone(),
                    values,
                });
            }
            rows
        }
        RelationNode::Distinct { input } => {
            symbolic_distinct(encode_relation(input, context)?.rows, context.metrics)?
        }
        RelationNode::SetOperation {
            op,
            all,
            left,
            right,
        } => {
            let left = encode_relation(left, context)?;
            let right = encode_relation(right, context)?;
            symbolic_set_operation(*op, *all, &left.rows, &right.rows, context.metrics)?
        }
        RelationNode::Aggregate {
            input,
            group_by,
            expressions,
            having,
        } => symbolic_aggregate(
            &encode_relation(input, context)?.rows,
            &input.columns,
            group_by,
            expressions,
            having.as_ref(),
            context,
        )?,
        RelationNode::Sort { input, keys } => {
            symbolic_sort(&encode_relation(input, context)?.rows, keys, context)?
        }
        RelationNode::Slice {
            input,
            offset,
            limit,
        } => symbolic_slice(&encode_relation(input, context)?.rows, *offset, *limit)?,
    };
    if let Some(metrics) = context.metrics {
        let counter = match &relation.node {
            RelationNode::Unit => Counter::UnitRows,
            RelationNode::Scan { .. } => Counter::ScanRows,
            RelationNode::Product { .. } => Counter::ProductRows,
            RelationNode::Join { .. } => Counter::JoinRows,
            RelationNode::Filter { .. } => Counter::FilterRows,
            RelationNode::Project { .. } => Counter::ProjectRows,
            RelationNode::Distinct { .. } => Counter::DistinctRows,
            RelationNode::SetOperation { .. } => Counter::SetOperationRows,
            RelationNode::Aggregate { .. } => Counter::AggregateRows,
            RelationNode::Sort { .. } => Counter::SortRows,
            RelationNode::Slice { .. } => Counter::SliceRows,
        };
        metrics.add(counter, rows.len());
        if context.nesting_depth > 0 {
            metrics.add(Counter::NestedRelationRows, rows.len());
        }
    }
    Ok(SymbolicRelation { rows })
}

fn symbolic_product(left: &[SymbolicRow], right: &[SymbolicRow]) -> Vec<SymbolicRow> {
    let mut product = Vec::with_capacity(left.len().saturating_mul(right.len()));
    for prefix in left {
        for suffix in right {
            let mut values = Vec::with_capacity(prefix.values.len() + suffix.values.len());
            values.extend(prefix.values.iter().cloned());
            values.extend(suffix.values.iter().cloned());
            product.push(SymbolicRow {
                live: and_all([prefix.live.clone(), suffix.live.clone()]),
                values,
            });
        }
    }
    product
}

fn symbolic_join(
    left: &[SymbolicRow],
    right: &[SymbolicRow],
    left_columns: &[ColumnMeta],
    right_columns: &[ColumnMeta],
    on: &TypedExpr,
    kind: JoinKind,
    context: &SymbolicEvalContext<'_>,
) -> Result<Vec<SymbolicRow>, UnsupportedReason> {
    let preserve_left = matches!(kind, JoinKind::Left | JoinKind::Full);
    let preserve_right = matches!(kind, JoinKind::Right | JoinKind::Full);
    let product_size = left.len().saturating_mul(right.len());
    if let Some(metrics) = context.metrics {
        metrics.add(Counter::CartesianProductPairs, product_size);
    }

    let output_capacity = product_size
        .saturating_add(if preserve_left { left.len() } else { 0 })
        .saturating_add(if preserve_right { right.len() } else { 0 });
    let mut output = Vec::with_capacity(output_capacity);
    let mut predicates = Vec::with_capacity(if preserve_left || preserve_right {
        product_size
    } else {
        0
    });
    for left_row in left {
        for right_row in right {
            let mut combined = symbolic_concatenate(left_row, right_row);
            if let Some(metrics) = context.metrics {
                metrics.increment(Counter::OnPredicateEvaluations);
            }
            let predicate = eval_expr(on, &combined.values, context)?.is_true()?;
            if preserve_left || preserve_right {
                predicates.push(predicate.clone());
            }
            combined.live = and_all([combined.live, predicate]);
            output.push(combined);
        }
    }

    if preserve_left {
        for (left_index, left_row) in left.iter().enumerate() {
            let matches = right
                .iter()
                .enumerate()
                .map(|(right_index, right_row)| {
                    and_all([
                        right_row.live.clone(),
                        predicates[left_index * right.len() + right_index].clone(),
                    ])
                })
                .collect::<Vec<_>>();
            let mut values = left_row.values.clone();
            values.extend(
                right_columns
                    .iter()
                    .map(|column| symbolic_literal(&Value::Null, column.data_type)),
            );
            output.push(SymbolicRow {
                live: and_all([left_row.live.clone(), or_many(matches).not()]),
                values,
            });
        }
    }
    if preserve_right {
        for (right_index, right_row) in right.iter().enumerate() {
            let matches = left
                .iter()
                .enumerate()
                .map(|(left_index, left_row)| {
                    and_all([
                        left_row.live.clone(),
                        predicates[left_index * right.len() + right_index].clone(),
                    ])
                })
                .collect::<Vec<_>>();
            let mut values = left_columns
                .iter()
                .map(|column| symbolic_literal(&Value::Null, column.data_type))
                .collect::<Vec<_>>();
            values.extend(right_row.values.iter().cloned());
            output.push(SymbolicRow {
                live: and_all([right_row.live.clone(), or_many(matches).not()]),
                values,
            });
        }
    }
    Ok(output)
}

fn symbolic_concatenate(left: &SymbolicRow, right: &SymbolicRow) -> SymbolicRow {
    let mut values = Vec::with_capacity(left.values.len() + right.values.len());
    values.extend(left.values.iter().cloned());
    values.extend(right.values.iter().cloned());
    SymbolicRow {
        live: and_all([left.live.clone(), right.live.clone()]),
        values,
    }
}

fn symbolic_distinct(
    rows: Vec<SymbolicRow>,
    metrics: Option<&MetricsRecorder>,
) -> Result<Vec<SymbolicRow>, UnsupportedReason> {
    let mut output = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().enumerate() {
        let duplicate = rows[..index]
            .iter()
            .map(|previous| {
                Ok(and_all([
                    previous.live.clone(),
                    row_values_equal(previous, row, metrics)?,
                ]))
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        let mut row = row.clone();
        row.live = and_all([row.live, or_many(duplicate).not()]);
        output.push(row);
    }
    Ok(output)
}

fn symbolic_set_operation(
    op: SetOp,
    all: bool,
    left: &[SymbolicRow],
    right: &[SymbolicRow],
    metrics: Option<&MetricsRecorder>,
) -> Result<Vec<SymbolicRow>, UnsupportedReason> {
    if op == SetOp::Union {
        let rows = left.iter().chain(right).cloned().collect::<Vec<_>>();
        return if all {
            Ok(rows)
        } else {
            symbolic_distinct(rows, metrics)
        };
    }

    let zero = Int::from_i64(0);
    let mut output = Vec::with_capacity(left.len());
    for (index, representative) in left.iter().enumerate() {
        let right_count = matching_count(right, representative, metrics)?;
        let live = if all {
            let rank = matching_count(&left[..=index], representative, metrics)?;
            match op {
                SetOp::Intersect => and_all([representative.live.clone(), rank.le(&right_count)]),
                SetOp::Except => and_all([representative.live.clone(), rank.gt(&right_count)]),
                SetOp::Union => unreachable!("UNION returned above"),
            }
        } else {
            let previous = matching_count(&left[..index], representative, metrics)?;
            let first = previous.eq(&zero);
            match op {
                SetOp::Intersect => {
                    and_all([representative.live.clone(), first, right_count.gt(&zero)])
                }
                SetOp::Except => {
                    and_all([representative.live.clone(), first, right_count.eq(&zero)])
                }
                SetOp::Union => unreachable!("UNION returned above"),
            }
        };
        let mut row = representative.clone();
        row.live = live;
        output.push(row);
    }
    Ok(output)
}

#[derive(Clone)]
struct SymbolicGroupMember<'a> {
    row: &'a SymbolicRow,
    member: Bool,
}

fn symbolic_aggregate(
    input: &[SymbolicRow],
    input_columns: &[ColumnMeta],
    group_by: &[TypedExpr],
    expressions: &[TypedExpr],
    having: Option<&TypedExpr>,
    context: &SymbolicEvalContext<'_>,
) -> Result<Vec<SymbolicRow>, UnsupportedReason> {
    if group_by.is_empty() {
        let mut representative = SymbolicRow {
            live: Bool::from_bool(false),
            values: input_columns
                .iter()
                .map(|column| symbolic_literal(&Value::Null, column.data_type))
                .collect(),
        };
        for row in input.iter().rev() {
            representative.values = row
                .values
                .iter()
                .zip(&representative.values)
                .map(|(value, fallback)| {
                    Ok(SymbolicValue {
                        data_type: value.data_type,
                        is_null: row.live.ite(&value.is_null, &fallback.is_null),
                        scalar: scalar_ite(&row.live, &value.scalar, &fallback.scalar)?,
                    })
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?;
            representative.live = or_all([row.live.clone(), representative.live]);
        }
        let members = input
            .iter()
            .map(|row| SymbolicGroupMember {
                row,
                member: row.live.clone(),
            })
            .collect::<Vec<_>>();
        return Ok(vec![build_symbolic_group_row(
            &representative,
            &members,
            Bool::from_bool(true),
            expressions,
            having,
            context,
        )?]);
    }

    let mut output = Vec::with_capacity(input.len());
    for (representative_index, representative) in input.iter().enumerate() {
        let duplicate = input[..representative_index]
            .iter()
            .map(|previous| {
                Ok(and_all([
                    previous.live.clone(),
                    group_keys_equal(previous, representative, group_by, context)?,
                ]))
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        let group_live = and_all([representative.live.clone(), or_many(duplicate).not()]);
        let members = input
            .iter()
            .map(|row| {
                Ok(SymbolicGroupMember {
                    row,
                    member: and_all([
                        row.live.clone(),
                        group_keys_equal(row, representative, group_by, context)?,
                    ]),
                })
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        output.push(build_symbolic_group_row(
            representative,
            &members,
            group_live,
            expressions,
            having,
            context,
        )?);
    }
    Ok(output)
}

fn build_symbolic_group_row(
    representative: &SymbolicRow,
    members: &[SymbolicGroupMember<'_>],
    mut live: Bool,
    expressions: &[TypedExpr],
    having: Option<&TypedExpr>,
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicRow, UnsupportedReason> {
    if let Some(having) = having {
        let predicate = eval_group_expr(having, &representative.values, members, context)?;
        live = and_all([live, predicate.is_true()?]);
    }
    let values = expressions
        .iter()
        .map(|expression| eval_group_expr(expression, &representative.values, members, context))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SymbolicRow { live, values })
}

fn group_keys_equal(
    left: &SymbolicRow,
    right: &SymbolicRow,
    group_by: &[TypedExpr],
    context: &SymbolicEvalContext<'_>,
) -> Result<Bool, UnsupportedReason> {
    if let Some(metrics) = context.metrics {
        metrics.increment(Counter::GroupKeyComparisons);
    }
    let equalities = group_by
        .iter()
        .map(|expression| {
            if let Some(metrics) = context.metrics {
                metrics.increment(Counter::GroupKeyExpressionEvaluations);
            }
            let left = eval_expr(expression, &left.values, context)?;
            if let Some(metrics) = context.metrics {
                metrics.increment(Counter::GroupKeyExpressionEvaluations);
            }
            let right = eval_expr(expression, &right.values, context)?;
            symbolic_value_equal(&left, &right)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(and_many(equalities))
}

fn symbolic_value_equal(
    left: &SymbolicValue,
    right: &SymbolicValue,
) -> Result<Bool, UnsupportedReason> {
    if left.data_type != right.data_type {
        return Err(internal("symbolic equality received different types"));
    }
    Ok(or_all([
        and_all([left.is_null.clone(), right.is_null.clone()]),
        and_all([
            left.is_null.not(),
            right.is_null.not(),
            scalar_equal(&left.scalar, &right.scalar)?,
        ]),
    ]))
}

fn symbolic_window_rank(
    rows: &[SymbolicRow],
    row_index: usize,
    function: WindowRankFunction,
    partition_by: &[TypedExpr],
    order_by: &[SortKey],
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    let row = rows
        .get(row_index)
        .ok_or_else(|| internal("ROW_NUMBER row index is out of bounds"))?;
    let terms = rows
        .iter()
        .enumerate()
        .map(|(other_index, other)| {
            let same_partition = group_keys_equal(other, row, partition_by, context)?;
            let before = sort_keys_before(other, row, order_by, context)?;
            let equal = sort_keys_equal(other, row, order_by, context)?;
            let precedes = match function {
                WindowRankFunction::RowNumber => or_all([
                    before.clone(),
                    and_all([equal, Bool::from_bool(other_index < row_index)]),
                ]),
                WindowRankFunction::Rank | WindowRankFunction::DenseRank => before,
            };
            let canonical = if function == WindowRankFunction::DenseRank {
                let duplicate = rows[..other_index]
                    .iter()
                    .map(|previous| {
                        Ok(and_all([
                            previous.live.clone(),
                            group_keys_equal(previous, other, partition_by, context)?,
                            sort_keys_equal(previous, other, order_by, context)?,
                        ]))
                    })
                    .collect::<Result<Vec<_>, UnsupportedReason>>()?;
                or_many(duplicate).not()
            } else {
                Bool::from_bool(true)
            };
            Ok(
                and_all([other.live.clone(), same_partition, precedes, canonical])
                    .ite(&Int::from_i64(1), &Int::from_i64(0)),
            )
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    Ok(SymbolicValue {
        data_type: DataType::Integer,
        is_null: Bool::from_bool(false),
        scalar: SymbolicScalar::Integer(Int::from_i64(1) + int_sum(terms)),
    })
}

struct SymbolicWindowAggregate<'expression> {
    function: AggregateFunction,
    expression: Option<&'expression TypedExpr>,
    distinct: bool,
    partition_by: &'expression [TypedExpr],
    order_by: &'expression [SortKey],
    data_type: DataType,
}

fn symbolic_window_aggregate(
    rows: &[SymbolicRow],
    row_index: usize,
    window: SymbolicWindowAggregate<'_>,
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    let SymbolicWindowAggregate {
        function,
        expression,
        distinct,
        partition_by,
        order_by,
        data_type,
    } = window;
    let row = rows
        .get(row_index)
        .ok_or_else(|| internal("window aggregate row index is out of bounds"))?;
    let members = rows
        .iter()
        .map(|candidate| {
            let prefix_member = if order_by.is_empty() {
                Bool::from_bool(true)
            } else {
                or_all([
                    sort_keys_before(candidate, row, order_by, context)?,
                    sort_keys_equal(candidate, row, order_by, context)?,
                ])
            };
            Ok(SymbolicGroupMember {
                row: candidate,
                member: and_all([
                    candidate.live.clone(),
                    group_keys_equal(candidate, row, partition_by, context)?,
                    prefix_member,
                ]),
            })
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    symbolic_aggregate_value(function, expression, distinct, &members, data_type, context)
}

fn symbolic_first_value(
    rows: &[SymbolicRow],
    row_index: usize,
    expression: &TypedExpr,
    partition_by: &[TypedExpr],
    order_by: &[SortKey],
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    let row = rows
        .get(row_index)
        .ok_or_else(|| internal("FIRST_VALUE row index is out of bounds"))?;
    let mut result = symbolic_literal(&Value::Null, expression.data_type);
    for (candidate_index, candidate) in rows.iter().enumerate().rev() {
        let predecessors = rows
            .iter()
            .enumerate()
            .map(|(previous_index, previous)| {
                Ok(and_all([
                    previous.live.clone(),
                    group_keys_equal(previous, candidate, partition_by, context)?,
                    or_all([
                        sort_keys_before(previous, candidate, order_by, context)?,
                        and_all([
                            sort_keys_equal(previous, candidate, order_by, context)?,
                            Bool::from_bool(previous_index < candidate_index),
                        ]),
                    ]),
                ]))
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        let selected = and_all([
            candidate.live.clone(),
            group_keys_equal(candidate, row, partition_by, context)?,
            or_many(predecessors).not(),
        ]);
        let value = eval_expr(expression, &candidate.values, context)?;
        result = SymbolicValue {
            data_type: expression.data_type,
            is_null: selected.ite(&value.is_null, &result.is_null),
            scalar: scalar_ite(&selected, &value.scalar, &result.scalar)?,
        };
    }
    Ok(result)
}

fn symbolic_sort(
    rows: &[SymbolicRow],
    keys: &[SortKey],
    context: &SymbolicEvalContext<'_>,
) -> Result<Vec<SymbolicRow>, UnsupportedReason> {
    if rows.is_empty() {
        return Ok(Vec::new());
    }
    let mut ranks = Vec::with_capacity(rows.len());
    for (row_index, row) in rows.iter().enumerate() {
        let terms = rows
            .iter()
            .enumerate()
            .map(|(other_index, other)| {
                let before = sort_keys_before(other, row, keys, context)?;
                let equal = sort_keys_equal(other, row, keys, context)?;
                let precedes = or_all([
                    before,
                    and_all([equal, Bool::from_bool(other_index < row_index)]),
                ]);
                Ok(and_all([other.live.clone(), precedes])
                    .ite(&Int::from_i64(1), &Int::from_i64(0)))
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        ranks.push(int_sum(terms));
    }

    let mut output = Vec::with_capacity(rows.len());
    for rank in 0..rows.len() {
        let rank = Int::from_u64(u64::try_from(rank).unwrap_or(u64::MAX));
        let candidates = rows
            .iter()
            .zip(&ranks)
            .map(|(row, row_rank)| and_all([row.live.clone(), row_rank.eq(&rank)]))
            .collect::<Vec<_>>();
        let values = (0..rows[0].values.len())
            .map(|column| {
                let mut result = symbolic_literal(&Value::Null, rows[0].values[column].data_type);
                for (candidate, row) in candidates.iter().zip(rows).rev() {
                    result = SymbolicValue {
                        data_type: result.data_type,
                        is_null: candidate.ite(&row.values[column].is_null, &result.is_null),
                        scalar: scalar_ite(candidate, &row.values[column].scalar, &result.scalar)?,
                    };
                }
                Ok(result)
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        output.push(SymbolicRow {
            live: or_many(candidates),
            values,
        });
    }
    Ok(output)
}

fn symbolic_slice(
    rows: &[SymbolicRow],
    offset: usize,
    limit: Option<usize>,
) -> Result<Vec<SymbolicRow>, UnsupportedReason> {
    let output_len = limit
        .unwrap_or(rows.len())
        .min(rows.len().saturating_sub(offset));
    let mut output = Vec::with_capacity(output_len);
    for output_index in 0..output_len {
        let desired_rank =
            Int::from_u64(u64::try_from(offset.saturating_add(output_index)).unwrap_or(u64::MAX));
        let candidates = rows
            .iter()
            .enumerate()
            .map(|(index, row)| {
                and_all([
                    row.live.clone(),
                    live_count(&rows[..index]).eq(&desired_rank),
                ])
            })
            .collect::<Vec<_>>();
        let values = if let Some(first) = rows.first() {
            (0..first.values.len())
                .map(|column| {
                    let mut value = symbolic_literal(&Value::Null, first.values[column].data_type);
                    for (candidate, row) in candidates.iter().zip(rows).rev() {
                        value = SymbolicValue {
                            data_type: value.data_type,
                            is_null: candidate.ite(&row.values[column].is_null, &value.is_null),
                            scalar: scalar_ite(
                                candidate,
                                &row.values[column].scalar,
                                &value.scalar,
                            )?,
                        };
                    }
                    Ok(value)
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?
        } else {
            Vec::new()
        };
        output.push(SymbolicRow {
            live: or_many(candidates),
            values,
        });
    }
    Ok(output)
}

fn sort_keys_equal(
    left: &SymbolicRow,
    right: &SymbolicRow,
    keys: &[SortKey],
    context: &SymbolicEvalContext<'_>,
) -> Result<Bool, UnsupportedReason> {
    let equalities = keys
        .iter()
        .map(|key| {
            let left = eval_expr(&key.expression, &left.values, context)?;
            let right = eval_expr(&key.expression, &right.values, context)?;
            symbolic_value_equal(&left, &right)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(and_many(equalities))
}

fn sort_keys_before(
    left: &SymbolicRow,
    right: &SymbolicRow,
    keys: &[SortKey],
    context: &SymbolicEvalContext<'_>,
) -> Result<Bool, UnsupportedReason> {
    let mut before = Bool::from_bool(false);
    let mut prefix_equal = Bool::from_bool(true);
    for key in keys {
        let left = eval_expr(&key.expression, &left.values, context)?;
        let right = eval_expr(&key.expression, &right.values, context)?;
        let value_before = ordered_value_before(&left, &right, key)?;
        before = or_all([before, and_all([prefix_equal.clone(), value_before])]);
        prefix_equal = and_all([prefix_equal, symbolic_value_equal(&left, &right)?]);
    }
    Ok(before)
}

fn ordered_value_before(
    left: &SymbolicValue,
    right: &SymbolicValue,
    key: &SortKey,
) -> Result<Bool, UnsupportedReason> {
    let null_before = if key.nulls_first {
        and_all([left.is_null.clone(), right.is_null.not()])
    } else {
        and_all([left.is_null.not(), right.is_null.clone()])
    };
    let operator = if key.ascending {
        CompareOp::Less
    } else {
        CompareOp::Greater
    };
    Ok(or_all([
        null_before,
        and_all([
            left.is_null.not(),
            right.is_null.not(),
            compare_scalars(operator, &left.scalar, &right.scalar)?,
        ]),
    ]))
}

pub(crate) fn bag_equal(
    left: &SymbolicRelation,
    right: &SymbolicRelation,
    metrics: Option<&MetricsRecorder>,
) -> Result<Bool, UnsupportedReason> {
    let representatives = if left.rows.len() <= right.rows.len() {
        &left.rows
    } else {
        &right.rows
    };
    let mut formulas = Vec::with_capacity(representatives.len() + 1);
    formulas.push(live_count(&left.rows).eq(live_count(&right.rows)));

    // Equal total cardinality plus matching multiplicities for the live values on the side with
    // fewer symbolic rows is sufficient. Any unmatched value on the other side would otherwise
    // have to replace one of those values or increase the total cardinality.
    for representative in representatives {
        let left_count = matching_count(&left.rows, representative, metrics)?;
        let right_count = matching_count(&right.rows, representative, metrics)?;
        formulas.push(representative.live.implies(left_count.eq(right_count)));
    }

    Ok(and_many(formulas))
}

pub(crate) fn list_equal(
    left: &SymbolicRelation,
    right: &SymbolicRelation,
    metrics: Option<&MetricsRecorder>,
) -> Result<Bool, UnsupportedReason> {
    let shared = left.rows.len().min(right.rows.len());
    let mut formulas = Vec::with_capacity(left.rows.len().max(right.rows.len()) * 2);
    for index in 0..shared {
        let left = &left.rows[index];
        let right = &right.rows[index];
        formulas.push(left.live.eq(&right.live));
        formulas.push(
            and_all([left.live.clone(), right.live.clone()])
                .implies(row_values_equal(left, right, metrics)?),
        );
    }
    formulas.extend(left.rows[shared..].iter().map(|row| row.live.not()));
    formulas.extend(right.rows[shared..].iter().map(|row| row.live.not()));
    Ok(and_many(formulas))
}

pub(crate) fn extract_database(
    schema: &Schema,
    database: &SymbolicDatabase,
    model: &Model,
) -> Result<ConcreteDatabase, UnsupportedReason> {
    let mut concrete_tables = Vec::with_capacity(database.tables.len());
    for (table, symbolic_table) in schema.tables.iter().zip(&database.tables) {
        let mut rows = Vec::new();
        for symbolic_row in &symbolic_table.rows {
            if !model_bool(model, &symbolic_row.live)? {
                continue;
            }
            let values = symbolic_row
                .values
                .iter()
                .map(|value| model_value(model, value))
                .collect::<Result<Vec<_>, _>>()?;
            if values.len() != table.columns.len() {
                return Err(internal(format!(
                    "model row for `{}` has the wrong width",
                    table.name
                )));
            }
            rows.push(Row::new(values));
        }
        concrete_tables.push(rows);
    }
    if concrete_tables.len() != schema.tables.len() {
        return Err(internal(
            "model produced a different number of tables than the schema",
        ));
    }
    Ok(ConcreteDatabase {
        tables: concrete_tables,
    })
}

fn eval_expr(
    expression: &TypedExpr,
    row: &[SymbolicValue],
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    eval_expr_context(expression, row, None, context)
}

fn eval_group_expr(
    expression: &TypedExpr,
    row: &[SymbolicValue],
    group: &[SymbolicGroupMember<'_>],
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    eval_expr_context(expression, row, Some(group), context)
}

fn eval_expr_context(
    expression: &TypedExpr,
    row: &[SymbolicValue],
    group: Option<&[SymbolicGroupMember<'_>]>,
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    match &expression.kind {
        ExprKind::Column(index) => row
            .get(*index)
            .cloned()
            .ok_or_else(|| internal(format!("column index {index} is outside the symbolic row"))),
        ExprKind::OuterColumn { depth, index } => context
            .outer_rows
            .len()
            .checked_sub(depth + 1)
            .and_then(|outer_index| context.outer_rows.get(outer_index))
            .and_then(|outer| outer.get(*index))
            .cloned()
            .ok_or_else(|| {
                internal(format!(
                    "outer column depth {depth}, index {index} is outside the symbolic context"
                ))
            }),
        ExprKind::Literal(value) => Ok(symbolic_literal(value, expression.data_type)),
        ExprKind::Compare { op, left, right } => {
            let left = eval_expr_context(left, row, group, context)?;
            let right = eval_expr_context(right, row, group, context)?;
            let value = compare_scalars(*op, &left.scalar, &right.scalar)?;
            Ok(SymbolicValue {
                data_type: DataType::Boolean,
                is_null: or_all([left.is_null, right.is_null]),
                scalar: SymbolicScalar::Boolean(value),
            })
        }
        ExprKind::And(left, right) => {
            let left = eval_expr_context(left, row, group, context)?;
            let right = eval_expr_context(right, row, group, context)?;
            symbolic_and(left, right)
        }
        ExprKind::Or(left, right) => {
            let left = eval_expr_context(left, row, group, context)?;
            let right = eval_expr_context(right, row, group, context)?;
            symbolic_or(left, right)
        }
        ExprKind::Not(inner) => symbolic_not(eval_expr_context(inner, row, group, context)?),
        ExprKind::IsNull(inner) | ExprKind::IsNotNull(inner) => {
            let inner = eval_expr_context(inner, row, group, context)?;
            let value = if matches!(expression.kind, ExprKind::IsNull(_)) {
                inner.is_null
            } else {
                inner.is_null.not()
            };
            Ok(SymbolicValue {
                data_type: DataType::Boolean,
                is_null: Bool::from_bool(false),
                scalar: SymbolicScalar::Boolean(value),
            })
        }
        ExprKind::Coalesce(expressions) => {
            let values = expressions
                .iter()
                .map(|expression| eval_expr_context(expression, row, group, context))
                .collect::<Result<Vec<_>, _>>()?;
            symbolic_coalesce(&values, expression.data_type)
        }
        ExprKind::Arithmetic { op, left, right } => symbolic_arithmetic(
            *op,
            eval_expr_context(left, row, group, context)?,
            eval_expr_context(right, row, group, context)?,
            expression.data_type,
        ),
        ExprKind::Negate(inner) => symbolic_negate(eval_expr_context(inner, row, group, context)?),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            let mut result = eval_expr_context(else_result, row, group, context)?;
            for (condition, branch) in branches.iter().rev() {
                let condition = eval_expr_context(condition, row, group, context)?.is_true()?;
                let branch = eval_expr_context(branch, row, group, context)?;
                result = SymbolicValue {
                    data_type: expression.data_type,
                    is_null: condition.ite(&branch.is_null, &result.is_null),
                    scalar: scalar_ite(&condition, &branch.scalar, &result.scalar)?,
                };
            }
            Ok(result)
        }
        ExprKind::Cast {
            expression: inner,
            to,
        } => symbolic_cast(eval_expr_context(inner, row, group, context)?, *to),
        ExprKind::ScalarFunction {
            function,
            arguments,
        } => {
            let arguments = arguments
                .iter()
                .map(|argument| eval_expr_context(argument, row, group, context))
                .collect::<Result<Vec<_>, _>>()?;
            symbolic_scalar_function(*function, &arguments, expression.data_type)
        }
        ExprKind::Aggregate {
            function,
            expression: argument,
            distinct,
        } => symbolic_aggregate_value(
            *function,
            argument.as_deref(),
            *distinct,
            group.ok_or_else(|| internal("aggregate evaluated outside a group"))?,
            expression.data_type,
            context,
        ),
        ExprKind::CountDistinctRow { expressions } => symbolic_count_distinct_row(
            expressions,
            group.ok_or_else(|| internal("aggregate evaluated outside a group"))?,
            context,
        ),
        ExprKind::Exists { query, negated } => {
            let nested = nested_symbolic_context(context, row);
            let exists = or_many(
                encode_relation(query, &nested)?
                    .rows
                    .into_iter()
                    .map(|row| row.live),
            );
            Ok(SymbolicValue {
                data_type: DataType::Boolean,
                is_null: Bool::from_bool(false),
                scalar: SymbolicScalar::Boolean(if *negated { exists.not() } else { exists }),
            })
        }
        ExprKind::InSubquery {
            expressions,
            query,
            negated,
        } => {
            let values = expressions
                .iter()
                .map(|expression| eval_expr_context(expression, row, group, context))
                .collect::<Result<Vec<_>, _>>()?;
            let nested = nested_symbolic_context(context, row);
            let query = encode_relation(query, &nested)?;
            let mut matches = Vec::with_capacity(query.rows.len());
            let mut unknowns = Vec::with_capacity(query.rows.len());
            for candidate in query.rows {
                if candidate.values.len() != values.len() {
                    return Err(internal("IN subquery returned the wrong column count"));
                }
                let (equal, unknown) = symbolic_row_equal(&values, &candidate.values)?;
                matches.push(and_all([candidate.live.clone(), equal]));
                unknowns.push(and_all([candidate.live, unknown]));
            }
            let matched = or_many(matches);
            let is_null = and_all([matched.not(), or_many(unknowns)]);
            Ok(SymbolicValue {
                data_type: DataType::Boolean,
                is_null,
                scalar: SymbolicScalar::Boolean(if *negated { matched.not() } else { matched }),
            })
        }
        ExprKind::ScalarSubquery { query } => {
            let nested = nested_symbolic_context(context, row);
            let query = encode_relation(query, &nested)?;
            let mut result = symbolic_literal(&Value::Null, expression.data_type);
            for candidate in query.rows.iter().rev() {
                let [candidate_value] = candidate.values.as_slice() else {
                    return Err(internal("scalar subquery returned the wrong column count"));
                };
                result = SymbolicValue {
                    data_type: expression.data_type,
                    is_null: candidate
                        .live
                        .ite(&candidate_value.is_null, &result.is_null),
                    scalar: scalar_ite(&candidate.live, &candidate_value.scalar, &result.scalar)?,
                };
            }
            Ok(result)
        }
        ExprKind::WindowRank { .. }
        | ExprKind::WindowAggregate { .. }
        | ExprKind::FirstValue { .. } => Err(internal(
            "window function was evaluated outside a project relation",
        )),
    }
}

fn symbolic_row_equal(
    left: &[SymbolicValue],
    right: &[SymbolicValue],
) -> Result<(Bool, Bool), UnsupportedReason> {
    if left.len() != right.len() {
        return Err(internal("row comparison received different arities"));
    }
    let mut equalities = Vec::with_capacity(left.len());
    let mut inequalities = Vec::with_capacity(left.len());
    let mut unknowns = Vec::with_capacity(left.len());
    for (left, right) in left.iter().zip(right) {
        let scalar_equal = scalar_equal(&left.scalar, &right.scalar)?;
        let known = and_all([left.is_null.not(), right.is_null.not()]);
        equalities.push(and_all([known.clone(), scalar_equal.clone()]));
        inequalities.push(and_all([known, scalar_equal.not()]));
        unknowns.push(or_all([left.is_null.clone(), right.is_null.clone()]));
    }
    let unequal = or_many(inequalities);
    let equal = and_many(equalities);
    let unknown = and_all([unequal.not(), or_many(unknowns)]);
    Ok((equal, unknown))
}

fn nested_symbolic_context<'database>(
    context: &SymbolicEvalContext<'database>,
    row: &[SymbolicValue],
) -> SymbolicEvalContext<'database> {
    if let Some(metrics) = context.metrics {
        metrics.increment(Counter::NestedSubqueryEncodings);
    }
    let mut nested = context.clone();
    nested.outer_rows.push(row.to_vec());
    nested.nesting_depth += 1;
    nested
}

fn symbolic_coalesce(
    values: &[SymbolicValue],
    data_type: DataType,
) -> Result<SymbolicValue, UnsupportedReason> {
    let Some(last) = values.last() else {
        return Err(internal("COALESCE received no symbolic values"));
    };
    let mut scalar = last.scalar.clone();
    let mut all_null = last.is_null.clone();
    for value in values[..values.len() - 1].iter().rev() {
        scalar = scalar_ite(&value.is_null.not(), &value.scalar, &scalar)?;
        all_null = and_all([value.is_null.clone(), all_null]);
    }
    Ok(SymbolicValue {
        data_type,
        is_null: all_null,
        scalar,
    })
}

fn scalar_ite(
    condition: &Bool,
    then_value: &SymbolicScalar,
    else_value: &SymbolicScalar,
) -> Result<SymbolicScalar, UnsupportedReason> {
    match (then_value, else_value) {
        (SymbolicScalar::Integer(then_value), SymbolicScalar::Integer(else_value)) => Ok(
            SymbolicScalar::Integer(condition.ite(then_value, else_value)),
        ),
        (SymbolicScalar::Boolean(then_value), SymbolicScalar::Boolean(else_value)) => Ok(
            SymbolicScalar::Boolean(condition.ite(then_value, else_value)),
        ),
        (SymbolicScalar::String(then_value), SymbolicScalar::String(else_value)) => Ok(
            SymbolicScalar::String(condition.ite(then_value, else_value)),
        ),
        (SymbolicScalar::Numeric(then_value), SymbolicScalar::Numeric(else_value)) => Ok(
            SymbolicScalar::Numeric(condition.ite(then_value, else_value)),
        ),
        _ => Err(internal("COALESCE received unlike symbolic scalar types")),
    }
}

fn symbolic_arithmetic(
    operator: ArithmeticOp,
    left: SymbolicValue,
    right: SymbolicValue,
    result_type: DataType,
) -> Result<SymbolicValue, UnsupportedReason> {
    let mut is_null = or_all([left.is_null.clone(), right.is_null.clone()]);
    let scalar = match (&left.scalar, &right.scalar) {
        (SymbolicScalar::Integer(left), SymbolicScalar::Integer(right)) => {
            let value = match operator {
                ArithmeticOp::Add => Int::add(&[left.clone(), right.clone()]),
                ArithmeticOp::Subtract => Int::sub(&[left.clone(), right.clone()]),
                ArithmeticOp::Multiply => Int::mul(&[left.clone(), right.clone()]),
                ArithmeticOp::Modulo => {
                    is_null = or_all([is_null, right.eq(Int::from_i64(0))]);
                    left.rem(right)
                }
                ArithmeticOp::Divide => {
                    return Err(internal("integer division was not promoted to numeric"));
                }
            };
            SymbolicScalar::Integer(value)
        }
        (SymbolicScalar::Numeric(left), SymbolicScalar::Numeric(right)) => {
            let value = match operator {
                ArithmeticOp::Add => Real::add(&[left.clone(), right.clone()]),
                ArithmeticOp::Subtract => Real::sub(&[left.clone(), right.clone()]),
                ArithmeticOp::Multiply => Real::mul(&[left.clone(), right.clone()]),
                ArithmeticOp::Divide => {
                    is_null = or_all([is_null, right.eq(Real::from_rational(0, 1))]);
                    left.div(right)
                }
                ArithmeticOp::Modulo => {
                    return Err(internal("numeric modulo passed type checking"));
                }
            };
            SymbolicScalar::Numeric(value)
        }
        _ => {
            return Err(internal("type checking allowed unlike arithmetic operands"));
        }
    };
    if result_type == DataType::Date {
        let SymbolicScalar::Integer(value) = &scalar else {
            return Err(internal(
                "date arithmetic did not produce an integer scalar",
            ));
        };
        is_null = or_all([
            is_null,
            value.lt(Int::from_i64(i64::from(i32::MIN))),
            value.gt(Int::from_i64(i64::from(i32::MAX))),
        ]);
    }
    Ok(SymbolicValue {
        data_type: result_type,
        is_null,
        scalar,
    })
}

fn symbolic_negate(value: SymbolicValue) -> Result<SymbolicValue, UnsupportedReason> {
    let scalar = match value.scalar {
        SymbolicScalar::Integer(value) => SymbolicScalar::Integer(value.unary_minus()),
        SymbolicScalar::Numeric(value) => SymbolicScalar::Numeric(value.unary_minus()),
        _ => return Err(internal("non-numeric symbolic value was negated")),
    };
    Ok(SymbolicValue {
        data_type: value.data_type,
        is_null: value.is_null,
        scalar,
    })
}

fn symbolic_cast(
    value: SymbolicValue,
    target: DataType,
) -> Result<SymbolicValue, UnsupportedReason> {
    if value.data_type == target {
        return Ok(value);
    }
    let scalar = match (value.scalar, target) {
        (SymbolicScalar::Integer(value), DataType::Numeric) => {
            SymbolicScalar::Numeric(Real::from_int(&value))
        }
        (SymbolicScalar::Boolean(value), DataType::Integer) => {
            SymbolicScalar::Integer(value.ite(&Int::from_i64(1), &Int::from_i64(0)))
        }
        (SymbolicScalar::Integer(value), DataType::Boolean) => {
            SymbolicScalar::Boolean(value.eq(Int::from_i64(0)).not())
        }
        (SymbolicScalar::Numeric(value), DataType::Boolean) => {
            SymbolicScalar::Boolean(value.eq(Real::from_rational(0, 1)).not())
        }
        (SymbolicScalar::String(value), DataType::Text | DataType::Enum) => {
            SymbolicScalar::String(value)
        }
        _ => return Err(internal("unsupported symbolic cast passed type checking")),
    };
    Ok(SymbolicValue {
        data_type: target,
        is_null: value.is_null,
        scalar,
    })
}

fn symbolic_scalar_function(
    function: ScalarFunction,
    arguments: &[SymbolicValue],
    data_type: DataType,
) -> Result<SymbolicValue, UnsupportedReason> {
    let is_null = or_many(arguments.iter().map(|argument| argument.is_null.clone()));
    let scalar = match function {
        ScalarFunction::Abs => match arguments {
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(value),
                    ..
                },
            ] => {
                SymbolicScalar::Integer(value.ge(Int::from_i64(0)).ite(value, &value.unary_minus()))
            }
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Numeric(value),
                    ..
                },
            ] => SymbolicScalar::Numeric(
                value
                    .ge(Real::from_rational(0, 1))
                    .ite(value, &value.unary_minus()),
            ),
            _ => return Err(internal("ABS received invalid symbolic arguments")),
        },
        ScalarFunction::Round => match arguments {
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(value),
                    ..
                },
            ]
            | [
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(value),
                    ..
                },
                _,
            ] => SymbolicScalar::Integer(value.clone()),
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Numeric(value),
                    ..
                },
            ] => SymbolicScalar::Numeric(symbolic_round(value, 0)?),
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Numeric(value),
                    ..
                },
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(scale),
                    ..
                },
            ] => {
                let scale = scale
                    .as_i64()
                    .and_then(|scale| i32::try_from(scale).ok())
                    .ok_or_else(|| internal("ROUND scale is not a concrete i32"))?;
                SymbolicScalar::Numeric(symbolic_round(value, scale)?)
            }
            _ => return Err(internal("ROUND received invalid symbolic arguments")),
        },
        ScalarFunction::Truncate => match arguments {
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(value),
                    ..
                },
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(scale),
                    ..
                },
            ] => {
                let scale = scale
                    .as_i64()
                    .and_then(|scale| i32::try_from(scale).ok())
                    .ok_or_else(|| internal("TRUNCATE scale is not a concrete i32"))?;
                if scale >= 0 {
                    SymbolicScalar::Integer(value.clone())
                } else {
                    let factor = 10_i64
                        .checked_pow(scale.unsigned_abs())
                        .ok_or_else(|| internal("TRUNCATE scale is too large"))?;
                    let factor = Int::from_i64(factor);
                    let zero = Int::from_i64(0);
                    let quotient = value.ge(&zero).ite(
                        &value.div(&factor),
                        &value.unary_minus().div(&factor).unary_minus(),
                    );
                    SymbolicScalar::Integer(quotient * factor)
                }
            }
            [
                SymbolicValue {
                    scalar: SymbolicScalar::Numeric(value),
                    ..
                },
                SymbolicValue {
                    scalar: SymbolicScalar::Integer(scale),
                    ..
                },
            ] => {
                let scale = scale
                    .as_i64()
                    .and_then(|scale| i32::try_from(scale).ok())
                    .ok_or_else(|| internal("TRUNCATE scale is not a concrete i32"))?;
                SymbolicScalar::Numeric(symbolic_truncate(value, scale)?)
            }
            _ => return Err(internal("TRUNCATE received invalid symbolic arguments")),
        },
        ScalarFunction::Concat => {
            let strings = arguments
                .iter()
                .map(|argument| {
                    let SymbolicScalar::String(value) = &argument.scalar else {
                        return Err(internal("CONCAT received a non-string symbolic value"));
                    };
                    Ok(value.clone())
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?;
            SymbolicScalar::String(Z3String::concat(&strings))
        }
        ScalarFunction::Length => {
            let [argument] = arguments else {
                return Err(internal("LENGTH received invalid symbolic arguments"));
            };
            let SymbolicScalar::String(value) = &argument.scalar else {
                return Err(internal("LENGTH received a non-string symbolic value"));
            };
            SymbolicScalar::Integer(value.length())
        }
        ScalarFunction::DateDiff => {
            let [left, right] = arguments else {
                return Err(internal("DATEDIFF received invalid symbolic arguments"));
            };
            let (SymbolicScalar::Integer(left), SymbolicScalar::Integer(right)) =
                (&left.scalar, &right.scalar)
            else {
                return Err(internal("DATEDIFF received non-date symbolic values"));
            };
            SymbolicScalar::Integer(Int::sub(&[left.clone(), right.clone()]))
        }
        ScalarFunction::Year | ScalarFunction::Month | ScalarFunction::Day => {
            let [argument] = arguments else {
                return Err(internal(
                    "date-part function received invalid symbolic arguments",
                ));
            };
            let SymbolicScalar::Integer(value) = &argument.scalar else {
                return Err(internal(
                    "date-part function received a non-date symbolic value",
                ));
            };
            let (year, month, day) = symbolic_date_components(value);
            SymbolicScalar::Integer(match function {
                ScalarFunction::Year => year,
                ScalarFunction::Month => month,
                ScalarFunction::Day => day,
                _ => unreachable!(),
            })
        }
        ScalarFunction::ToDays => {
            let [argument] = arguments else {
                return Err(internal("TO_DAYS received invalid symbolic arguments"));
            };
            let SymbolicScalar::Integer(value) = &argument.scalar else {
                return Err(internal("TO_DAYS received a non-date symbolic value"));
            };
            SymbolicScalar::Integer(value + Int::from_i64(719_528))
        }
        ScalarFunction::LastDay
        | ScalarFunction::Weekday
        | ScalarFunction::DayOfWeek
        | ScalarFunction::Quarter => {
            let [argument] = arguments else {
                return Err(internal(
                    "date function received invalid symbolic arguments",
                ));
            };
            let SymbolicScalar::Integer(value) = &argument.scalar else {
                return Err(internal("date function received a non-date symbolic value"));
            };
            let scalar = match function {
                ScalarFunction::LastDay => {
                    let (year, month, day) = symbolic_date_components(value);
                    value + symbolic_days_in_month(&year, &month) - day
                }
                ScalarFunction::Weekday => (value + Int::from_i64(3)).rem(Int::from_i64(7)),
                ScalarFunction::DayOfWeek => {
                    (value + Int::from_i64(4)).rem(Int::from_i64(7)) + Int::from_i64(1)
                }
                ScalarFunction::Quarter => {
                    let (_, month, _) = symbolic_date_components(value);
                    (month - Int::from_i64(1)).div(Int::from_i64(3)) + Int::from_i64(1)
                }
                _ => unreachable!(),
            };
            SymbolicScalar::Integer(scalar)
        }
        ScalarFunction::Sign => {
            let [argument] = arguments else {
                return Err(internal("SIGN received invalid symbolic arguments"));
            };
            let zero = Int::from_i64(0);
            let one = Int::from_i64(1);
            let negative_one = Int::from_i64(-1);
            let sign = match &argument.scalar {
                SymbolicScalar::Integer(value) => value
                    .gt(Int::from_i64(0))
                    .ite(&one, &value.lt(Int::from_i64(0)).ite(&negative_one, &zero)),
                SymbolicScalar::Numeric(value) => value.gt(Real::from_rational(0, 1)).ite(
                    &one,
                    &value
                        .lt(Real::from_rational(0, 1))
                        .ite(&negative_one, &zero),
                ),
                _ => return Err(internal("SIGN received a non-numeric symbolic value")),
            };
            SymbolicScalar::Integer(sign)
        }
        ScalarFunction::Power(exponent) => {
            let [
                SymbolicValue {
                    scalar: SymbolicScalar::Numeric(value),
                    ..
                },
            ] = arguments
            else {
                return Err(internal("POWER received invalid symbolic arguments"));
            };
            let mut result = Real::from_rational(1, 1);
            for _ in 0..exponent {
                result *= value;
            }
            SymbolicScalar::Numeric(result)
        }
        ScalarFunction::Floor | ScalarFunction::Ceil => {
            let [
                SymbolicValue {
                    scalar: SymbolicScalar::Numeric(value),
                    ..
                },
            ] = arguments
            else {
                return Err(internal(
                    "FLOOR or CEIL received invalid symbolic arguments",
                ));
            };
            SymbolicScalar::Integer(if function == ScalarFunction::Floor {
                Int::from_real(value)
            } else {
                Int::from_real(&value.unary_minus()).unary_minus()
            })
        }
        ScalarFunction::StartsWith | ScalarFunction::EndsWith | ScalarFunction::Contains => {
            let [value, pattern] = arguments else {
                return Err(internal("LIKE received invalid symbolic arguments"));
            };
            let (SymbolicScalar::String(value), SymbolicScalar::String(pattern)) =
                (&value.scalar, &pattern.scalar)
            else {
                return Err(internal("LIKE received non-string symbolic arguments"));
            };
            SymbolicScalar::Boolean(match function {
                ScalarFunction::StartsWith => pattern.prefix(value),
                ScalarFunction::EndsWith => pattern.suffix(value),
                ScalarFunction::Contains => value.contains(pattern),
                _ => unreachable!(),
            })
        }
        ScalarFunction::Substring { start, length } => {
            let [
                SymbolicValue {
                    scalar: SymbolicScalar::String(value),
                    ..
                },
            ] = arguments
            else {
                return Err(internal("SUBSTRING received invalid symbolic arguments"));
            };
            let start =
                i64::try_from(start).map_err(|_| internal("SUBSTRING start is outside i64"))?;
            let length = match length {
                Some(length) => Int::from_i64(
                    i64::try_from(length)
                        .map_err(|_| internal("SUBSTRING length is outside i64"))?,
                ),
                None => value.length(),
            };
            SymbolicScalar::String(value.substr(Int::from_i64(start), length))
        }
        ScalarFunction::Left(length) | ScalarFunction::Right(length) => {
            let [
                SymbolicValue {
                    scalar: SymbolicScalar::String(value),
                    ..
                },
            ] = arguments
            else {
                return Err(internal(
                    "LEFT or RIGHT received invalid symbolic arguments",
                ));
            };
            let length = Int::from_i64(
                i64::try_from(length)
                    .map_err(|_| internal("LEFT or RIGHT length is outside i64"))?,
            );
            let value_length = value.length();
            let offset = value_length
                .ge(&length)
                .ite(&(&value_length - &length), &Int::from_i64(0));
            SymbolicScalar::String(if matches!(function, ScalarFunction::Left(_)) {
                value.substr(Int::from_i64(0), length)
            } else {
                value.substr(offset, length)
            })
        }
    };
    Ok(SymbolicValue {
        data_type,
        is_null,
        scalar,
    })
}

fn symbolic_date_components(days_since_epoch: &Int) -> (Int, Int, Int) {
    let days = days_since_epoch + Int::from_i64(719_468);
    let era = days.div(Int::from_i64(146_097));
    let day_of_era = &days - &era * Int::from_i64(146_097);
    let year_of_era = (&day_of_era - day_of_era.div(Int::from_i64(1_460))
        + day_of_era.div(Int::from_i64(36_524))
        - day_of_era.div(Int::from_i64(146_096)))
    .div(Int::from_i64(365));
    let mut year = &year_of_era + &era * Int::from_i64(400);
    let day_of_year = &day_of_era
        - (Int::from_i64(365) * &year_of_era + year_of_era.div(Int::from_i64(4))
            - year_of_era.div(Int::from_i64(100)));
    let month_prime = (Int::from_i64(5) * &day_of_year + Int::from_i64(2)).div(Int::from_i64(153));
    let day = &day_of_year
        - (Int::from_i64(153) * &month_prime + Int::from_i64(2)).div(Int::from_i64(5))
        + Int::from_i64(1);
    let month = month_prime.lt(Int::from_i64(10)).ite(
        &(&month_prime + Int::from_i64(3)),
        &(&month_prime - Int::from_i64(9)),
    );
    year += month
        .le(Int::from_i64(2))
        .ite(&Int::from_i64(1), &Int::from_i64(0));
    (year, month, day)
}

fn symbolic_days_in_month(year: &Int, month: &Int) -> Int {
    let leap_year = and_all([
        year.rem(Int::from_i64(4)).eq(Int::from_i64(0)),
        or_all([
            year.rem(Int::from_i64(100)).eq(Int::from_i64(0)).not(),
            year.rem(Int::from_i64(400)).eq(Int::from_i64(0)),
        ]),
    ]);
    let february_days = leap_year.ite(&Int::from_i64(29), &Int::from_i64(28));
    let thirty_days = or_all([4, 6, 9, 11].map(|value| month.eq(Int::from_i64(value))));
    month.eq(Int::from_i64(2)).ite(
        &february_days,
        &thirty_days.ite(&Int::from_i64(30), &Int::from_i64(31)),
    )
}

fn symbolic_round(value: &Real, scale: i32) -> Result<Real, UnsupportedReason> {
    let factor = 10_i64
        .checked_pow(scale.unsigned_abs())
        .ok_or_else(|| internal("ROUND scale is too large"))?;
    let factor = Real::from_rational(factor, 1);
    let scaled = if scale >= 0 {
        value * &factor
    } else {
        value.div(&factor)
    };
    let half = Real::from_rational(1, 2);
    let positive = scaled.ge(Real::from_rational(0, 1));
    let positive_rounded = Int::from_real(&(scaled.clone() + &half));
    let negative_rounded = Int::from_real(&(scaled.unary_minus() + half)).unary_minus();
    let rounded = Real::from_int(&positive.ite(&positive_rounded, &negative_rounded));
    Ok(if scale >= 0 {
        rounded.div(factor)
    } else {
        rounded * factor
    })
}

fn symbolic_truncate(value: &Real, scale: i32) -> Result<Real, UnsupportedReason> {
    let factor = 10_i64
        .checked_pow(scale.unsigned_abs())
        .ok_or_else(|| internal("TRUNCATE scale is too large"))?;
    let factor = Real::from_rational(factor, 1);
    let scaled = if scale >= 0 {
        value * &factor
    } else {
        value.div(&factor)
    };
    let zero = Real::from_rational(0, 1);
    let truncated = scaled.ge(&zero).ite(
        &Int::from_real(&scaled),
        &Int::from_real(&scaled.unary_minus()).unary_minus(),
    );
    let truncated = Real::from_int(&truncated);
    Ok(if scale >= 0 {
        truncated.div(factor)
    } else {
        truncated * factor
    })
}

fn symbolic_count_distinct_row(
    expressions: &[TypedExpr],
    group: &[SymbolicGroupMember<'_>],
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    let values = group
        .iter()
        .map(|member| {
            Ok((
                expressions
                    .iter()
                    .map(|expression| eval_expr(expression, &member.row.values, context))
                    .collect::<Result<Vec<_>, _>>()?,
                member.member.clone(),
            ))
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    let mut valid: Vec<Bool> = Vec::with_capacity(values.len());
    for (index, (value, membership)) in values.iter().enumerate() {
        let mut live = and_all([
            membership.clone(),
            and_many(value.iter().map(|value| value.is_null.not())),
        ]);
        let duplicate = values[..index]
            .iter()
            .zip(&valid)
            .map(|((previous, _), previous_valid)| {
                let (equal, _) = symbolic_row_equal(previous, value)?;
                Ok(and_all([previous_valid.clone(), equal]))
            })
            .collect::<Result<Vec<_>, UnsupportedReason>>()?;
        live = and_all([live, or_many(duplicate).not()]);
        valid.push(live);
    }
    Ok(SymbolicValue {
        data_type: DataType::Integer,
        is_null: Bool::from_bool(false),
        scalar: SymbolicScalar::Integer(int_sum(
            valid
                .iter()
                .map(|valid| valid.ite(&Int::from_i64(1), &Int::from_i64(0)))
                .collect(),
        )),
    })
}

fn symbolic_aggregate_value(
    function: AggregateFunction,
    expression: Option<&TypedExpr>,
    distinct: bool,
    group: &[SymbolicGroupMember<'_>],
    data_type: DataType,
    context: &SymbolicEvalContext<'_>,
) -> Result<SymbolicValue, UnsupportedReason> {
    if function == AggregateFunction::Count && expression.is_none() {
        let count = int_sum(
            group
                .iter()
                .map(|member| member.member.ite(&Int::from_i64(1), &Int::from_i64(0)))
                .collect(),
        );
        return Ok(SymbolicValue {
            data_type: DataType::Integer,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Integer(count),
        });
    }
    let expression = expression.ok_or_else(|| internal("aggregate argument is missing"))?;
    let values = group
        .iter()
        .map(|member| {
            Ok((
                eval_expr(expression, &member.row.values, context)?,
                member.member.clone(),
            ))
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    let mut valid: Vec<Bool> = Vec::with_capacity(values.len());
    for (index, (value, membership)) in values.iter().enumerate() {
        let mut live = and_all([membership.clone(), value.is_null.not()]);
        if distinct {
            let duplicate = values[..index]
                .iter()
                .zip(&valid)
                .map(|((previous, _), previous_valid)| {
                    Ok(and_all([
                        previous_valid.clone(),
                        scalar_equal(&previous.scalar, &value.scalar)?,
                    ]))
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?;
            live = and_all([live, or_many(duplicate).not()]);
        }
        valid.push(live);
    }
    let count = int_sum(
        valid
            .iter()
            .map(|valid| valid.ite(&Int::from_i64(1), &Int::from_i64(0)))
            .collect(),
    );
    if function == AggregateFunction::Count {
        return Ok(SymbolicValue {
            data_type: DataType::Integer,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Integer(count),
        });
    }
    if function == AggregateFunction::Sum || function == AggregateFunction::Avg {
        return symbolic_sum_or_avg(function, &values, &valid, count, data_type);
    }
    symbolic_min_or_max(function, &values, &valid, data_type)
}

fn symbolic_sum_or_avg(
    function: AggregateFunction,
    values: &[(SymbolicValue, Bool)],
    valid: &[Bool],
    count: Int,
    data_type: DataType,
) -> Result<SymbolicValue, UnsupportedReason> {
    let is_null = count.eq(Int::from_i64(0));
    let scalar = match data_type {
        DataType::Integer => {
            let terms = values
                .iter()
                .zip(valid)
                .map(|((value, _), valid)| match &value.scalar {
                    SymbolicScalar::Integer(value) => Ok(valid.ite(value, &Int::from_i64(0))),
                    SymbolicScalar::Boolean(value) => Ok(valid.ite(
                        &value.ite(&Int::from_i64(1), &Int::from_i64(0)),
                        &Int::from_i64(0),
                    )),
                    _ => Err(internal("SUM received a non-numeric symbolic value")),
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?;
            SymbolicScalar::Integer(int_sum(terms))
        }
        DataType::Numeric => {
            let terms = values
                .iter()
                .zip(valid)
                .map(|((value, _), valid)| {
                    let numeric = match &value.scalar {
                        SymbolicScalar::Numeric(value) => value.clone(),
                        SymbolicScalar::Integer(value) => Real::from_int(value),
                        SymbolicScalar::Boolean(value) => {
                            Real::from_int(&value.ite(&Int::from_i64(1), &Int::from_i64(0)))
                        }
                        _ => {
                            return Err(internal("AVG received a non-numeric symbolic value"));
                        }
                    };
                    Ok(valid.ite(&numeric, &Real::from_rational(0, 1)))
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?;
            let sum = real_sum(terms);
            let value = if function == AggregateFunction::Avg {
                sum.div(Real::from_int(&count))
            } else {
                sum
            };
            SymbolicScalar::Numeric(value)
        }
        _ => return Err(internal("SUM/AVG has a non-numeric output type")),
    };
    Ok(SymbolicValue {
        data_type,
        is_null,
        scalar,
    })
}

fn symbolic_min_or_max(
    function: AggregateFunction,
    values: &[(SymbolicValue, Bool)],
    valid: &[Bool],
    data_type: DataType,
) -> Result<SymbolicValue, UnsupportedReason> {
    let mut found = Bool::from_bool(false);
    let mut scalar = symbolic_literal(&Value::Null, data_type).scalar;
    for ((value, _), valid) in values.iter().zip(valid) {
        let operator = if function == AggregateFunction::Min {
            CompareOp::Less
        } else {
            CompareOp::Greater
        };
        let better = or_all([
            found.not(),
            compare_scalars(operator, &value.scalar, &scalar)?,
        ]);
        let select = and_all([valid.clone(), better]);
        scalar = scalar_ite(&select, &value.scalar, &scalar)?;
        found = or_all([found, valid.clone()]);
    }
    Ok(SymbolicValue {
        data_type,
        is_null: found.not(),
        scalar,
    })
}

fn real_sum(values: Vec<Real>) -> Real {
    match values.as_slice() {
        [] => Real::from_rational(0, 1),
        [value] => value.clone(),
        _ => Real::add(&values),
    }
}

fn symbolic_boolean(value: bool) -> SymbolicValue {
    SymbolicValue {
        data_type: DataType::Boolean,
        is_null: Bool::from_bool(false),
        scalar: SymbolicScalar::Boolean(Bool::from_bool(value)),
    }
}

fn symbolic_and(
    left: SymbolicValue,
    right: SymbolicValue,
) -> Result<SymbolicValue, UnsupportedReason> {
    let left_true = left.is_true()?;
    let right_true = right.is_true()?;
    let left_false = left.is_false()?;
    let right_false = right.is_false()?;
    let is_true = and_all([left_true, right_true]);
    let is_false = or_all([left_false, right_false]);
    Ok(SymbolicValue {
        data_type: DataType::Boolean,
        is_null: or_all([is_true.clone(), is_false]).not(),
        scalar: SymbolicScalar::Boolean(is_true),
    })
}

fn symbolic_or(
    left: SymbolicValue,
    right: SymbolicValue,
) -> Result<SymbolicValue, UnsupportedReason> {
    let left_true = left.is_true()?;
    let right_true = right.is_true()?;
    let left_false = left.is_false()?;
    let right_false = right.is_false()?;
    let is_true = or_all([left_true, right_true]);
    let is_false = and_all([left_false, right_false]);
    Ok(SymbolicValue {
        data_type: DataType::Boolean,
        is_null: or_all([is_true.clone(), is_false]).not(),
        scalar: SymbolicScalar::Boolean(is_true),
    })
}

fn symbolic_not(value: SymbolicValue) -> Result<SymbolicValue, UnsupportedReason> {
    let SymbolicScalar::Boolean(scalar) = value.scalar else {
        return Err(internal("NOT received a non-boolean symbolic value"));
    };
    Ok(SymbolicValue {
        data_type: DataType::Boolean,
        is_null: value.is_null,
        scalar: SymbolicScalar::Boolean(scalar.not()),
    })
}

fn symbolic_literal(value: &Value, data_type: DataType) -> SymbolicValue {
    match value {
        Value::Integer(value) => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Integer(Int::from_i64(*value)),
        },
        Value::Boolean(value) => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Boolean(Bool::from_bool(*value)),
        },
        Value::Text(value) | Value::Enum(value) => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::String(Z3String::from(value.as_str())),
        },
        Value::Date(value) => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Integer(Int::from_i64(i64::from(value.days_since_epoch()))),
        },
        Value::Time(value) => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Integer(Int::from_i64(value.nanoseconds_since_midnight())),
        },
        Value::Numeric(value) => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(false),
            scalar: SymbolicScalar::Numeric(Real::from_rational(
                value.numerator(),
                value.denominator(),
            )),
        },
        Value::Null => SymbolicValue {
            data_type,
            is_null: Bool::from_bool(true),
            scalar: match data_type {
                DataType::Integer | DataType::Date | DataType::Time => {
                    SymbolicScalar::Integer(Int::from_i64(0))
                }
                DataType::Boolean => SymbolicScalar::Boolean(Bool::from_bool(false)),
                DataType::Text | DataType::Enum => SymbolicScalar::String(Z3String::from("")),
                DataType::Numeric => SymbolicScalar::Numeric(Real::from_rational(0, 1)),
            },
        },
    }
}

impl SymbolicValue {
    fn is_true(&self) -> Result<Bool, UnsupportedReason> {
        let SymbolicScalar::Boolean(value) = &self.scalar else {
            return Err(internal("a non-boolean value was used as a predicate"));
        };
        Ok(and_all([self.is_null.not(), value.clone()]))
    }

    fn is_false(&self) -> Result<Bool, UnsupportedReason> {
        let SymbolicScalar::Boolean(value) = &self.scalar else {
            return Err(internal("a non-boolean value was used as a predicate"));
        };
        Ok(and_all([self.is_null.not(), value.not()]))
    }
}

fn compare_scalars(
    operator: CompareOp,
    left: &SymbolicScalar,
    right: &SymbolicScalar,
) -> Result<Bool, UnsupportedReason> {
    match (left, right) {
        (SymbolicScalar::Integer(left), SymbolicScalar::Integer(right)) => Ok(match operator {
            CompareOp::Equal => left.eq(right),
            CompareOp::NotEqual => left.eq(right).not(),
            CompareOp::Less => left.lt(right),
            CompareOp::LessOrEqual => left.le(right),
            CompareOp::Greater => left.gt(right),
            CompareOp::GreaterOrEqual => left.ge(right),
        }),
        (SymbolicScalar::Boolean(left), SymbolicScalar::Boolean(right)) => Ok(match operator {
            CompareOp::Equal => left.eq(right),
            CompareOp::NotEqual => left.eq(right).not(),
            CompareOp::Less => and_all([left.not(), right.clone()]),
            CompareOp::LessOrEqual => or_all([left.not(), right.clone()]),
            CompareOp::Greater => and_all([left.clone(), right.not()]),
            CompareOp::GreaterOrEqual => or_all([left.clone(), right.not()]),
        }),
        (SymbolicScalar::String(left), SymbolicScalar::String(right)) => Ok(match operator {
            CompareOp::Equal => left.eq(right),
            CompareOp::NotEqual => left.eq(right).not(),
            CompareOp::Less => right.str_gt(left),
            CompareOp::LessOrEqual => right.str_ge(left),
            CompareOp::Greater => left.str_gt(right),
            CompareOp::GreaterOrEqual => left.str_ge(right),
        }),
        (SymbolicScalar::Numeric(left), SymbolicScalar::Numeric(right)) => Ok(match operator {
            CompareOp::Equal => left.eq(right),
            CompareOp::NotEqual => left.eq(right).not(),
            CompareOp::Less => left.lt(right),
            CompareOp::LessOrEqual => left.le(right),
            CompareOp::Greater => left.gt(right),
            CompareOp::GreaterOrEqual => left.ge(right),
        }),
        _ => Err(internal(
            "type checking allowed unlike symbolic comparison operands",
        )),
    }
}

fn row_values_equal(
    left: &SymbolicRow,
    right: &SymbolicRow,
    metrics: Option<&MetricsRecorder>,
) -> Result<Bool, UnsupportedReason> {
    if let Some(metrics) = metrics {
        metrics.increment(Counter::RowValueComparisons);
    }
    if left.values.len() != right.values.len() {
        return Err(internal(
            "bag comparison received rows with different widths",
        ));
    }
    let equalities = left
        .values
        .iter()
        .zip(&right.values)
        .map(|(left, right)| {
            if left.data_type != right.data_type {
                return Err(internal(
                    "bag comparison received values with different types",
                ));
            }
            let both_null = and_all([left.is_null.clone(), right.is_null.clone()]);
            let both_values = and_all([
                left.is_null.not(),
                right.is_null.not(),
                scalar_equal(&left.scalar, &right.scalar)?,
            ]);
            Ok(or_all([both_null, both_values]))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(and_many(equalities))
}

fn scalar_equal(left: &SymbolicScalar, right: &SymbolicScalar) -> Result<Bool, UnsupportedReason> {
    match (left, right) {
        (SymbolicScalar::Integer(left), SymbolicScalar::Integer(right)) => Ok(left.eq(right)),
        (SymbolicScalar::Boolean(left), SymbolicScalar::Boolean(right)) => Ok(left.eq(right)),
        (SymbolicScalar::String(left), SymbolicScalar::String(right)) => Ok(left.eq(right)),
        (SymbolicScalar::Numeric(left), SymbolicScalar::Numeric(right)) => Ok(left.eq(right)),
        _ => Err(internal(
            "symbolic scalar equality received different types",
        )),
    }
}

fn live_count(rows: &[SymbolicRow]) -> Int {
    let zero = Int::from_i64(0);
    let one = Int::from_i64(1);
    let terms = rows
        .iter()
        .map(|row| row.live.ite(&one, &zero))
        .collect::<Vec<_>>();
    int_sum(terms)
}

fn matching_count(
    rows: &[SymbolicRow],
    representative: &SymbolicRow,
    metrics: Option<&MetricsRecorder>,
) -> Result<Int, UnsupportedReason> {
    if let Some(metrics) = metrics {
        metrics.increment(Counter::MatchingCountFormulas);
        metrics.add(Counter::MatchingCountTerms, rows.len());
    }
    let zero = Int::from_i64(0);
    let one = Int::from_i64(1);
    let terms = rows
        .iter()
        .map(|row| {
            row_values_equal(row, representative, metrics)
                .map(|equal| and_all([row.live.clone(), equal]).ite(&one, &zero))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(int_sum(terms))
}

fn int_sum(values: Vec<Int>) -> Int {
    match values.as_slice() {
        [] => Int::from_i64(0),
        [value] => value.clone(),
        _ => Int::add(&values),
    }
}

fn and_all<const N: usize>(values: [Bool; N]) -> Bool {
    match values.as_slice() {
        [] => Bool::from_bool(true),
        [value] => value.clone(),
        _ => Bool::and(&values),
    }
}

fn and_many<I>(values: I) -> Bool
where
    I: IntoIterator<Item = Bool>,
{
    let values = values.into_iter().collect::<Vec<_>>();
    match values.as_slice() {
        [] => Bool::from_bool(true),
        [value] => value.clone(),
        _ => Bool::and(&values),
    }
}

fn or_all<const N: usize>(values: [Bool; N]) -> Bool {
    match values.as_slice() {
        [] => Bool::from_bool(false),
        [value] => value.clone(),
        _ => Bool::or(&values),
    }
}

fn or_many<I>(values: I) -> Bool
where
    I: IntoIterator<Item = Bool>,
{
    let values = values.into_iter().collect::<Vec<_>>();
    match values.as_slice() {
        [] => Bool::from_bool(false),
        [value] => value.clone(),
        _ => Bool::or(&values),
    }
}

fn model_value(model: &Model, value: &SymbolicValue) -> Result<Value, UnsupportedReason> {
    if model_bool(model, &value.is_null)? {
        return Ok(Value::Null);
    }
    match (value.data_type, &value.scalar) {
        (DataType::Integer, SymbolicScalar::Integer(value)) => model
            .eval(value, true)
            .and_then(|value| value.as_i64())
            .map(Value::Integer)
            .ok_or_else(|| internal("Z3 returned an integer outside the supported 64-bit range")),
        (DataType::Boolean, SymbolicScalar::Boolean(value)) => {
            model_bool(model, value).map(Value::Boolean)
        }
        (DataType::Text, SymbolicScalar::String(value)) => model
            .eval(value, true)
            .and_then(|value| value.as_string())
            .map(Value::Text)
            .ok_or_else(|| internal("Z3 did not provide a concrete text value")),
        (DataType::Enum, SymbolicScalar::String(value)) => model
            .eval(value, true)
            .and_then(|value| value.as_string())
            .map(Value::Enum)
            .ok_or_else(|| internal("Z3 did not provide a concrete enum value")),
        (DataType::Date, SymbolicScalar::Integer(value)) => {
            let days = model
                .eval(value, true)
                .and_then(|value| value.as_i64())
                .and_then(|value| i32::try_from(value).ok())
                .ok_or_else(|| internal("Z3 returned a date outside the supported range"))?;
            Ok(Value::Date(DateValue::from_days_since_epoch(days)))
        }
        (DataType::Time, SymbolicScalar::Integer(value)) => {
            let nanoseconds = model
                .eval(value, true)
                .and_then(|value| value.as_i64())
                .ok_or_else(|| internal("Z3 returned a time outside the supported range"))?;
            TimeValue::from_nanoseconds_since_midnight(nanoseconds)
                .map(Value::Time)
                .map_err(|error| internal(format!("invalid Z3 time value: {error}")))
        }
        (DataType::Numeric, SymbolicScalar::Numeric(value)) => {
            let (numerator, denominator) = model
                .eval(value, true)
                .and_then(|value| value.as_rational())
                .ok_or_else(|| internal("Z3 returned a numeric value outside the exact range"))?;
            ExactNumeric::new(numerator, denominator)
                .map(Value::Numeric)
                .map_err(|error| internal(format!("invalid Z3 numeric value: {error}")))
        }
        _ => Err(internal(
            "symbolic value data type does not match its scalar representation",
        )),
    }
}

fn model_bool(model: &Model, value: &Bool) -> Result<bool, UnsupportedReason> {
    model
        .eval(value, true)
        .and_then(|value| value.as_bool())
        .ok_or_else(|| internal("Z3 did not provide a concrete boolean value"))
}

fn internal(message: impl Into<String>) -> UnsupportedReason {
    UnsupportedReason::new(UnsupportedKind::Internal, message)
}
