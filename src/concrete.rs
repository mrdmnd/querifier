use std::collections::{BTreeMap, BTreeSet};

use crate::counterexample::{DateValue, ExactNumeric, QueryResult, Row, Value};
use crate::ir::{
    AggregateFunction, ArithmeticOp, CompareOp, ExprKind, JoinKind, Relation, RelationNode,
    ScalarFunction, SetOp, SortKey, TypedExpr, TypedQuery, WindowRankFunction,
};
use crate::outcome::{UnsupportedKind, UnsupportedReason};
use crate::schema::{
    ColumnRef, ConstraintComparison, ConstraintOperand, ConstraintPredicate, DataType,
    IntegrityConstraint, Schema, canonical_name,
};

#[derive(Clone, Debug)]
pub(crate) struct ConcreteDatabase {
    pub tables: Vec<Vec<Row>>,
}

#[derive(Clone)]
struct EvalContext<'database> {
    database: &'database ConcreteDatabase,
    outer_rows: Vec<Vec<Value>>,
}

pub(crate) fn evaluate(
    query: &TypedQuery,
    database: &ConcreteDatabase,
) -> Result<QueryResult, UnsupportedReason> {
    let context = EvalContext {
        database,
        outer_rows: Vec::new(),
    };
    Ok(QueryResult {
        columns: query.output_names(),
        column_types: query.output_types().collect(),
        rows: eval_relation(&query.root, &context)?,
    })
}

fn eval_relation(
    relation: &Relation,
    context: &EvalContext<'_>,
) -> Result<Vec<Row>, UnsupportedReason> {
    match &relation.node {
        RelationNode::Unit => Ok(vec![Row::new([])]),
        RelationNode::Scan { table_index } => context
            .database
            .tables
            .get(*table_index)
            .cloned()
            .ok_or_else(|| {
                internal(format!(
                    "counterexample is missing table index {table_index}"
                ))
            }),
        RelationNode::Product { left, right } => {
            let left = eval_relation(left, context)?;
            let right = eval_relation(right, context)?;
            Ok(product_rows(&left, &right))
        }
        RelationNode::Join {
            kind,
            left,
            right,
            on,
        } => {
            let left_width = left.columns.len();
            let right_width = right.columns.len();
            let left = eval_relation(left, context)?;
            let right = eval_relation(right, context)?;
            concrete_join(&left, &right, left_width, right_width, on, *kind, context)
        }
        RelationNode::Filter { input, predicate } => eval_relation(input, context)?
            .into_iter()
            .filter_map(|row| match eval_expr(predicate, &row.values, context) {
                Ok(Value::Boolean(true)) => Some(Ok(row)),
                Ok(_) => None,
                Err(error) => Some(Err(error)),
            })
            .collect(),
        RelationNode::Project { input, expressions } => {
            let input_rows = eval_relation(input, context)?;
            input_rows
                .iter()
                .enumerate()
                .map(|(row_index, row)| {
                    expressions
                        .iter()
                        .map(|expression| match &expression.kind {
                            ExprKind::WindowRank {
                                function,
                                partition_by,
                                order_by,
                            } => concrete_window_rank(
                                &input_rows,
                                row_index,
                                *function,
                                partition_by,
                                order_by,
                                context,
                            ),
                            ExprKind::WindowAggregate {
                                function,
                                expression,
                                distinct,
                                partition_by,
                                order_by,
                            } => concrete_window_aggregate(
                                &input_rows,
                                row_index,
                                ConcreteWindowAggregate {
                                    function: *function,
                                    expression: expression.as_deref(),
                                    distinct: *distinct,
                                    partition_by,
                                    order_by,
                                },
                                context,
                            ),
                            ExprKind::FirstValue {
                                expression,
                                partition_by,
                                order_by,
                            } => concrete_first_value(
                                &input_rows,
                                row_index,
                                expression,
                                partition_by,
                                order_by,
                                context,
                            ),
                            _ => eval_expr(expression, &row.values, context),
                        })
                        .collect::<Result<Vec<_>, _>>()
                        .map(Row::new)
                })
                .collect()
        }
        RelationNode::Distinct { input } => {
            let mut seen = BTreeSet::new();
            Ok(eval_relation(input, context)?
                .into_iter()
                .filter(|row| seen.insert(row.clone()))
                .collect())
        }
        RelationNode::SetOperation {
            op,
            all,
            left,
            right,
        } => {
            let left = eval_relation(left, context)?;
            let right = eval_relation(right, context)?;
            Ok(concrete_set_operation(*op, *all, left, right))
        }
        RelationNode::Aggregate {
            input,
            group_by,
            expressions,
            having,
        } => {
            let input_rows = eval_relation(input, context)?;
            eval_aggregate_relation(
                &input_rows,
                input.columns.len(),
                group_by,
                expressions,
                having.as_ref(),
                context,
            )
        }
        RelationNode::Sort { input, keys } => {
            let rows = eval_relation(input, context)?;
            sort_concrete_rows(rows, keys, context)
        }
        RelationNode::Slice {
            input,
            offset,
            limit,
        } => {
            let rows = eval_relation(input, context)?;
            Ok(rows
                .into_iter()
                .skip(*offset)
                .take(limit.unwrap_or(usize::MAX))
                .collect())
        }
    }
}

struct ConcreteWindowAggregate<'expression> {
    function: AggregateFunction,
    expression: Option<&'expression TypedExpr>,
    distinct: bool,
    partition_by: &'expression [TypedExpr],
    order_by: &'expression [SortKey],
}

fn concrete_window_aggregate(
    rows: &[Row],
    row_index: usize,
    window: ConcreteWindowAggregate<'_>,
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    let ConcreteWindowAggregate {
        function,
        expression,
        distinct,
        partition_by,
        order_by,
    } = window;
    let row = rows
        .get(row_index)
        .ok_or_else(|| internal("window aggregate row index is out of bounds"))?;
    let partition = partition_by
        .iter()
        .map(|expression| eval_expr(expression, &row.values, context))
        .collect::<Result<Vec<_>, _>>()?;
    let current_order = order_by
        .iter()
        .map(|key| eval_expr(&key.expression, &row.values, context))
        .collect::<Result<Vec<_>, _>>()?;
    let members = rows
        .iter()
        .filter_map(|candidate| {
            let candidate_partition = partition_by
                .iter()
                .map(|expression| eval_expr(expression, &candidate.values, context))
                .collect::<Result<Vec<_>, _>>();
            match candidate_partition {
                Ok(candidate_partition) if candidate_partition == partition => Some(
                    order_by
                        .iter()
                        .map(|key| eval_expr(&key.expression, &candidate.values, context))
                        .collect::<Result<Vec<_>, _>>()
                        .map(|candidate_order| {
                            (
                                order_by.is_empty()
                                    || compare_sort_keys(
                                        &candidate_order,
                                        &current_order,
                                        order_by,
                                    )
                                    .is_le(),
                                candidate.clone(),
                            )
                        }),
                ),
                Ok(_) => None,
                Err(error) => Some(Err(error)),
            }
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?
        .into_iter()
        .filter_map(|(included, row)| included.then_some(row))
        .collect::<Vec<_>>();
    eval_aggregate(function, expression, distinct, &members, context)
}

fn concrete_first_value(
    rows: &[Row],
    row_index: usize,
    expression: &TypedExpr,
    partition_by: &[TypedExpr],
    order_by: &[SortKey],
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    let row = rows
        .get(row_index)
        .ok_or_else(|| internal("FIRST_VALUE row index is out of bounds"))?;
    let partition = partition_by
        .iter()
        .map(|expression| eval_expr(expression, &row.values, context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut best: Option<(usize, Vec<Value>)> = None;
    for (candidate_index, candidate) in rows.iter().enumerate() {
        let candidate_partition = partition_by
            .iter()
            .map(|expression| eval_expr(expression, &candidate.values, context))
            .collect::<Result<Vec<_>, _>>()?;
        if candidate_partition != partition {
            continue;
        }
        let candidate_order = order_by
            .iter()
            .map(|key| eval_expr(&key.expression, &candidate.values, context))
            .collect::<Result<Vec<_>, _>>()?;
        let replace = best.as_ref().is_none_or(|(best_index, best_order)| {
            let ordering = compare_sort_keys(&candidate_order, best_order, order_by);
            ordering.is_lt() || (ordering.is_eq() && candidate_index < *best_index)
        });
        if replace {
            best = Some((candidate_index, candidate_order));
        }
    }
    let (best_index, _) =
        best.ok_or_else(|| internal("FIRST_VALUE partition unexpectedly has no rows"))?;
    eval_expr(expression, &rows[best_index].values, context)
}

fn concrete_window_rank(
    rows: &[Row],
    row_index: usize,
    function: WindowRankFunction,
    partition_by: &[TypedExpr],
    order_by: &[SortKey],
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    let row = rows
        .get(row_index)
        .ok_or_else(|| internal("ROW_NUMBER row index is out of bounds"))?;
    let partition = partition_by
        .iter()
        .map(|expression| eval_expr(expression, &row.values, context))
        .collect::<Result<Vec<_>, _>>()?;
    let order = order_by
        .iter()
        .map(|key| eval_expr(&key.expression, &row.values, context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut rank = 1_usize;
    let mut dense_predecessors = BTreeSet::new();
    for (other_index, other) in rows.iter().enumerate() {
        let other_partition = partition_by
            .iter()
            .map(|expression| eval_expr(expression, &other.values, context))
            .collect::<Result<Vec<_>, _>>()?;
        if other_partition != partition {
            continue;
        }
        let other_order = order_by
            .iter()
            .map(|key| eval_expr(&key.expression, &other.values, context))
            .collect::<Result<Vec<_>, _>>()?;
        let ordering = compare_sort_keys(&other_order, &order, order_by);
        match function {
            WindowRankFunction::RowNumber
                if ordering.is_lt() || (ordering.is_eq() && other_index < row_index) =>
            {
                rank = rank.saturating_add(1);
            }
            WindowRankFunction::Rank if ordering.is_lt() => {
                rank = rank.saturating_add(1);
            }
            WindowRankFunction::DenseRank if ordering.is_lt() => {
                dense_predecessors.insert(other_order);
            }
            _ => {}
        }
    }
    if function == WindowRankFunction::DenseRank {
        rank = dense_predecessors.len().saturating_add(1);
    }
    i64::try_from(rank)
        .map(Value::Integer)
        .map_err(|_| internal("ROW_NUMBER result is outside i64"))
}

fn sort_concrete_rows(
    rows: Vec<Row>,
    keys: &[SortKey],
    context: &EvalContext<'_>,
) -> Result<Vec<Row>, UnsupportedReason> {
    let mut keyed = rows
        .into_iter()
        .map(|row| {
            let values = keys
                .iter()
                .map(|key| eval_expr(&key.expression, &row.values, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((row, values))
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    keyed.sort_by(|(_, left), (_, right)| compare_sort_keys(left, right, keys));
    Ok(keyed.into_iter().map(|(row, _)| row).collect())
}

fn compare_sort_keys(left: &[Value], right: &[Value], keys: &[SortKey]) -> std::cmp::Ordering {
    for ((left, right), key) in left.iter().zip(right).zip(keys) {
        let ordering = match (left, right) {
            (Value::Null, Value::Null) => std::cmp::Ordering::Equal,
            (Value::Null, _) => {
                if key.nulls_first {
                    std::cmp::Ordering::Less
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            (_, Value::Null) => {
                if key.nulls_first {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Less
                }
            }
            _ => value_ordering(left, right).unwrap_or(std::cmp::Ordering::Equal),
        };
        let ordering = if key.ascending {
            ordering
        } else {
            ordering.reverse()
        };
        if !ordering.is_eq() {
            return ordering;
        }
    }
    std::cmp::Ordering::Equal
}

fn value_ordering(left: &Value, right: &Value) -> Option<std::cmp::Ordering> {
    match (left, right) {
        (Value::Integer(left), Value::Integer(right)) => Some(left.cmp(right)),
        (Value::Boolean(left), Value::Boolean(right)) => Some(left.cmp(right)),
        (Value::Text(left), Value::Text(right)) | (Value::Enum(left), Value::Enum(right)) => {
            Some(left.cmp(right))
        }
        (Value::Date(left), Value::Date(right)) => Some(left.cmp(right)),
        (Value::Time(left), Value::Time(right)) => Some(left.cmp(right)),
        (Value::Numeric(left), Value::Numeric(right)) => {
            let left_scaled = i128::from(left.numerator()) * i128::from(right.denominator());
            let right_scaled = i128::from(right.numerator()) * i128::from(left.denominator());
            Some(left_scaled.cmp(&right_scaled))
        }
        _ => None,
    }
}

fn eval_aggregate_relation(
    input: &[Row],
    input_width: usize,
    group_by: &[TypedExpr],
    expressions: &[TypedExpr],
    having: Option<&TypedExpr>,
    context: &EvalContext<'_>,
) -> Result<Vec<Row>, UnsupportedReason> {
    let groups = if group_by.is_empty() {
        vec![input.to_vec()]
    } else {
        let mut groups: BTreeMap<Vec<Value>, Vec<Row>> = BTreeMap::new();
        for row in input {
            let key = group_by
                .iter()
                .map(|expression| eval_expr(expression, &row.values, context))
                .collect::<Result<Vec<_>, _>>()?;
            groups.entry(key).or_default().push(row.clone());
        }
        groups.into_values().collect()
    };

    let mut output = Vec::with_capacity(groups.len());
    for group in groups {
        let null_representative = Row::new(std::iter::repeat_n(Value::Null, input_width));
        let representative = group.first().unwrap_or(&null_representative);
        if let Some(having) = having
            && eval_group_expr(having, &representative.values, &group, context)?
                != Value::Boolean(true)
        {
            continue;
        }
        let values = expressions
            .iter()
            .map(|expression| eval_group_expr(expression, &representative.values, &group, context))
            .collect::<Result<Vec<_>, _>>()?;
        output.push(Row::new(values));
    }
    Ok(output)
}

fn concrete_join(
    left: &[Row],
    right: &[Row],
    left_width: usize,
    right_width: usize,
    on: &TypedExpr,
    kind: JoinKind,
    context: &EvalContext<'_>,
) -> Result<Vec<Row>, UnsupportedReason> {
    let mut output = Vec::new();
    let mut right_matched = vec![false; right.len()];
    for left_row in left {
        let mut left_matched = false;
        for (right_index, right_row) in right.iter().enumerate() {
            let row = concatenate_rows(left_row, right_row);
            if eval_expr(on, &row.values, context)? == Value::Boolean(true) {
                left_matched = true;
                right_matched[right_index] = true;
                output.push(row);
            }
        }
        if !left_matched && matches!(kind, JoinKind::Left | JoinKind::Full) {
            let mut values = left_row.values.clone();
            values.extend(std::iter::repeat_n(Value::Null, right_width));
            output.push(Row::new(values));
        }
    }
    if matches!(kind, JoinKind::Right | JoinKind::Full) {
        for (matched, right_row) in right_matched.into_iter().zip(right) {
            if !matched {
                let mut values = vec![Value::Null; left_width];
                values.extend(right_row.values.iter().cloned());
                output.push(Row::new(values));
            }
        }
    }
    Ok(output)
}

fn concrete_set_operation(op: SetOp, all: bool, mut left: Vec<Row>, right: Vec<Row>) -> Vec<Row> {
    match (op, all) {
        (SetOp::Union, true) => {
            left.extend(right);
            left
        }
        (SetOp::Union, false) => {
            left.extend(right);
            left.into_iter()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
        (SetOp::Intersect, true) => {
            let mut right_counts = bag_counts(right);
            left.into_iter()
                .filter(|row| {
                    let count = right_counts.entry(row.clone()).or_default();
                    if *count == 0 {
                        false
                    } else {
                        *count -= 1;
                        true
                    }
                })
                .collect()
        }
        (SetOp::Intersect, false) => {
            let right = right.into_iter().collect::<BTreeSet<_>>();
            left.into_iter()
                .filter(|row| right.contains(row))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
        (SetOp::Except, true) => {
            let mut right_counts = bag_counts(right);
            left.into_iter()
                .filter(|row| {
                    let count = right_counts.entry(row.clone()).or_default();
                    if *count == 0 {
                        true
                    } else {
                        *count -= 1;
                        false
                    }
                })
                .collect()
        }
        (SetOp::Except, false) => {
            let right = right.into_iter().collect::<BTreeSet<_>>();
            left.into_iter()
                .filter(|row| !right.contains(row))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
    }
}

fn bag_counts(rows: Vec<Row>) -> BTreeMap<Row, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row).or_default() += 1;
    }
    counts
}

fn product_rows(left: &[Row], right: &[Row]) -> Vec<Row> {
    let mut product = Vec::with_capacity(left.len().saturating_mul(right.len()));
    for prefix in left {
        for suffix in right {
            product.push(concatenate_rows(prefix, suffix));
        }
    }
    product
}

fn concatenate_rows(left: &Row, right: &Row) -> Row {
    let mut values = Vec::with_capacity(left.values.len() + right.values.len());
    values.extend(left.values.iter().cloned());
    values.extend(right.values.iter().cloned());
    Row::new(values)
}

pub(crate) fn bags_equal(left: &QueryResult, right: &QueryResult) -> bool {
    if left.column_types != right.column_types {
        return false;
    }
    let mut left_rows = left.rows.clone();
    let mut right_rows = right.rows.clone();
    left_rows.sort_unstable();
    right_rows.sort_unstable();
    left_rows == right_rows
}

pub(crate) fn lists_equal(left: &QueryResult, right: &QueryResult) -> bool {
    left.column_types == right.column_types && left.rows == right.rows
}

pub(crate) fn validate_database(
    schema: &Schema,
    database: &ConcreteDatabase,
) -> Result<(), UnsupportedReason> {
    if database.tables.len() != schema.tables.len() {
        return Err(internal("counterexample has the wrong number of tables"));
    }

    for (table, rows) in schema.tables.iter().zip(&database.tables) {
        for row in rows {
            if row.values.len() != table.columns.len() {
                return Err(internal(format!(
                    "counterexample row for `{}` has the wrong width",
                    table.name
                )));
            }
            for (value, column) in row.values.iter().zip(&table.columns) {
                let type_matches = matches!(
                    (value, column.data_type),
                    (Value::Integer(_), DataType::Integer)
                        | (Value::Boolean(_), DataType::Boolean)
                        | (Value::Text(_), DataType::Text)
                        | (Value::Enum(_), DataType::Enum)
                        | (Value::Date(_), DataType::Date)
                        | (Value::Time(_), DataType::Time)
                        | (Value::Numeric(_), DataType::Numeric)
                        | (Value::Null, _)
                );
                if !type_matches {
                    return Err(internal(format!(
                        "counterexample value for `{}.{}` has the wrong type",
                        table.name, column.name
                    )));
                }
                if !column.nullable && value == &Value::Null {
                    return Err(internal(format!(
                        "counterexample violates NOT NULL on `{}.{}`",
                        table.name, column.name
                    )));
                }
                if let Value::Enum(value) = value
                    && !column.enum_values.contains(value)
                {
                    return Err(internal(format!(
                        "counterexample enum value for `{}.{}` is outside its domain",
                        table.name, column.name
                    )));
                }
            }
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
            let mut seen = BTreeSet::new();
            for row in rows {
                let key = key_indices
                    .iter()
                    .map(|index| row.values[*index].clone())
                    .collect::<Vec<_>>();
                if key.iter().any(|value| value == &Value::Null) {
                    return Err(internal(format!(
                        "counterexample has NULL in primary key for `{}`",
                        table.name
                    )));
                }
                if !seen.insert(key) {
                    return Err(internal(format!(
                        "counterexample has a duplicate primary key for `{}`",
                        table.name
                    )));
                }
            }
        }
    }

    validate_integrity_constraints(schema, database)?;
    Ok(())
}

fn validate_integrity_constraints(
    schema: &Schema,
    database: &ConcreteDatabase,
) -> Result<(), UnsupportedReason> {
    for constraint in &schema.constraints {
        match constraint {
            IntegrityConstraint::PrimaryKey { columns } => {
                validate_key(schema, database, columns, true)?;
            }
            IntegrityConstraint::Unique { columns } => {
                validate_key(schema, database, columns, false)?;
            }
            IntegrityConstraint::ForeignKey {
                columns,
                referenced_columns,
            } => validate_foreign_key(schema, database, columns, referenced_columns)?,
            IntegrityConstraint::Check { predicate } => {
                validate_check(schema, database, predicate)?;
            }
            IntegrityConstraint::AutoIncrement { column } => {
                validate_sequence(schema, database, column, false)?;
            }
            IntegrityConstraint::Consecutive { column } => {
                validate_sequence(schema, database, column, true)?;
            }
        }
    }
    Ok(())
}

fn validate_key(
    schema: &Schema,
    database: &ConcreteDatabase,
    columns: &[ColumnRef],
    primary: bool,
) -> Result<(), UnsupportedReason> {
    let indices = resolve_indices(schema, columns)?;
    let table_index = indices
        .first()
        .map(|(table, _)| *table)
        .ok_or_else(|| internal("validated key became empty"))?;
    let mut seen = BTreeSet::new();
    for row in &database.tables[table_index] {
        let key = indices
            .iter()
            .map(|(_, column)| row.values[*column].clone())
            .collect::<Vec<_>>();
        if key.iter().any(|value| value == &Value::Null) {
            if primary {
                return Err(internal("counterexample has NULL in a primary key"));
            }
            continue;
        }
        if !seen.insert(key) {
            return Err(internal("counterexample has a duplicate unique key"));
        }
    }
    Ok(())
}

fn validate_foreign_key(
    schema: &Schema,
    database: &ConcreteDatabase,
    columns: &[ColumnRef],
    referenced_columns: &[ColumnRef],
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
    for source in &database.tables[source_table] {
        let values = source_indices
            .iter()
            .map(|(_, column)| &source.values[*column])
            .collect::<Vec<_>>();
        if values.contains(&&Value::Null) {
            continue;
        }
        let found = database.tables[target_table].iter().any(|target| {
            values
                .iter()
                .zip(&target_indices)
                .all(|(value, (_, column))| **value == target.values[*column])
        });
        if !found {
            return Err(internal("counterexample violates a foreign key"));
        }
    }
    Ok(())
}

fn validate_check(
    schema: &Schema,
    database: &ConcreteDatabase,
    predicate: &ConstraintPredicate,
) -> Result<(), UnsupportedReason> {
    let mut tables = BTreeSet::new();
    collect_predicate_tables(schema, predicate, &mut tables)?;
    let table_indices = tables.into_iter().collect::<Vec<_>>();
    for assignment in concrete_row_assignments(database, &table_indices) {
        if eval_constraint_predicate(schema, database, predicate, &assignment)?
            == Value::Boolean(false)
        {
            return Err(internal("counterexample violates a check constraint"));
        }
    }
    Ok(())
}

fn validate_sequence(
    schema: &Schema,
    database: &ConcreteDatabase,
    column: &ColumnRef,
    consecutive: bool,
) -> Result<(), UnsupportedReason> {
    let (table_index, column_index, _) = schema.resolve_column(column)?;
    for row in &database.tables[table_index] {
        if row.values[column_index] == Value::Null {
            return Err(internal("counterexample has NULL in a sequence column"));
        }
    }
    for adjacent in database.tables[table_index].windows(2) {
        let [left, right] = adjacent else {
            unreachable!("windows of two always contain two rows");
        };
        let (Value::Integer(left), Value::Integer(right)) =
            (&left.values[column_index], &right.values[column_index])
        else {
            return Err(internal("validated sequence column is not an integer"));
        };
        let valid = if consecutive {
            left.checked_add(1) == Some(*right)
        } else {
            right > left
        };
        if !valid {
            return Err(internal("counterexample violates a sequence constraint"));
        }
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

fn concrete_row_assignments(
    database: &ConcreteDatabase,
    table_indices: &[usize],
) -> Vec<Vec<(usize, usize)>> {
    let mut assignments = vec![Vec::new()];
    for table_index in table_indices {
        let mut expanded = Vec::new();
        for assignment in &assignments {
            for row_index in 0..database.tables[*table_index].len() {
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
    database: &ConcreteDatabase,
    predicate: &ConstraintPredicate,
    assignment: &[(usize, usize)],
) -> Result<Value, UnsupportedReason> {
    match predicate {
        ConstraintPredicate::Compare { op, left, right } => {
            let left = eval_constraint_operand(schema, database, left, assignment)?;
            let right = eval_constraint_operand(schema, database, right, assignment)?;
            let op = match op {
                ConstraintComparison::Equal => CompareOp::Equal,
                ConstraintComparison::NotEqual => CompareOp::NotEqual,
                ConstraintComparison::Less => CompareOp::Less,
                ConstraintComparison::LessOrEqual => CompareOp::LessOrEqual,
                ConstraintComparison::Greater => CompareOp::Greater,
                ConstraintComparison::GreaterOrEqual => CompareOp::GreaterOrEqual,
            };
            compare(op, left, right)
        }
        ConstraintPredicate::Between {
            value,
            lower,
            upper,
        } => {
            let value = eval_constraint_operand(schema, database, value, assignment)?;
            let lower = eval_constraint_operand(schema, database, lower, assignment)?;
            let upper = eval_constraint_operand(schema, database, upper, assignment)?;
            let lower_result = compare(CompareOp::GreaterOrEqual, value.clone(), lower)?;
            let upper_result = compare(CompareOp::LessOrEqual, value, upper)?;
            Ok(sql_and(
                concrete_boolean(lower_result)?,
                concrete_boolean(upper_result)?,
            ))
        }
        ConstraintPredicate::In { value, choices } => {
            let value = eval_constraint_operand(schema, database, value, assignment)?;
            let mut result = Value::Boolean(false);
            for choice in choices {
                let choice = eval_constraint_operand(schema, database, choice, assignment)?;
                let equal = compare(CompareOp::Equal, value.clone(), choice)?;
                result = sql_or(concrete_boolean(result)?, concrete_boolean(equal)?);
            }
            Ok(result)
        }
        ConstraintPredicate::Implies {
            premise,
            conclusion,
        } => {
            let premise = eval_constraint_predicate(schema, database, premise, assignment)?;
            let conclusion = eval_constraint_predicate(schema, database, conclusion, assignment)?;
            let premise = concrete_boolean(premise)?;
            let conclusion = concrete_boolean(conclusion)?;
            Ok(sql_or(premise.map(|value| !value), conclusion))
        }
    }
}

fn eval_constraint_operand(
    schema: &Schema,
    database: &ConcreteDatabase,
    operand: &ConstraintOperand,
    assignment: &[(usize, usize)],
) -> Result<Value, UnsupportedReason> {
    match operand {
        ConstraintOperand::Column(column) => {
            let (table_index, column_index, _) = schema.resolve_column(column)?;
            let row_index = assignment
                .iter()
                .find_map(|(table, row)| (*table == table_index).then_some(*row))
                .ok_or_else(|| internal("constraint row assignment is missing a table"))?;
            Ok(database.tables[table_index][row_index].values[column_index].clone())
        }
        ConstraintOperand::Literal(value) => Ok(value.clone()),
    }
}

fn eval_expr(
    expression: &TypedExpr,
    row: &[Value],
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    eval_expr_context(expression, row, None, context)
}

fn eval_group_expr(
    expression: &TypedExpr,
    row: &[Value],
    group: &[Row],
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    eval_expr_context(expression, row, Some(group), context)
}

fn eval_expr_context(
    expression: &TypedExpr,
    row: &[Value],
    group: Option<&[Row]>,
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    match &expression.kind {
        ExprKind::Column(index) => row
            .get(*index)
            .cloned()
            .ok_or_else(|| internal(format!("column index {index} is outside the concrete row"))),
        ExprKind::OuterColumn { depth, index } => context
            .outer_rows
            .len()
            .checked_sub(depth + 1)
            .and_then(|outer_index| context.outer_rows.get(outer_index))
            .and_then(|outer| outer.get(*index))
            .cloned()
            .ok_or_else(|| {
                internal(format!(
                    "outer column depth {depth}, index {index} is outside the concrete context"
                ))
            }),
        ExprKind::Literal(value) => Ok(value.clone()),
        ExprKind::Compare { op, left, right } => {
            let left = eval_expr_context(left, row, group, context)?;
            let right = eval_expr_context(right, row, group, context)?;
            compare(*op, left, right)
        }
        ExprKind::And(left, right) => {
            let left = eval_boolean_context(left, row, group, context)?;
            let right = eval_boolean_context(right, row, group, context)?;
            Ok(sql_and(left, right))
        }
        ExprKind::Or(left, right) => {
            let left = eval_boolean_context(left, row, group, context)?;
            let right = eval_boolean_context(right, row, group, context)?;
            Ok(sql_or(left, right))
        }
        ExprKind::Not(inner) => match eval_boolean_context(inner, row, group, context)? {
            Some(value) => Ok(Value::Boolean(!value)),
            None => Ok(Value::Null),
        },
        ExprKind::IsNull(inner) => Ok(Value::Boolean(
            eval_expr_context(inner, row, group, context)? == Value::Null,
        )),
        ExprKind::IsNotNull(inner) => Ok(Value::Boolean(
            eval_expr_context(inner, row, group, context)? != Value::Null,
        )),
        ExprKind::Coalesce(expressions) => {
            for expression in expressions {
                let value = eval_expr_context(expression, row, group, context)?;
                if value != Value::Null {
                    return Ok(value);
                }
            }
            Ok(Value::Null)
        }
        ExprKind::Arithmetic { op, left, right } => {
            let left = eval_expr_context(left, row, group, context)?;
            let right = eval_expr_context(right, row, group, context)?;
            eval_arithmetic(*op, left, right)
        }
        ExprKind::Negate(inner) => match eval_expr_context(inner, row, group, context)? {
            Value::Integer(value) => value
                .checked_neg()
                .map(Value::Integer)
                .ok_or_else(|| internal("integer negation overflowed")),
            Value::Numeric(value) => ExactNumeric::new(
                value
                    .numerator()
                    .checked_neg()
                    .ok_or_else(|| internal("numeric negation overflowed"))?,
                value.denominator(),
            )
            .map(Value::Numeric)
            .map_err(|error| internal(format!("invalid numeric negation: {error}"))),
            Value::Null => Ok(Value::Null),
            _ => Err(internal("type checking allowed non-numeric negation")),
        },
        ExprKind::Case {
            branches,
            else_result,
        } => {
            for (condition, result) in branches {
                if eval_expr_context(condition, row, group, context)? == Value::Boolean(true) {
                    return eval_expr_context(result, row, group, context);
                }
            }
            eval_expr_context(else_result, row, group, context)
        }
        ExprKind::Cast {
            expression: inner,
            to,
        } => eval_cast(eval_expr_context(inner, row, group, context)?, *to),
        ExprKind::ScalarFunction {
            function,
            arguments,
        } => {
            let arguments = arguments
                .iter()
                .map(|argument| eval_expr_context(argument, row, group, context))
                .collect::<Result<Vec<_>, _>>()?;
            eval_scalar_function(*function, &arguments)
        }
        ExprKind::Aggregate {
            function,
            expression,
            distinct,
        } => eval_aggregate(
            *function,
            expression.as_deref(),
            *distinct,
            group.ok_or_else(|| internal("aggregate evaluated outside a group"))?,
            context,
        ),
        ExprKind::CountDistinctRow { expressions } => eval_count_distinct_row(
            expressions,
            group.ok_or_else(|| internal("aggregate evaluated outside a group"))?,
            context,
        ),
        ExprKind::Exists { query, negated } => {
            let nested = nested_context(context, row);
            let exists = !eval_relation(query, &nested)?.is_empty();
            Ok(Value::Boolean(if *negated { !exists } else { exists }))
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
            let nested = nested_context(context, row);
            let rows = eval_relation(query, &nested)?;
            let mut matched = false;
            let mut unknown = false;
            for candidate in rows {
                if candidate.values.len() != values.len() {
                    return Err(internal("IN subquery returned the wrong column count"));
                }
                match compare_rows(&values, &candidate.values)? {
                    Value::Boolean(true) => {
                        matched = true;
                        break;
                    }
                    Value::Null => unknown = true,
                    Value::Boolean(false) => {}
                    _ => return Err(internal("comparison returned a non-boolean value")),
                }
            }
            if matched {
                Ok(Value::Boolean(!*negated))
            } else if unknown {
                Ok(Value::Null)
            } else {
                Ok(Value::Boolean(*negated))
            }
        }
        ExprKind::ScalarSubquery { query } => {
            let nested = nested_context(context, row);
            let rows = eval_relation(query, &nested)?;
            match rows.as_slice() {
                [] => Ok(Value::Null),
                [row] => row
                    .values
                    .first()
                    .cloned()
                    .ok_or_else(|| internal("scalar subquery returned no columns")),
                _ => Err(internal(
                    "scalar subquery produced multiple rows despite its static bound",
                )),
            }
        }
        ExprKind::WindowRank { .. }
        | ExprKind::WindowAggregate { .. }
        | ExprKind::FirstValue { .. } => Err(internal(
            "window function was evaluated outside a project relation",
        )),
    }
}

fn compare_rows(left: &[Value], right: &[Value]) -> Result<Value, UnsupportedReason> {
    if left.len() != right.len() {
        return Err(internal("row comparison received different arities"));
    }
    let mut unknown = false;
    for (left, right) in left.iter().zip(right) {
        match compare(CompareOp::Equal, left.clone(), right.clone())? {
            Value::Boolean(false) => return Ok(Value::Boolean(false)),
            Value::Boolean(true) => {}
            Value::Null => unknown = true,
            _ => return Err(internal("comparison returned a non-boolean value")),
        }
    }
    Ok(if unknown {
        Value::Null
    } else {
        Value::Boolean(true)
    })
}

fn nested_context<'database>(
    context: &EvalContext<'database>,
    row: &[Value],
) -> EvalContext<'database> {
    let mut nested = context.clone();
    nested.outer_rows.push(row.to_vec());
    nested
}

fn eval_boolean_context(
    expression: &TypedExpr,
    row: &[Value],
    group: Option<&[Row]>,
    context: &EvalContext<'_>,
) -> Result<Option<bool>, UnsupportedReason> {
    concrete_boolean(eval_expr_context(expression, row, group, context)?)
}

fn eval_arithmetic(
    operator: ArithmeticOp,
    left: Value,
    right: Value,
) -> Result<Value, UnsupportedReason> {
    if left == Value::Null || right == Value::Null {
        return Ok(Value::Null);
    }
    match (left, right) {
        (Value::Integer(left), Value::Integer(right)) => {
            let value = match operator {
                ArithmeticOp::Add => left.checked_add(right).map(Value::Integer),
                ArithmeticOp::Subtract => left.checked_sub(right).map(Value::Integer),
                ArithmeticOp::Multiply => left.checked_mul(right).map(Value::Integer),
                ArithmeticOp::Modulo if right == 0 => return Ok(Value::Null),
                ArithmeticOp::Modulo => left.checked_rem(right).map(Value::Integer),
                ArithmeticOp::Divide => {
                    return numeric_divide(
                        ExactNumeric::from_integer(left),
                        ExactNumeric::from_integer(right),
                    );
                }
            };
            value.ok_or_else(|| internal("integer arithmetic overflowed"))
        }
        (Value::Numeric(left), Value::Numeric(right)) => match operator {
            ArithmeticOp::Add => numeric_binary(left, right, |a, b| a.checked_add(b)),
            ArithmeticOp::Subtract => numeric_binary(left, right, |a, b| a.checked_sub(b)),
            ArithmeticOp::Multiply => {
                let numerator =
                    i128::from(left.numerator()).checked_mul(i128::from(right.numerator()));
                let denominator =
                    i128::from(left.denominator()).checked_mul(i128::from(right.denominator()));
                exact_numeric_value(numerator, denominator)
            }
            ArithmeticOp::Divide => numeric_divide(left, right),
            ArithmeticOp::Modulo => Err(internal("numeric modulo passed type checking")),
        },
        (Value::Date(date), Value::Integer(days))
            if matches!(operator, ArithmeticOp::Add | ArithmeticOp::Subtract) =>
        {
            let days = if operator == ArithmeticOp::Subtract {
                days.checked_neg()
            } else {
                Some(days)
            };
            let shifted = days
                .and_then(|days| i64::from(date.days_since_epoch()).checked_add(days))
                .and_then(|days| i32::try_from(days).ok());
            Ok(shifted.map_or(Value::Null, |days| {
                Value::Date(DateValue::from_days_since_epoch(days))
            }))
        }
        (Value::Integer(days), Value::Date(date)) if operator == ArithmeticOp::Add => {
            let shifted = i64::from(date.days_since_epoch())
                .checked_add(days)
                .and_then(|days| i32::try_from(days).ok());
            Ok(shifted.map_or(Value::Null, |days| {
                Value::Date(DateValue::from_days_since_epoch(days))
            }))
        }
        (Value::Date(left), Value::Date(right)) if operator == ArithmeticOp::Subtract => {
            Ok(Value::Integer(
                i64::from(left.days_since_epoch()) - i64::from(right.days_since_epoch()),
            ))
        }
        _ => Err(internal("type checking allowed unlike arithmetic operands")),
    }
}

fn numeric_binary(
    left: ExactNumeric,
    right: ExactNumeric,
    operation: impl FnOnce(i128, i128) -> Option<i128>,
) -> Result<Value, UnsupportedReason> {
    let left_scaled = i128::from(left.numerator())
        .checked_mul(i128::from(right.denominator()))
        .ok_or_else(|| internal("numeric arithmetic overflowed"))?;
    let right_scaled = i128::from(right.numerator())
        .checked_mul(i128::from(left.denominator()))
        .ok_or_else(|| internal("numeric arithmetic overflowed"))?;
    let numerator = operation(left_scaled, right_scaled);
    let denominator = i128::from(left.denominator()).checked_mul(i128::from(right.denominator()));
    exact_numeric_value(numerator, denominator)
}

fn numeric_divide(left: ExactNumeric, right: ExactNumeric) -> Result<Value, UnsupportedReason> {
    if right.numerator() == 0 {
        return Ok(Value::Null);
    }
    exact_numeric_value(
        i128::from(left.numerator()).checked_mul(i128::from(right.denominator())),
        i128::from(left.denominator()).checked_mul(i128::from(right.numerator())),
    )
}

fn exact_numeric_value(
    numerator: Option<i128>,
    denominator: Option<i128>,
) -> Result<Value, UnsupportedReason> {
    let numerator = numerator.ok_or_else(|| internal("numeric arithmetic overflowed"))?;
    let denominator = denominator.ok_or_else(|| internal("numeric arithmetic overflowed"))?;
    let numerator =
        i64::try_from(numerator).map_err(|_| internal("numeric result is outside i64"))?;
    let denominator =
        i64::try_from(denominator).map_err(|_| internal("numeric result is outside i64"))?;
    ExactNumeric::new(numerator, denominator)
        .map(Value::Numeric)
        .map_err(|error| internal(format!("invalid exact numeric result: {error}")))
}

fn eval_cast(value: Value, target: DataType) -> Result<Value, UnsupportedReason> {
    if value == Value::Null {
        return Ok(Value::Null);
    }
    match (value, target) {
        (value @ Value::Integer(_), DataType::Integer)
        | (value @ Value::Boolean(_), DataType::Boolean)
        | (value @ Value::Text(_), DataType::Text)
        | (value @ Value::Enum(_), DataType::Enum)
        | (value @ Value::Date(_), DataType::Date)
        | (value @ Value::Time(_), DataType::Time)
        | (value @ Value::Numeric(_), DataType::Numeric) => Ok(value),
        (Value::Integer(value), DataType::Numeric) => {
            Ok(Value::Numeric(ExactNumeric::from_integer(value)))
        }
        (Value::Boolean(value), DataType::Integer) => Ok(Value::Integer(i64::from(value))),
        (Value::Integer(value), DataType::Boolean) => Ok(Value::Boolean(value != 0)),
        (Value::Numeric(value), DataType::Boolean) => Ok(Value::Boolean(value.numerator() != 0)),
        (Value::Text(value), DataType::Enum) => Ok(Value::Enum(value)),
        (Value::Enum(value), DataType::Text) => Ok(Value::Text(value)),
        _ => Err(internal("unsupported cast passed type checking")),
    }
}

fn eval_scalar_function(
    function: ScalarFunction,
    arguments: &[Value],
) -> Result<Value, UnsupportedReason> {
    if arguments.iter().any(|argument| argument == &Value::Null) {
        return Ok(Value::Null);
    }
    match function {
        ScalarFunction::Abs => match arguments {
            [Value::Integer(value)] => value
                .checked_abs()
                .map(Value::Integer)
                .ok_or_else(|| internal("ABS overflowed")),
            [Value::Numeric(value)] => ExactNumeric::new(
                value
                    .numerator()
                    .checked_abs()
                    .ok_or_else(|| internal("ABS overflowed"))?,
                value.denominator(),
            )
            .map(Value::Numeric)
            .map_err(|error| internal(format!("invalid ABS result: {error}"))),
            _ => Err(internal("ABS received invalid arguments")),
        },
        ScalarFunction::Round => {
            let [Value::Numeric(value), rest @ ..] = arguments else {
                if let [value @ Value::Integer(_), ..] = arguments {
                    return Ok(value.clone());
                }
                return Err(internal("ROUND received invalid arguments"));
            };
            let scale = match rest {
                [] => 0,
                [Value::Integer(scale)] => {
                    i32::try_from(*scale).map_err(|_| internal("ROUND scale is outside i32"))?
                }
                _ => return Err(internal("ROUND received invalid scale arguments")),
            };
            round_numeric(*value, scale).map(Value::Numeric)
        }
        ScalarFunction::Truncate => {
            let [value, Value::Integer(scale)] = arguments else {
                return Err(internal("TRUNCATE received invalid arguments"));
            };
            let scale =
                i32::try_from(*scale).map_err(|_| internal("TRUNCATE scale is outside i32"))?;
            match value {
                Value::Integer(value) if scale >= 0 => Ok(Value::Integer(*value)),
                Value::Integer(value) => {
                    let factor = 10_i64
                        .checked_pow(scale.unsigned_abs())
                        .ok_or_else(|| internal("TRUNCATE scale is too large"))?;
                    Ok(Value::Integer(value / factor * factor))
                }
                Value::Numeric(value) => truncate_numeric(*value, scale).map(Value::Numeric),
                _ => Err(internal("TRUNCATE received a non-numeric argument")),
            }
        }
        ScalarFunction::Concat => {
            let mut result = String::new();
            for argument in arguments {
                let Value::Text(value) = argument else {
                    return Err(internal("CONCAT received a non-text argument"));
                };
                result.push_str(value);
            }
            Ok(Value::Text(result))
        }
        ScalarFunction::Length => match arguments {
            [Value::Text(value)] => i64::try_from(value.chars().count())
                .map(Value::Integer)
                .map_err(|_| internal("text length is outside i64")),
            _ => Err(internal("LENGTH received invalid arguments")),
        },
        ScalarFunction::DateDiff => match arguments {
            [Value::Date(left), Value::Date(right)] => Ok(Value::Integer(
                i64::from(left.days_since_epoch()) - i64::from(right.days_since_epoch()),
            )),
            _ => Err(internal("DATEDIFF received invalid arguments")),
        },
        ScalarFunction::Year | ScalarFunction::Month | ScalarFunction::Day => match arguments {
            [Value::Date(value)] => {
                let (year, month, day) = value.components();
                Ok(Value::Integer(match function {
                    ScalarFunction::Year => year,
                    ScalarFunction::Month => month,
                    ScalarFunction::Day => day,
                    _ => unreachable!(),
                }))
            }
            _ => Err(internal("date-part function received invalid arguments")),
        },
        ScalarFunction::ToDays => match arguments {
            [Value::Date(value)] => Ok(Value::Integer(
                i64::from(value.days_since_epoch()) + 719_528,
            )),
            _ => Err(internal("TO_DAYS received invalid arguments")),
        },
        ScalarFunction::LastDay => match arguments {
            [Value::Date(value)] => {
                let (year, month, day) = value.components();
                let remaining = concrete_days_in_month(year, month) - day;
                let days = i64::from(value.days_since_epoch()) + remaining;
                i32::try_from(days)
                    .map(DateValue::from_days_since_epoch)
                    .map(Value::Date)
                    .map_err(|_| internal("LAST_DAY overflowed the supported date range"))
            }
            _ => Err(internal("LAST_DAY received invalid arguments")),
        },
        ScalarFunction::Weekday => match arguments {
            [Value::Date(value)] => Ok(Value::Integer(
                (i64::from(value.days_since_epoch()) + 3).rem_euclid(7),
            )),
            _ => Err(internal("WEEKDAY received invalid arguments")),
        },
        ScalarFunction::DayOfWeek => match arguments {
            [Value::Date(value)] => Ok(Value::Integer(
                (i64::from(value.days_since_epoch()) + 4).rem_euclid(7) + 1,
            )),
            _ => Err(internal("DAYOFWEEK received invalid arguments")),
        },
        ScalarFunction::Quarter => match arguments {
            [Value::Date(value)] => {
                let (_, month, _) = value.components();
                Ok(Value::Integer((month - 1) / 3 + 1))
            }
            _ => Err(internal("QUARTER received invalid arguments")),
        },
        ScalarFunction::Sign => match arguments {
            [Value::Integer(value)] => Ok(Value::Integer(value.signum())),
            [Value::Numeric(value)] => Ok(Value::Integer(value.numerator().signum())),
            _ => Err(internal("SIGN received invalid arguments")),
        },
        ScalarFunction::Power(exponent) => match arguments {
            [Value::Numeric(value)] => ExactNumeric::new(
                value
                    .numerator()
                    .checked_pow(exponent)
                    .ok_or_else(|| internal("POWER overflowed"))?,
                value
                    .denominator()
                    .checked_pow(exponent)
                    .ok_or_else(|| internal("POWER overflowed"))?,
            )
            .map(Value::Numeric)
            .map_err(|error| internal(format!("invalid POWER result: {error}"))),
            _ => Err(internal("POWER received invalid arguments")),
        },
        ScalarFunction::Floor | ScalarFunction::Ceil => match arguments {
            [Value::Numeric(value)] => {
                let numerator = i128::from(value.numerator());
                let denominator = i128::from(value.denominator());
                let result = if function == ScalarFunction::Floor {
                    numerator.div_euclid(denominator)
                } else {
                    -(-numerator).div_euclid(denominator)
                };
                i64::try_from(result)
                    .map(Value::Integer)
                    .map_err(|_| internal("FLOOR or CEIL result is outside i64"))
            }
            _ => Err(internal("FLOOR or CEIL received invalid arguments")),
        },
        ScalarFunction::StartsWith | ScalarFunction::EndsWith | ScalarFunction::Contains => {
            let [Value::Text(value), Value::Text(pattern)] = arguments else {
                return Err(internal("LIKE received invalid arguments"));
            };
            Ok(Value::Boolean(match function {
                ScalarFunction::StartsWith => value.starts_with(pattern),
                ScalarFunction::EndsWith => value.ends_with(pattern),
                ScalarFunction::Contains => value.contains(pattern),
                _ => unreachable!(),
            }))
        }
        ScalarFunction::Substring { start, length } => match arguments {
            [Value::Text(value)] => Ok(Value::Text(
                value
                    .chars()
                    .skip(start)
                    .take(length.unwrap_or(usize::MAX))
                    .collect(),
            )),
            _ => Err(internal("SUBSTRING received invalid arguments")),
        },
        ScalarFunction::Left(length) | ScalarFunction::Right(length) => match arguments {
            [Value::Text(value)] => {
                let characters = value.chars().collect::<Vec<_>>();
                let range = if matches!(function, ScalarFunction::Left(_)) {
                    0..characters.len().min(length)
                } else {
                    characters.len().saturating_sub(length)..characters.len()
                };
                Ok(Value::Text(characters[range].iter().collect()))
            }
            _ => Err(internal("LEFT or RIGHT received invalid arguments")),
        },
    }
}

fn concrete_days_in_month(year: i64, month: i64) -> i64 {
    match month {
        4 | 6 | 9 | 11 => 30,
        2 if year.rem_euclid(4) == 0
            && (year.rem_euclid(100) != 0 || year.rem_euclid(400) == 0) =>
        {
            29
        }
        2 => 28,
        _ => 31,
    }
}

fn round_numeric(value: ExactNumeric, scale: i32) -> Result<ExactNumeric, UnsupportedReason> {
    let power = scale.unsigned_abs();
    let factor = 10_i128
        .checked_pow(power)
        .ok_or_else(|| internal("ROUND scale is too large"))?;
    let numerator = i128::from(value.numerator());
    let denominator = i128::from(value.denominator());
    let (rounded, output_denominator) = if scale >= 0 {
        (
            round_ratio(
                numerator
                    .checked_mul(factor)
                    .ok_or_else(|| internal("ROUND overflowed"))?,
                denominator,
            ),
            factor,
        )
    } else {
        (
            round_ratio(
                numerator,
                denominator
                    .checked_mul(factor)
                    .ok_or_else(|| internal("ROUND overflowed"))?,
            )
            .checked_mul(factor)
            .ok_or_else(|| internal("ROUND overflowed"))?,
            1,
        )
    };
    ExactNumeric::new(
        i64::try_from(rounded).map_err(|_| internal("ROUND result is outside i64"))?,
        i64::try_from(output_denominator)
            .map_err(|_| internal("ROUND denominator is outside i64"))?,
    )
    .map_err(|error| internal(format!("invalid ROUND result: {error}")))
}

fn truncate_numeric(value: ExactNumeric, scale: i32) -> Result<ExactNumeric, UnsupportedReason> {
    let factor = 10_i128
        .checked_pow(scale.unsigned_abs())
        .ok_or_else(|| internal("TRUNCATE scale is too large"))?;
    let numerator = i128::from(value.numerator());
    let denominator = i128::from(value.denominator());
    let (truncated, output_denominator) = if scale >= 0 {
        (
            numerator
                .checked_mul(factor)
                .ok_or_else(|| internal("TRUNCATE overflowed"))?
                / denominator,
            factor,
        )
    } else {
        (
            (numerator
                / denominator
                    .checked_mul(factor)
                    .ok_or_else(|| internal("TRUNCATE overflowed"))?)
            .checked_mul(factor)
            .ok_or_else(|| internal("TRUNCATE overflowed"))?,
            1,
        )
    };
    ExactNumeric::new(
        i64::try_from(truncated).map_err(|_| internal("TRUNCATE result is outside i64"))?,
        i64::try_from(output_denominator)
            .map_err(|_| internal("TRUNCATE denominator is outside i64"))?,
    )
    .map_err(|error| internal(format!("invalid TRUNCATE result: {error}")))
}

fn round_ratio(numerator: i128, denominator: i128) -> i128 {
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if remainder.unsigned_abs() * 2 >= denominator.unsigned_abs() {
        quotient + if numerator.is_negative() { -1 } else { 1 }
    } else {
        quotient
    }
}

fn eval_aggregate(
    function: AggregateFunction,
    expression: Option<&TypedExpr>,
    distinct: bool,
    group: &[Row],
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    if function == AggregateFunction::Count && expression.is_none() {
        return i64::try_from(group.len())
            .map(Value::Integer)
            .map_err(|_| internal("COUNT is outside i64"));
    }
    let expression = expression.ok_or_else(|| internal("aggregate argument is missing"))?;
    let mut values = group
        .iter()
        .map(|row| eval_expr(expression, &row.values, context))
        .collect::<Result<Vec<_>, _>>()?;
    values.retain(|value| value != &Value::Null);
    if distinct {
        values = values
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
    }
    match function {
        AggregateFunction::Count => i64::try_from(values.len())
            .map(Value::Integer)
            .map_err(|_| internal("COUNT is outside i64")),
        AggregateFunction::Sum => sum_values(&values),
        AggregateFunction::Avg => {
            let sum = sum_values(&values)?;
            let count =
                i64::try_from(values.len()).map_err(|_| internal("AVG count overflowed"))?;
            match sum {
                Value::Null => Ok(Value::Null),
                Value::Integer(sum) => {
                    exact_numeric_value(Some(i128::from(sum)), Some(i128::from(count)))
                }
                Value::Numeric(sum) => exact_numeric_value(
                    Some(i128::from(sum.numerator())),
                    i128::from(sum.denominator()).checked_mul(i128::from(count)),
                ),
                _ => Err(internal("AVG received a non-numeric sum")),
            }
        }
        AggregateFunction::Min | AggregateFunction::Max => {
            let mut result: Option<Value> = None;
            for value in values {
                let replace = match &result {
                    None => true,
                    Some(current) => {
                        let operator = if function == AggregateFunction::Min {
                            CompareOp::Less
                        } else {
                            CompareOp::Greater
                        };
                        compare(operator, value.clone(), current.clone())? == Value::Boolean(true)
                    }
                };
                if replace {
                    result = Some(value);
                }
            }
            Ok(result.unwrap_or(Value::Null))
        }
    }
}

fn eval_count_distinct_row(
    expressions: &[TypedExpr],
    group: &[Row],
    context: &EvalContext<'_>,
) -> Result<Value, UnsupportedReason> {
    let mut distinct = BTreeSet::new();
    for row in group {
        let values = expressions
            .iter()
            .map(|expression| eval_expr(expression, &row.values, context))
            .collect::<Result<Vec<_>, _>>()?;
        if !values.contains(&Value::Null) {
            distinct.insert(values);
        }
    }
    i64::try_from(distinct.len())
        .map(Value::Integer)
        .map_err(|_| internal("COUNT(DISTINCT ...) is outside i64"))
}

fn sum_values(values: &[Value]) -> Result<Value, UnsupportedReason> {
    let Some(first) = values.first() else {
        return Ok(Value::Null);
    };
    match first {
        Value::Integer(_) | Value::Boolean(_) => {
            let mut sum = 0_i64;
            for value in values {
                let value = match value {
                    Value::Integer(value) => *value,
                    Value::Boolean(value) => i64::from(*value),
                    _ => return Err(internal("SUM received mixed value types")),
                };
                sum = sum
                    .checked_add(value)
                    .ok_or_else(|| internal("SUM overflowed"))?;
            }
            Ok(Value::Integer(sum))
        }
        Value::Numeric(_) => {
            let mut sum = ExactNumeric::from_integer(0);
            for value in values {
                let Value::Numeric(value) = value else {
                    return Err(internal("SUM received mixed value types"));
                };
                let Value::Numeric(next) =
                    numeric_binary(sum, *value, |left, right| left.checked_add(right))?
                else {
                    unreachable!("numeric addition returns a numeric value");
                };
                sum = next;
            }
            Ok(Value::Numeric(sum))
        }
        _ => Err(internal("SUM received a non-numeric value")),
    }
}

fn concrete_boolean(value: Value) -> Result<Option<bool>, UnsupportedReason> {
    match value {
        Value::Boolean(value) => Ok(Some(value)),
        Value::Null => Ok(None),
        Value::Integer(_)
        | Value::Text(_)
        | Value::Enum(_)
        | Value::Date(_)
        | Value::Time(_)
        | Value::Numeric(_) => Err(internal("type checking allowed a non-boolean predicate")),
    }
}

fn compare(operator: CompareOp, left: Value, right: Value) -> Result<Value, UnsupportedReason> {
    if left == Value::Null || right == Value::Null {
        return Ok(Value::Null);
    }
    let result = match (left, right) {
        (Value::Integer(left), Value::Integer(right)) => match operator {
            CompareOp::Equal => left == right,
            CompareOp::NotEqual => left != right,
            CompareOp::Less => left < right,
            CompareOp::LessOrEqual => left <= right,
            CompareOp::Greater => left > right,
            CompareOp::GreaterOrEqual => left >= right,
        },
        (Value::Boolean(left), Value::Boolean(right)) => apply_ordering(operator, left.cmp(&right)),
        (Value::Text(left), Value::Text(right)) | (Value::Enum(left), Value::Enum(right)) => {
            apply_ordering(operator, left.cmp(&right))
        }
        (Value::Date(left), Value::Date(right)) => apply_ordering(operator, left.cmp(&right)),
        (Value::Time(left), Value::Time(right)) => apply_ordering(operator, left.cmp(&right)),
        (Value::Numeric(left), Value::Numeric(right)) => {
            let left_scaled = i128::from(left.numerator()) * i128::from(right.denominator());
            let right_scaled = i128::from(right.numerator()) * i128::from(left.denominator());
            apply_ordering(operator, left_scaled.cmp(&right_scaled))
        }
        _ => {
            return Err(internal(
                "type checking allowed a comparison between unlike values",
            ));
        }
    };
    Ok(Value::Boolean(result))
}

fn apply_ordering(operator: CompareOp, ordering: std::cmp::Ordering) -> bool {
    match operator {
        CompareOp::Equal => ordering.is_eq(),
        CompareOp::NotEqual => ordering.is_ne(),
        CompareOp::Less => ordering.is_lt(),
        CompareOp::LessOrEqual => !ordering.is_gt(),
        CompareOp::Greater => ordering.is_gt(),
        CompareOp::GreaterOrEqual => !ordering.is_lt(),
    }
}

fn sql_and(left: Option<bool>, right: Option<bool>) -> Value {
    match (left, right) {
        (Some(false), _) | (_, Some(false)) => Value::Boolean(false),
        (Some(true), Some(true)) => Value::Boolean(true),
        _ => Value::Null,
    }
}

fn sql_or(left: Option<bool>, right: Option<bool>) -> Value {
    match (left, right) {
        (Some(true), _) | (_, Some(true)) => Value::Boolean(true),
        (Some(false), Some(false)) => Value::Boolean(false),
        _ => Value::Null,
    }
}

fn internal(message: impl Into<String>) -> UnsupportedReason {
    UnsupportedReason::new(UnsupportedKind::Internal, message)
}
