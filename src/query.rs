use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use sqlparser::ast::{
    BinaryOperator, CastKind, CeilFloorKind, DataType as SqlDataType, DateTimeField,
    DuplicateTreatment, Expr as SqlExpr, Function, FunctionArg, FunctionArgExpr, FunctionArguments,
    GroupByExpr, Ident, JoinConstraint, JoinOperator, LimitClause, ObjectName, ObjectNamePart,
    OrderByKind, Query, Select, SelectItem, SelectItemQualifiedWildcardKind, SetExpr,
    SetOperator as SqlSetOperator, SetQuantifier, Statement, TableFactor, UnaryOperator,
    Value as SqlValue, WildcardAdditionalOptions, WindowType,
};
use sqlparser::dialect::GenericDialect;
use sqlparser::parser::Parser;

use crate::counterexample::{DateValue, ExactNumeric, TimeValue, Value};
use crate::ir::{
    AggregateFunction, ArithmeticOp, ColumnMeta, CompareOp, ExprKind, FunctionalDependency,
    JoinKind, QuerySemantics, Relation, RelationNode, ScalarFunction, SetOp, SortKey, TypedExpr,
    TypedQuery, WindowRankFunction,
};
use crate::outcome::{UnsupportedKind, UnsupportedReason};
use crate::schema::{DataType, IntegrityConstraint, Schema, canonical_name};

pub(crate) fn parse_query(
    schema: &Schema,
    sql: &str,
    bound: usize,
    max_intermediate_rows: usize,
    ignore_top_level_order: bool,
    permissive_grouping: bool,
    mysql_coercions: bool,
) -> Result<TypedQuery, UnsupportedReason> {
    let statements = Parser::parse_sql(&GenericDialect {}, sql)
        .map_err(|error| unsupported(UnsupportedKind::ParseError, error.to_string()))?;
    if statements.len() != 1 {
        return Err(sql_unsupported("exactly one SELECT statement is required"));
    }
    let statement = statements
        .into_iter()
        .next()
        .ok_or_else(|| sql_unsupported("exactly one SELECT statement is required"))?;
    let Statement::Query(mut query) = statement else {
        return Err(sql_unsupported("only SELECT queries are supported"));
    };
    if ignore_top_level_order && query.limit_clause.is_none() {
        query.order_by = None;
    }
    if query.fetch.is_some()
        || !query.locks.is_empty()
        || query.for_clause.is_some()
        || query.settings.is_some()
        || query.format_clause.is_some()
        || !query.pipe_operators.is_empty()
    {
        return Err(sql_unsupported(
            "FETCH, locking, and dialect-specific query clauses are unsupported",
        ));
    }
    let mut lowerer = Lowerer {
        schema,
        bound,
        max_intermediate_rows,
        qualifiers: HashSet::new(),
        ctes: HashMap::new(),
        outer_scopes: Vec::new(),
        clause_aliases: Vec::new(),
        allow_window_functions: false,
        permissive_grouping,
        mysql_coercions,
    };
    let (root, semantics) = lowerer.lower_query(&query)?;
    validate_recursive_complexity(&root, max_intermediate_rows)?;
    Ok(TypedQuery { root, semantics })
}

struct Lowerer<'schema> {
    schema: &'schema Schema,
    bound: usize,
    max_intermediate_rows: usize,
    qualifiers: HashSet<String>,
    ctes: HashMap<String, Relation>,
    outer_scopes: Vec<Vec<ColumnMeta>>,
    clause_aliases: Vec<(String, TypedExpr)>,
    allow_window_functions: bool,
    permissive_grouping: bool,
    mysql_coercions: bool,
}

impl Lowerer<'_> {
    fn lower_query(
        &mut self,
        query: &Query,
    ) -> Result<(Relation, QuerySemantics), UnsupportedReason> {
        validate_query_clauses(query)?;
        let saved_ctes = self.ctes.clone();
        let result = (|| {
            if let Some(with) = &query.with {
                if with.recursive {
                    return Err(sql_unsupported("recursive CTEs are unsupported"));
                }
                let mut local_names = HashSet::new();
                for cte in &with.cte_tables {
                    if cte.from.is_some() {
                        return Err(sql_unsupported("CTE FROM clauses are unsupported"));
                    }
                    if cte.alias.at.is_some() {
                        return Err(sql_unsupported("AT aliases are unsupported"));
                    }
                    let name = identifier(&cte.alias.name, "CTE name")?;
                    if !local_names.insert(name.clone()) {
                        return Err(unsupported(
                            UnsupportedKind::NameResolution,
                            format!("duplicate CTE name `{name}`"),
                        ));
                    }
                    let (mut relation, _) = self.lower_query(&cte.query)?;
                    apply_column_aliases(&mut relation, &cte.alias.columns)?;
                    for column in &mut relation.columns {
                        column.qualifier = None;
                        column.source_qualifier = None;
                        column.source_name = None;
                    }
                    self.ctes.insert(name, relation);
                }
            }
            let relation = self.lower_set_expr(query.body.as_ref())?;
            let relation = self.lower_order_and_slice(
                relation,
                query.order_by.as_ref(),
                query.limit_clause.as_ref(),
            )?;
            Ok((
                relation,
                QuerySemantics {
                    ordered: query.order_by.is_some(),
                    sliced: query.limit_clause.is_some(),
                },
            ))
        })();
        self.ctes = saved_ctes;
        result
    }

    fn lower_order_and_slice(
        &mut self,
        mut relation: Relation,
        order_by: Option<&sqlparser::ast::OrderBy>,
        limit_clause: Option<&LimitClause>,
    ) -> Result<Relation, UnsupportedReason> {
        if let Some(order_by) = order_by {
            if order_by.interpolate.is_some() {
                return Err(sql_unsupported("ORDER BY INTERPOLATE is unsupported"));
            }
            let OrderByKind::Expressions(order_expressions) = &order_by.kind else {
                return Err(sql_unsupported("ORDER BY ALL is unsupported"));
            };
            if order_expressions.is_empty() {
                return Err(sql_unsupported("ORDER BY needs at least one key"));
            }
            let mut keys = Vec::with_capacity(order_expressions.len());
            for order in order_expressions {
                if order.with_fill.is_some() {
                    return Err(sql_unsupported("ORDER BY WITH FILL is unsupported"));
                }
                let expression = if let SqlExpr::Value(value) = &order.expr
                    && let SqlValue::Number(position, _) = &value.value
                    && !position.contains('.')
                {
                    let position = position
                        .parse::<usize>()
                        .map_err(|_| type_error("ORDER BY position is outside usize"))?;
                    let column =
                        relation
                            .columns
                            .get(position.wrapping_sub(1))
                            .ok_or_else(|| {
                                type_error(format!("ORDER BY position {position} is invalid"))
                            })?;
                    TypedExpr::column(position - 1, column)
                } else {
                    lower_expr(self, &order.expr, &relation.columns, None)?
                };
                if contains_aggregate(&expression) {
                    return Err(sql_unsupported(
                        "ORDER BY aggregate expressions must reference a projected alias or position",
                    ));
                }
                let ascending = order.options.asc.unwrap_or(true);
                keys.push(SortKey {
                    expression,
                    ascending,
                    nulls_first: order.options.nulls_first.unwrap_or(ascending),
                });
            }
            relation = Relation {
                columns: relation.columns.clone(),
                max_rows: relation.max_rows,
                functional_dependencies: relation.functional_dependencies.clone(),
                node: RelationNode::Sort {
                    input: Box::new(relation),
                    keys,
                },
            };
        }

        if let Some(limit_clause) = limit_clause {
            let (offset, limit) = match limit_clause {
                LimitClause::LimitOffset {
                    limit,
                    offset,
                    limit_by,
                } => {
                    if !limit_by.is_empty() {
                        return Err(sql_unsupported("LIMIT BY is unsupported"));
                    }
                    (
                        offset
                            .as_ref()
                            .map(|offset| parse_slice_value(&offset.value, "OFFSET"))
                            .transpose()?
                            .unwrap_or(0),
                        limit
                            .as_ref()
                            .map(|limit| parse_slice_value(limit, "LIMIT"))
                            .transpose()?,
                    )
                }
                LimitClause::OffsetCommaLimit { offset, limit } => (
                    parse_slice_value(offset, "OFFSET")?,
                    Some(parse_slice_value(limit, "LIMIT")?),
                ),
            };
            let remaining = relation.max_rows.saturating_sub(offset);
            relation = Relation {
                columns: relation.columns.clone(),
                max_rows: limit.map_or(remaining, |limit| remaining.min(limit)),
                functional_dependencies: relation.functional_dependencies.clone(),
                node: RelationNode::Slice {
                    input: Box::new(relation),
                    offset,
                    limit,
                },
            };
        }
        Ok(relation)
    }

    fn lower_subquery(
        &mut self,
        query: &Query,
        outer_columns: &[ColumnMeta],
    ) -> Result<Relation, UnsupportedReason> {
        const MAX_NESTING_DEPTH: usize = 8;
        if self.outer_scopes.len() >= MAX_NESTING_DEPTH {
            return Err(unsupported(
                UnsupportedKind::ComplexityLimit,
                format!("query nesting exceeds the supported depth of {MAX_NESTING_DEPTH}"),
            ));
        }
        self.outer_scopes.push(outer_columns.to_vec());
        let saved_qualifiers = self.qualifiers.clone();
        let saved_clause_aliases = std::mem::take(&mut self.clause_aliases);
        let saved_allow_window_functions =
            std::mem::replace(&mut self.allow_window_functions, false);
        let lowered = self.lower_query(query);
        self.qualifiers = saved_qualifiers;
        self.clause_aliases = saved_clause_aliases;
        self.allow_window_functions = saved_allow_window_functions;
        self.outer_scopes.pop();
        lowered.map(|(relation, _)| relation)
    }

    fn lower_set_expr(&mut self, expression: &SetExpr) -> Result<Relation, UnsupportedReason> {
        match expression {
            SetExpr::Select(select) => {
                self.qualifiers.clear();
                validate_select_shape(select)?;
                let relation = self.lower_select(select)?;
                if select.distinct.is_some() {
                    Ok(Relation {
                        columns: relation.columns.clone(),
                        max_rows: relation.max_rows,
                        functional_dependencies: relation.functional_dependencies.clone(),
                        node: RelationNode::Distinct {
                            input: Box::new(relation),
                        },
                    })
                } else {
                    Ok(relation)
                }
            }
            SetExpr::Query(query) => self.lower_query(query).map(|(relation, _)| relation),
            SetExpr::SetOperation {
                left,
                op,
                set_quantifier,
                right,
            } => {
                let left = self.lower_set_expr(left)?;
                let right = self.lower_set_expr(right)?;
                if left.columns.len() != right.columns.len()
                    || left
                        .columns
                        .iter()
                        .zip(&right.columns)
                        .any(|(left, right)| left.data_type != right.data_type)
                {
                    return Err(type_error(
                        "set-operation operands need matching column counts and types",
                    ));
                }
                let all = match set_quantifier {
                    SetQuantifier::All => true,
                    SetQuantifier::None | SetQuantifier::Distinct => false,
                    SetQuantifier::ByName
                    | SetQuantifier::AllByName
                    | SetQuantifier::DistinctByName => {
                        return Err(sql_unsupported("set operations BY NAME are unsupported"));
                    }
                };
                let op = match op {
                    SqlSetOperator::Union => SetOp::Union,
                    SqlSetOperator::Intersect => SetOp::Intersect,
                    SqlSetOperator::Except => SetOp::Except,
                    SqlSetOperator::Minus => {
                        return Err(sql_unsupported(
                            "the non-standard MINUS operator is unsupported",
                        ));
                    }
                };
                let max_rows = match op {
                    SetOp::Union => self.checked_sum(left.max_rows, right.max_rows)?,
                    SetOp::Intersect => left.max_rows.min(right.max_rows),
                    SetOp::Except => left.max_rows,
                };
                let functional_dependencies = match op {
                    SetOp::Union => Vec::new(),
                    SetOp::Intersect | SetOp::Except => left.functional_dependencies.clone(),
                };
                let columns = left
                    .columns
                    .iter()
                    .zip(&right.columns)
                    .map(|(column, right_column)| ColumnMeta {
                        qualifier: None,
                        name: column.name.clone(),
                        canonical_name: column.canonical_name.clone(),
                        source_qualifier: None,
                        source_name: None,
                        data_type: column.data_type,
                        nullable: column.nullable || right_column.nullable,
                        unqualified_visible: true,
                        wildcard_visible: true,
                    })
                    .collect();
                Ok(Relation {
                    node: RelationNode::SetOperation {
                        op,
                        all,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    columns,
                    max_rows,
                    functional_dependencies,
                })
            }
            _ => Err(sql_unsupported(
                "VALUES, TABLE, and data-modifying set operands are unsupported",
            )),
        }
    }

    fn lower_select(&mut self, select: &Select) -> Result<Relation, UnsupportedReason> {
        let mut relation = self.lower_from(select)?;
        if let Some(selection) = &select.selection {
            let predicate =
                lower_expr(self, selection, &relation.columns, Some(DataType::Boolean))?;
            let mut functional_dependencies = relation.functional_dependencies.clone();
            add_predicate_functional_dependencies(&predicate, &mut functional_dependencies);
            relation = Relation {
                columns: relation.columns.clone(),
                max_rows: relation.max_rows,
                functional_dependencies,
                node: RelationNode::Filter {
                    input: Box::new(relation),
                    predicate,
                },
            };
        }

        let saved_allow_window_functions = self.allow_window_functions;
        self.allow_window_functions = true;
        let projection = lower_projection(self, &select.projection, &relation.columns);
        self.allow_window_functions = saved_allow_window_functions;
        let (mut expressions, columns) = projection?;
        let group_by = lower_group_by(
            self,
            &select.group_by,
            &expressions,
            &columns,
            &relation.columns,
        )?;
        let clause_aliases = columns
            .iter()
            .zip(&expressions)
            .map(|(column, expression)| (column.canonical_name.clone(), expression.clone()))
            .collect();
        let saved_clause_aliases = std::mem::replace(&mut self.clause_aliases, clause_aliases);
        let having = select
            .having
            .as_ref()
            .map(|having| lower_expr(self, having, &relation.columns, Some(DataType::Boolean)))
            .transpose();
        self.clause_aliases = saved_clause_aliases;
        let having = having?;
        let aggregate_mode = !group_by.is_empty()
            || expressions.iter().any(contains_aggregate)
            || having.as_ref().is_some_and(contains_aggregate);
        if !aggregate_mode && having.is_none() {
            let mut windows = Vec::new();
            for expression in &expressions {
                collect_window_expressions(expression, &mut windows);
            }
            if !windows.is_empty() {
                let base_width = relation.columns.len();
                let mut inner_expressions = relation
                    .columns
                    .iter()
                    .enumerate()
                    .map(|(index, column)| TypedExpr::column(index, column))
                    .collect::<Vec<_>>();
                inner_expressions.extend(windows.iter().cloned());
                let mut inner_columns = relation.columns.clone();
                inner_columns.extend(windows.iter().enumerate().map(|(index, expression)| {
                    let name = format!("__window_{index}");
                    ColumnMeta {
                        qualifier: None,
                        name: name.clone(),
                        canonical_name: name,
                        source_qualifier: None,
                        source_name: None,
                        data_type: expression.data_type,
                        nullable: expression.nullable,
                        unqualified_visible: false,
                        wildcard_visible: false,
                    }
                }));
                for expression in &mut expressions {
                    replace_window_expressions(expression, &windows, &inner_columns, base_width);
                }
                let functional_dependencies = project_functional_dependencies(
                    &relation.functional_dependencies,
                    &inner_expressions,
                );
                relation = Relation {
                    max_rows: relation.max_rows,
                    node: RelationNode::Project {
                        input: Box::new(relation),
                        expressions: inner_expressions,
                    },
                    columns: inner_columns,
                    functional_dependencies,
                };
            }
        }
        let has_windows =
            expressions.iter().any(contains_window) || having.as_ref().is_some_and(contains_window);
        if has_windows && (aggregate_mode || having.is_some()) {
            return Err(sql_unsupported(
                "window functions combined with grouped aggregation or HAVING are unsupported",
            ));
        }
        if aggregate_mode || having.is_some() {
            let mut determined_columns =
                grouped_column_closure(&group_by, &relation.functional_dependencies);
            if self.permissive_grouping {
                determined_columns.extend(0..relation.columns.len());
            }
            for expression in &expressions {
                validate_grouped_expression(expression, &group_by, &determined_columns, false)?;
            }
            if let Some(having) = &having {
                validate_grouped_expression(having, &group_by, &determined_columns, false)?;
            }
            let functional_dependencies =
                aggregate_functional_dependencies(&group_by, &expressions);
            Ok(Relation {
                max_rows: if group_by.is_empty() {
                    1
                } else {
                    relation.max_rows
                },
                node: RelationNode::Aggregate {
                    input: Box::new(relation),
                    group_by,
                    expressions,
                    having,
                },
                columns,
                functional_dependencies,
            })
        } else {
            let functional_dependencies =
                project_functional_dependencies(&relation.functional_dependencies, &expressions);
            Ok(Relation {
                max_rows: relation.max_rows,
                node: RelationNode::Project {
                    input: Box::new(relation),
                    expressions,
                },
                columns,
                functional_dependencies,
            })
        }
    }

    fn lower_from(&mut self, select: &Select) -> Result<Relation, UnsupportedReason> {
        let mut result: Option<Relation> = None;
        for table_with_joins in &select.from {
            let current = self.lower_table_with_joins(table_with_joins)?;

            result = Some(match result {
                None => current,
                Some(left) => {
                    let columns = combined_columns(&left, &current);
                    let max_rows = self.checked_product(left.max_rows, current.max_rows)?;
                    let functional_dependencies = combined_functional_dependencies(&left, &current);
                    Relation {
                        node: RelationNode::Product {
                            left: Box::new(left),
                            right: Box::new(current),
                        },
                        columns,
                        max_rows,
                        functional_dependencies,
                    }
                }
            });
        }
        Ok(result.unwrap_or(Relation {
            node: RelationNode::Unit,
            columns: Vec::new(),
            max_rows: 1,
            functional_dependencies: vec![FunctionalDependency {
                determinants: Vec::new(),
                dependents: Vec::new(),
            }],
        }))
    }

    fn lower_table_with_joins(
        &mut self,
        table_with_joins: &sqlparser::ast::TableWithJoins,
    ) -> Result<Relation, UnsupportedReason> {
        let mut current = self.lower_table_factor(&table_with_joins.relation)?;
        for join in &table_with_joins.joins {
            if join.global {
                return Err(sql_unsupported("GLOBAL joins are unsupported"));
            }
            let right = self.lower_table_factor(&join.relation)?;
            current = match &join.join_operator {
                JoinOperator::CrossJoin(JoinConstraint::None) => {
                    let functional_dependencies =
                        combined_functional_dependencies(&current, &right);
                    Relation {
                        max_rows: self.checked_product(current.max_rows, right.max_rows)?,
                        columns: combined_columns(&current, &right),
                        node: RelationNode::Product {
                            left: Box::new(current),
                            right: Box::new(right),
                        },
                        functional_dependencies,
                    }
                }
                JoinOperator::Join(constraint) | JoinOperator::Inner(constraint) => {
                    self.lower_join(current, right, JoinKind::Inner, constraint)?
                }
                JoinOperator::Left(constraint) | JoinOperator::LeftOuter(constraint) => {
                    self.lower_join(current, right, JoinKind::Left, constraint)?
                }
                JoinOperator::Right(constraint) | JoinOperator::RightOuter(constraint) => {
                    self.lower_join(current, right, JoinKind::Right, constraint)?
                }
                JoinOperator::FullOuter(constraint) => {
                    self.lower_join(current, right, JoinKind::Full, constraint)?
                }
                JoinOperator::CrossJoin(_) => {
                    return Err(sql_unsupported("CROSS JOIN cannot have a join constraint"));
                }
                _ => {
                    return Err(sql_unsupported(
                        "semi, anti, ASOF, APPLY, and array joins are unsupported",
                    ));
                }
            };
        }
        Ok(current)
    }

    fn lower_join(
        &mut self,
        left: Relation,
        right: Relation,
        kind: JoinKind,
        constraint: &JoinConstraint,
    ) -> Result<Relation, UnsupportedReason> {
        let base_columns = nullable_join_columns(&left, &right, kind);
        let (on, using_pairs) = match constraint {
            JoinConstraint::On(condition) => (
                lower_expr(self, condition, &base_columns, Some(DataType::Boolean))?,
                None,
            ),
            JoinConstraint::Using(names) => {
                let pairs = explicit_using_pairs(names, &left.columns, &right.columns)?;
                (
                    using_predicate(&base_columns, left.columns.len(), &pairs)?,
                    Some(pairs),
                )
            }
            JoinConstraint::Natural => {
                let pairs = natural_join_pairs(&left.columns, &right.columns)?;
                (
                    using_predicate(&base_columns, left.columns.len(), &pairs)?,
                    Some(pairs),
                )
            }
            JoinConstraint::None if kind == JoinKind::Inner => (
                TypedExpr::literal(Value::Boolean(true), DataType::Boolean, false),
                None,
            ),
            JoinConstraint::None => {
                return Err(sql_unsupported("outer joins require ON, USING, or NATURAL"));
            }
        };
        let product_rows = self.checked_product(left.max_rows, right.max_rows)?;
        let max_rows = match kind {
            JoinKind::Inner => product_rows,
            JoinKind::Left => self.checked_sum(product_rows, left.max_rows)?,
            JoinKind::Right => self.checked_sum(product_rows, right.max_rows)?,
            JoinKind::Full => self.checked_sum(
                self.checked_sum(product_rows, left.max_rows)?,
                right.max_rows,
            )?,
        };
        let left_columns = left.columns.clone();
        let mut functional_dependencies = combined_functional_dependencies(&left, &right);
        if kind == JoinKind::Inner {
            add_predicate_functional_dependencies(&on, &mut functional_dependencies);
        }
        let joined = Relation {
            node: RelationNode::Join {
                kind,
                left: Box::new(left),
                right: Box::new(right),
                on,
            },
            columns: base_columns,
            max_rows,
            functional_dependencies,
        };
        match using_pairs {
            Some(pairs) => Ok(project_using_join(joined, &left_columns, &pairs, kind)),
            None => Ok(joined),
        }
    }

    fn lower_table_factor(&mut self, factor: &TableFactor) -> Result<Relation, UnsupportedReason> {
        if let TableFactor::NestedJoin {
            table_with_joins,
            alias,
        } = factor
        {
            let saved_qualifiers = self.qualifiers.clone();
            let mut relation = self.lower_table_with_joins(table_with_joins)?;
            if let Some(alias) = alias {
                self.qualifiers = saved_qualifiers;
                if alias.at.is_some() {
                    return Err(sql_unsupported("AT aliases are unsupported"));
                }
                let qualifier = identifier(&alias.name, "nested-join alias")?;
                if !self.qualifiers.insert(qualifier.clone()) {
                    return Err(unsupported(
                        UnsupportedKind::NameResolution,
                        format!("duplicate table name or alias `{qualifier}`"),
                    ));
                }
                apply_column_aliases(&mut relation, &alias.columns)?;
                for column in &mut relation.columns {
                    column.qualifier = Some(qualifier.clone());
                    column.source_qualifier = None;
                    column.source_name = None;
                }
            }
            return Ok(relation);
        }

        if let TableFactor::Derived {
            lateral,
            subquery,
            alias,
            sample,
        } = factor
        {
            if *lateral {
                return Err(sql_unsupported(
                    "LATERAL derived tables are not supported; use correlated scalar/EXISTS subqueries",
                ));
            }
            if sample.is_some() {
                return Err(sql_unsupported("samples on derived tables are unsupported"));
            }
            let saved_qualifiers = self.qualifiers.clone();
            let lowered = self.lower_query(subquery);
            self.qualifiers = saved_qualifiers;
            let (mut relation, _) = lowered?;
            let alias = alias
                .as_ref()
                .ok_or_else(|| sql_unsupported("derived tables require an alias"))?;
            let qualifier = identifier(&alias.name, "derived-table alias")?;
            if alias.at.is_some() {
                return Err(sql_unsupported("AT aliases are unsupported"));
            }
            if !self.qualifiers.insert(qualifier.clone()) {
                return Err(unsupported(
                    UnsupportedKind::NameResolution,
                    format!("duplicate table name or alias `{qualifier}`"),
                ));
            }
            apply_column_aliases(&mut relation, &alias.columns)?;
            for column in &mut relation.columns {
                column.qualifier = Some(qualifier.clone());
                column.source_qualifier = None;
                column.source_name = None;
            }
            return Ok(relation);
        }

        let TableFactor::Table {
            name,
            alias,
            args,
            with_hints,
            version,
            with_ordinality,
            partitions,
            json_path,
            sample,
            index_hints,
        } = factor
        else {
            return Err(sql_unsupported(
                "table functions, UNNEST, pivots, and dialect-specific table factors are unsupported",
            ));
        };
        if args.is_some()
            || !with_hints.is_empty()
            || version.is_some()
            || *with_ordinality
            || !partitions.is_empty()
            || json_path.is_some()
            || sample.is_some()
            || !index_hints.is_empty()
        {
            return Err(sql_unsupported(
                "table arguments, hints, versions, partitions, JSON paths, samples, and indexes are unsupported",
            ));
        }

        let table_name = single_object_name(name, "table")?;
        let qualifier = match alias {
            Some(alias) => {
                if alias.at.is_some() {
                    return Err(sql_unsupported("AT aliases are unsupported"));
                }
                identifier(&alias.name, "table alias")?
            }
            None => canonical_name(&table_name),
        };
        if !self.qualifiers.insert(qualifier.clone()) {
            return Err(unsupported(
                UnsupportedKind::NameResolution,
                format!("duplicate table name or alias `{qualifier}`"),
            ));
        }
        if let Some(mut relation) = self.ctes.get(&canonical_name(&table_name)).cloned() {
            if let Some(alias) = alias {
                apply_column_aliases(&mut relation, &alias.columns)?;
            }
            for column in &mut relation.columns {
                column.qualifier = Some(qualifier.clone());
                column.source_qualifier = None;
                column.source_name = None;
            }
            return Ok(relation);
        }
        let table_index = self.schema.table_index(&table_name).ok_or_else(|| {
            unsupported(
                UnsupportedKind::NameResolution,
                format!("unknown table or CTE `{table_name}`"),
            )
        })?;
        let table = &self.schema.tables[table_index];
        let mut columns = table
            .columns
            .iter()
            .map(|column| ColumnMeta {
                qualifier: Some(qualifier.clone()),
                name: column.name.clone(),
                canonical_name: canonical_name(&column.name),
                source_qualifier: None,
                source_name: None,
                data_type: column.data_type,
                nullable: column.nullable,
                unqualified_visible: true,
                wildcard_visible: true,
            })
            .collect::<Vec<_>>();
        if let Some(alias) = alias {
            apply_column_metadata_aliases(&mut columns, &alias.columns)?;
        }
        Ok(Relation {
            node: RelationNode::Scan { table_index },
            columns,
            max_rows: self.bound,
            functional_dependencies: self.base_functional_dependencies(table_index),
        })
    }

    fn base_functional_dependencies(&self, table_index: usize) -> Vec<FunctionalDependency> {
        let table = &self.schema.tables[table_index];
        let all_columns = (0..table.columns.len()).collect::<Vec<_>>();
        let mut dependencies = Vec::new();
        if let Some(primary_key) = &table.primary_key {
            let determinants = primary_key
                .iter()
                .filter_map(|name| {
                    let name = canonical_name(name);
                    table
                        .columns
                        .iter()
                        .position(|column| canonical_name(&column.name) == name)
                })
                .collect::<Vec<_>>();
            if determinants.len() == primary_key.len() {
                push_functional_dependency(&mut dependencies, determinants, all_columns.clone());
            }
        }
        for constraint in &self.schema.constraints {
            let (columns, require_not_null) = match constraint {
                IntegrityConstraint::PrimaryKey { columns } => (columns, false),
                IntegrityConstraint::Unique { columns } => (columns, true),
                _ => continue,
            };
            let resolved = columns
                .iter()
                .map(|column| self.schema.resolve_column(column))
                .collect::<Result<Vec<_>, _>>();
            let Ok(resolved) = resolved else {
                continue;
            };
            if resolved.iter().any(|(table, _, _)| *table != table_index)
                || (require_not_null && resolved.iter().any(|(_, _, column)| column.nullable))
            {
                continue;
            }
            push_functional_dependency(
                &mut dependencies,
                resolved
                    .into_iter()
                    .map(|(_, column_index, _)| column_index)
                    .collect(),
                all_columns.clone(),
            );
        }
        dependencies
    }

    fn checked_product(&self, left: usize, right: usize) -> Result<usize, UnsupportedReason> {
        let rows = left.checked_mul(right);
        if rows.is_none_or(|rows| rows > self.max_intermediate_rows) {
            return Err(unsupported(
                UnsupportedKind::ComplexityLimit,
                format!(
                    "an intermediate relation exceeds the configured {}-row symbolic limit",
                    self.max_intermediate_rows
                ),
            ));
        }
        Ok(rows.expect("the checked value is present after the limit test"))
    }

    fn checked_sum(&self, left: usize, right: usize) -> Result<usize, UnsupportedReason> {
        let rows = left.checked_add(right);
        if rows.is_none_or(|rows| rows > self.max_intermediate_rows) {
            return Err(unsupported(
                UnsupportedKind::ComplexityLimit,
                format!(
                    "an intermediate relation exceeds the configured {}-row symbolic limit",
                    self.max_intermediate_rows
                ),
            ));
        }
        Ok(rows.expect("the checked value is present after the limit test"))
    }
}

fn validate_query_clauses(query: &Query) -> Result<(), UnsupportedReason> {
    if query.fetch.is_some()
        || !query.locks.is_empty()
        || query.for_clause.is_some()
        || query.settings.is_some()
        || query.format_clause.is_some()
        || !query.pipe_operators.is_empty()
    {
        return Err(sql_unsupported(
            "FETCH, locking, and dialect-specific query clauses are unsupported",
        ));
    }
    Ok(())
}

fn apply_column_aliases(
    relation: &mut Relation,
    aliases: &[sqlparser::ast::TableAliasColumnDef],
) -> Result<(), UnsupportedReason> {
    apply_column_metadata_aliases(&mut relation.columns, aliases)
}

fn apply_column_metadata_aliases(
    columns: &mut [ColumnMeta],
    aliases: &[sqlparser::ast::TableAliasColumnDef],
) -> Result<(), UnsupportedReason> {
    if aliases.is_empty() {
        return Ok(());
    }
    if aliases.len() != columns.len() {
        return Err(type_error(format!(
            "table alias declares {} columns for a {}-column relation",
            aliases.len(),
            columns.len()
        )));
    }
    for (column, alias) in columns.iter_mut().zip(aliases) {
        if alias.data_type.is_some() {
            return Err(sql_unsupported("typed table-alias columns are unsupported"));
        }
        column.name = display_identifier(&alias.name, "table column alias")?;
        column.canonical_name = canonical_name(&column.name);
        column.source_qualifier = None;
        column.source_name = None;
    }
    Ok(())
}

fn validate_select_shape(select: &Select) -> Result<(), UnsupportedReason> {
    if select.top.is_some()
        || select.top_before_distinct
        || select.exclude.is_some()
        || select.into.is_some()
        || !select.lateral_views.is_empty()
        || select.prewhere.is_some()
        || !select.connect_by.is_empty()
        || !select.cluster_by.is_empty()
        || !select.distribute_by.is_empty()
        || !select.sort_by.is_empty()
        || !select.named_window.is_empty()
        || select.qualify.is_some()
        || select.window_before_qualify
        || select.value_table_mode.is_some()
    {
        return Err(sql_unsupported(
            "dialect-specific SELECT modifiers and window clauses are unsupported",
        ));
    }
    Ok(())
}

fn combined_columns(left: &Relation, right: &Relation) -> Vec<ColumnMeta> {
    left.columns.iter().chain(&right.columns).cloned().collect()
}

fn combined_functional_dependencies(
    left: &Relation,
    right: &Relation,
) -> Vec<FunctionalDependency> {
    let mut dependencies = left.functional_dependencies.clone();
    let offset = left.columns.len();
    for dependency in &right.functional_dependencies {
        push_functional_dependency(
            &mut dependencies,
            dependency
                .determinants
                .iter()
                .map(|index| offset + index)
                .collect(),
            dependency
                .dependents
                .iter()
                .map(|index| offset + index)
                .collect(),
        );
    }
    dependencies
}

fn project_functional_dependencies(
    input_dependencies: &[FunctionalDependency],
    expressions: &[TypedExpr],
) -> Vec<FunctionalDependency> {
    let mut projected = Vec::new();
    let constant_outputs = expressions
        .iter()
        .enumerate()
        .filter_map(|(index, expression)| {
            local_column_dependencies(expression)
                .is_empty()
                .then_some(index)
        })
        .collect::<Vec<_>>();
    if !constant_outputs.is_empty() {
        push_functional_dependency(&mut projected, Vec::new(), constant_outputs);
    }

    for dependency in input_dependencies {
        let determinants = dependency
            .determinants
            .iter()
            .map(|source_index| {
                expressions.iter().position(
                    |expression| matches!(expression.kind, ExprKind::Column(index) if index == *source_index),
                )
            })
            .collect::<Option<Vec<_>>>();
        let Some(determinants) = determinants else {
            continue;
        };
        let closure = functional_dependency_closure(
            dependency.determinants.iter().copied(),
            input_dependencies,
        );
        let dependents = expressions
            .iter()
            .enumerate()
            .filter_map(|(index, expression)| {
                local_column_dependencies(expression)
                    .iter()
                    .all(|column| closure.contains(column))
                    .then_some(index)
            })
            .collect::<Vec<_>>();
        push_functional_dependency(&mut projected, determinants, dependents);
    }
    for (rank_index, expression) in expressions.iter().enumerate() {
        let ExprKind::WindowRank {
            function: WindowRankFunction::DenseRank | WindowRankFunction::Rank,
            partition_by,
            order_by,
        } = &expression.kind
        else {
            continue;
        };
        let partition_outputs = partition_by
            .iter()
            .filter(|partition| !local_column_dependencies(partition).is_empty())
            .map(|partition| expressions.iter().position(|output| output == partition))
            .collect::<Option<Vec<_>>>();
        let order_outputs = order_by
            .iter()
            .map(|key| {
                expressions
                    .iter()
                    .position(|output| output == &key.expression)
            })
            .collect::<Option<Vec<_>>>();
        let (Some(partition_outputs), Some(order_outputs)) = (partition_outputs, order_outputs)
        else {
            continue;
        };
        let mut rank_determinants = partition_outputs.clone();
        rank_determinants.push(rank_index);
        push_functional_dependency(&mut projected, rank_determinants, order_outputs.clone());
        let mut order_determinants = partition_outputs;
        order_determinants.extend(order_outputs);
        push_functional_dependency(&mut projected, order_determinants, vec![rank_index]);
    }
    for (window_index, expression) in expressions.iter().enumerate() {
        let (partition_by, order_by, partition_determines) = match &expression.kind {
            ExprKind::FirstValue {
                partition_by,
                order_by,
                ..
            } => (partition_by, order_by, true),
            ExprKind::WindowAggregate {
                function,
                expression,
                partition_by,
                order_by,
                ..
            } => {
                let extremum_follows_order = expression.as_deref().is_some_and(|argument| {
                    order_by.first().is_some_and(|key| {
                        argument == &key.expression
                            && ((*function == AggregateFunction::Min && key.ascending)
                                || (*function == AggregateFunction::Max && !key.ascending))
                    })
                });
                (
                    partition_by,
                    order_by,
                    order_by.is_empty() || extremum_follows_order,
                )
            }
            _ => continue,
        };
        let partition_outputs = partition_by
            .iter()
            .filter(|partition| !local_column_dependencies(partition).is_empty())
            .map(|partition| expressions.iter().position(|output| output == partition))
            .collect::<Option<Vec<_>>>();
        let Some(mut determinants) = partition_outputs else {
            continue;
        };
        if !partition_determines {
            let order_outputs = order_by
                .iter()
                .map(|key| {
                    expressions
                        .iter()
                        .position(|output| output == &key.expression)
                })
                .collect::<Option<Vec<_>>>();
            let Some(order_outputs) = order_outputs else {
                continue;
            };
            determinants.extend(order_outputs);
        }
        push_functional_dependency(&mut projected, determinants, vec![window_index]);
    }
    projected
}

fn aggregate_functional_dependencies(
    group_by: &[TypedExpr],
    expressions: &[TypedExpr],
) -> Vec<FunctionalDependency> {
    let determinants = group_by
        .iter()
        .map(|group_expression| {
            expressions
                .iter()
                .position(|expression| expression == group_expression)
        })
        .collect::<Option<Vec<_>>>();
    determinants.map_or_else(Vec::new, |determinants| {
        vec![FunctionalDependency {
            determinants,
            dependents: (0..expressions.len()).collect(),
        }]
    })
}

fn grouped_column_closure(
    group_by: &[TypedExpr],
    dependencies: &[FunctionalDependency],
) -> HashSet<usize> {
    functional_dependency_closure(
        group_by.iter().filter_map(|expression| {
            if let ExprKind::Column(index) = expression.kind {
                Some(index)
            } else {
                None
            }
        }),
        dependencies,
    )
}

fn functional_dependency_closure(
    initial: impl IntoIterator<Item = usize>,
    dependencies: &[FunctionalDependency],
) -> HashSet<usize> {
    let mut closure = initial.into_iter().collect::<HashSet<_>>();
    loop {
        let previous_len = closure.len();
        for dependency in dependencies {
            if dependency
                .determinants
                .iter()
                .all(|column| closure.contains(column))
            {
                closure.extend(dependency.dependents.iter().copied());
            }
        }
        if closure.len() == previous_len {
            return closure;
        }
    }
}

fn push_functional_dependency(
    dependencies: &mut Vec<FunctionalDependency>,
    mut determinants: Vec<usize>,
    mut dependents: Vec<usize>,
) {
    determinants.sort_unstable();
    determinants.dedup();
    dependents.sort_unstable();
    dependents.dedup();
    let dependency = FunctionalDependency {
        determinants,
        dependents,
    };
    if !dependencies.contains(&dependency) {
        dependencies.push(dependency);
    }
}

fn add_predicate_functional_dependencies(
    predicate: &TypedExpr,
    dependencies: &mut Vec<FunctionalDependency>,
) {
    match &predicate.kind {
        ExprKind::And(left, right) => {
            add_predicate_functional_dependencies(left, dependencies);
            add_predicate_functional_dependencies(right, dependencies);
        }
        ExprKind::Compare {
            op: CompareOp::Equal,
            left,
            right,
        } => match (&left.kind, &right.kind) {
            (ExprKind::Column(left), ExprKind::Column(right)) => {
                push_functional_dependency(dependencies, vec![*left], vec![*right]);
                push_functional_dependency(dependencies, vec![*right], vec![*left]);
            }
            (ExprKind::Column(column), ExprKind::Literal(_))
            | (ExprKind::Literal(_), ExprKind::Column(column)) => {
                push_functional_dependency(dependencies, Vec::new(), vec![*column]);
            }
            _ => {}
        },
        _ => {}
    }
}

fn local_column_dependencies(expression: &TypedExpr) -> HashSet<usize> {
    fn collect(expression: &TypedExpr, columns: &mut HashSet<usize>) {
        match &expression.kind {
            ExprKind::Column(index) => {
                columns.insert(*index);
            }
            ExprKind::OuterColumn { .. }
            | ExprKind::Literal(_)
            | ExprKind::Exists { .. }
            | ExprKind::ScalarSubquery { .. } => {}
            ExprKind::WindowRank {
                partition_by,
                order_by,
                ..
            } => {
                for expression in partition_by {
                    collect(expression, columns);
                }
                for key in order_by {
                    collect(&key.expression, columns);
                }
            }
            ExprKind::WindowAggregate {
                expression,
                partition_by,
                order_by,
                ..
            } => {
                if let Some(expression) = expression {
                    collect(expression, columns);
                }
                for expression in partition_by {
                    collect(expression, columns);
                }
                for key in order_by {
                    collect(&key.expression, columns);
                }
            }
            ExprKind::FirstValue {
                expression,
                partition_by,
                order_by,
            } => {
                collect(expression, columns);
                for expression in partition_by {
                    collect(expression, columns);
                }
                for key in order_by {
                    collect(&key.expression, columns);
                }
            }
            ExprKind::InSubquery { expressions, .. } => {
                for expression in expressions {
                    collect(expression, columns);
                }
            }
            ExprKind::Compare { left, right, .. }
            | ExprKind::Arithmetic { left, right, .. }
            | ExprKind::And(left, right)
            | ExprKind::Or(left, right) => {
                collect(left, columns);
                collect(right, columns);
            }
            ExprKind::Not(inner)
            | ExprKind::IsNull(inner)
            | ExprKind::IsNotNull(inner)
            | ExprKind::Negate(inner)
            | ExprKind::Cast {
                expression: inner, ..
            } => collect(inner, columns),
            ExprKind::Coalesce(expressions)
            | ExprKind::CountDistinctRow { expressions }
            | ExprKind::ScalarFunction {
                arguments: expressions,
                ..
            } => {
                for expression in expressions {
                    collect(expression, columns);
                }
            }
            ExprKind::Case {
                branches,
                else_result,
            } => {
                for (condition, result) in branches {
                    collect(condition, columns);
                    collect(result, columns);
                }
                collect(else_result, columns);
            }
            ExprKind::Aggregate {
                expression: Some(expression),
                ..
            } => collect(expression, columns),
            ExprKind::Aggregate {
                expression: None, ..
            } => {}
        }
    }

    let mut columns = HashSet::new();
    collect(expression, &mut columns);
    columns
}

fn nullable_join_columns(left: &Relation, right: &Relation, kind: JoinKind) -> Vec<ColumnMeta> {
    let null_left = matches!(kind, JoinKind::Right | JoinKind::Full);
    let null_right = matches!(kind, JoinKind::Left | JoinKind::Full);
    left.columns
        .iter()
        .map(|column| {
            let mut column = column.clone();
            column.nullable |= null_left;
            column
        })
        .chain(right.columns.iter().map(|column| {
            let mut column = column.clone();
            column.nullable |= null_right;
            column
        }))
        .collect()
}

fn explicit_using_pairs(
    names: &[ObjectName],
    left: &[ColumnMeta],
    right: &[ColumnMeta],
) -> Result<Vec<(usize, usize)>, UnsupportedReason> {
    let mut seen = HashSet::new();
    names
        .iter()
        .map(|name| {
            let name = canonical_name(&single_object_name(name, "USING column")?);
            if !seen.insert(name.clone()) {
                return Err(sql_unsupported(format!("USING repeats column `{name}`")));
            }
            Ok((
                visible_column_index(left, &name)?,
                visible_column_index(right, &name)?,
            ))
        })
        .collect()
}

fn natural_join_pairs(
    left: &[ColumnMeta],
    right: &[ColumnMeta],
) -> Result<Vec<(usize, usize)>, UnsupportedReason> {
    let mut pairs = Vec::new();
    let mut seen = HashSet::new();
    for (left_index, column) in left.iter().enumerate() {
        if !column.unqualified_visible || !seen.insert(column.canonical_name.clone()) {
            continue;
        }
        let matches = right
            .iter()
            .enumerate()
            .filter(|(_, right)| {
                right.unqualified_visible && right.canonical_name == column.canonical_name
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => {}
            [right_index] => pairs.push((left_index, *right_index)),
            _ => {
                return Err(unsupported(
                    UnsupportedKind::NameResolution,
                    format!(
                        "NATURAL JOIN finds ambiguous right column `{}`",
                        column.name
                    ),
                ));
            }
        }
    }
    Ok(pairs)
}

fn visible_column_index(columns: &[ColumnMeta], name: &str) -> Result<usize, UnsupportedReason> {
    let matches = columns
        .iter()
        .enumerate()
        .filter(|(_, column)| column.unqualified_visible && column.canonical_name == name)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(unsupported(
            UnsupportedKind::NameResolution,
            format!("USING references unknown column `{name}`"),
        )),
        _ => Err(unsupported(
            UnsupportedKind::NameResolution,
            format!("USING references ambiguous column `{name}`"),
        )),
    }
}

fn using_predicate(
    columns: &[ColumnMeta],
    left_width: usize,
    pairs: &[(usize, usize)],
) -> Result<TypedExpr, UnsupportedReason> {
    let mut predicates = Vec::with_capacity(pairs.len());
    for (left_index, right_index) in pairs {
        let right_index = left_width + right_index;
        let left = &columns[*left_index];
        let right = &columns[right_index];
        if left.data_type != right.data_type {
            return Err(type_error(format!(
                "USING column `{}` has different types on each side",
                left.name
            )));
        }
        predicates.push(TypedExpr {
            data_type: DataType::Boolean,
            nullable: left.nullable || right.nullable,
            kind: ExprKind::Compare {
                op: CompareOp::Equal,
                left: Box::new(TypedExpr::column(*left_index, left)),
                right: Box::new(TypedExpr::column(right_index, right)),
            },
        });
    }
    Ok(predicates
        .into_iter()
        .reduce(|left, right| TypedExpr {
            data_type: DataType::Boolean,
            nullable: left.nullable || right.nullable,
            kind: ExprKind::And(Box::new(left), Box::new(right)),
        })
        .unwrap_or_else(|| TypedExpr::literal(Value::Boolean(true), DataType::Boolean, false)))
}

fn project_using_join(
    joined: Relation,
    left_columns: &[ColumnMeta],
    pairs: &[(usize, usize)],
    kind: JoinKind,
) -> Relation {
    let left_width = left_columns.len();
    let mut expressions = Vec::new();
    let mut columns = Vec::new();
    let left_keys = pairs.iter().map(|(left, _)| *left).collect::<HashSet<_>>();
    let right_keys = pairs
        .iter()
        .map(|(_, right)| *right)
        .collect::<HashSet<_>>();

    for (left_index, right_index) in pairs {
        let right_index = left_width + right_index;
        let left = &joined.columns[*left_index];
        let right = &joined.columns[right_index];
        let expression = match kind {
            JoinKind::Inner | JoinKind::Left => TypedExpr::column(*left_index, left),
            JoinKind::Right => TypedExpr::column(right_index, right),
            JoinKind::Full => TypedExpr {
                data_type: left.data_type,
                nullable: left.nullable || right.nullable,
                kind: ExprKind::Coalesce(vec![
                    TypedExpr::column(*left_index, left),
                    TypedExpr::column(right_index, right),
                ]),
            },
        };
        columns.push(ColumnMeta {
            qualifier: None,
            name: left.name.clone(),
            canonical_name: left.canonical_name.clone(),
            source_qualifier: None,
            source_name: None,
            data_type: left.data_type,
            nullable: expression.nullable,
            unqualified_visible: true,
            wildcard_visible: true,
        });
        expressions.push(expression);
    }
    for (index, column) in joined.columns.iter().take(left_width).enumerate() {
        if !left_keys.contains(&index) {
            expressions.push(TypedExpr::column(index, column));
            columns.push(column.clone());
        }
    }
    for (right_index, column) in joined.columns.iter().skip(left_width).enumerate() {
        if !right_keys.contains(&right_index) {
            expressions.push(TypedExpr::column(left_width + right_index, column));
            columns.push(column.clone());
        }
    }
    for (left_index, right_index) in pairs {
        for index in [*left_index, left_width + right_index] {
            let column = &joined.columns[index];
            let mut hidden = column.clone();
            hidden.unqualified_visible = false;
            hidden.wildcard_visible = false;
            expressions.push(TypedExpr::column(index, column));
            columns.push(hidden);
        }
    }
    let functional_dependencies =
        project_functional_dependencies(&joined.functional_dependencies, &expressions);
    Relation {
        max_rows: joined.max_rows,
        node: RelationNode::Project {
            input: Box::new(joined),
            expressions,
        },
        columns,
        functional_dependencies,
    }
}

fn lower_group_by(
    lowerer: &mut Lowerer<'_>,
    group_by: &GroupByExpr,
    projection: &[TypedExpr],
    projection_columns: &[ColumnMeta],
    input_columns: &[ColumnMeta],
) -> Result<Vec<TypedExpr>, UnsupportedReason> {
    let GroupByExpr::Expressions(expressions, modifiers) = group_by else {
        return Err(sql_unsupported("GROUP BY ALL is unsupported"));
    };
    if !modifiers.is_empty() {
        return Err(sql_unsupported("GROUP BY modifiers are unsupported"));
    }
    expressions
        .iter()
        .map(|expression| {
            if let SqlExpr::Value(value) = expression
                && let SqlValue::Number(position, _) = &value.value
                && !position.contains('.')
            {
                let position = position
                    .parse::<usize>()
                    .map_err(|_| type_error("GROUP BY position is outside usize"))?;
                return projection
                    .get(position.wrapping_sub(1))
                    .cloned()
                    .ok_or_else(|| type_error(format!("GROUP BY position {position} is invalid")));
            }
            if let SqlExpr::Identifier(ident) = expression {
                if let Some((index, column)) = resolve_column_in_scope(expression, input_columns)? {
                    return Ok(TypedExpr::column(index, column));
                }
                let name = identifier(ident, "GROUP BY alias")?;
                let matches = projection_columns
                    .iter()
                    .enumerate()
                    .filter(|(_, column)| column.canonical_name == name)
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>();
                if let [index] = matches.as_slice() {
                    return Ok(projection[*index].clone());
                }
            }
            lower_expr(lowerer, expression, input_columns, None)
        })
        .collect()
}

fn contains_aggregate(expression: &TypedExpr) -> bool {
    match &expression.kind {
        ExprKind::Aggregate { .. } | ExprKind::CountDistinctRow { .. } => true,
        ExprKind::Column(_)
        | ExprKind::OuterColumn { .. }
        | ExprKind::Literal(_)
        | ExprKind::Exists { .. }
        | ExprKind::ScalarSubquery { .. } => false,
        ExprKind::WindowRank {
            partition_by,
            order_by,
            ..
        } => {
            partition_by.iter().any(contains_aggregate)
                || order_by
                    .iter()
                    .any(|key| contains_aggregate(&key.expression))
        }
        ExprKind::WindowAggregate {
            expression,
            partition_by,
            order_by,
            ..
        } => {
            expression.as_deref().is_some_and(contains_aggregate)
                || partition_by.iter().any(contains_aggregate)
                || order_by
                    .iter()
                    .any(|key| contains_aggregate(&key.expression))
        }
        ExprKind::FirstValue {
            expression,
            partition_by,
            order_by,
        } => {
            contains_aggregate(expression)
                || partition_by.iter().any(contains_aggregate)
                || order_by
                    .iter()
                    .any(|key| contains_aggregate(&key.expression))
        }
        ExprKind::InSubquery { expressions, .. } => expressions.iter().any(contains_aggregate),
        ExprKind::Compare { left, right, .. } | ExprKind::Arithmetic { left, right, .. } => {
            contains_aggregate(left) || contains_aggregate(right)
        }
        ExprKind::And(left, right) | ExprKind::Or(left, right) => {
            contains_aggregate(left) || contains_aggregate(right)
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => contains_aggregate(inner),
        ExprKind::Coalesce(expressions)
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        } => expressions.iter().any(contains_aggregate),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            branches.iter().any(|(condition, result)| {
                contains_aggregate(condition) || contains_aggregate(result)
            }) || contains_aggregate(else_result)
        }
    }
}

fn collect_window_expressions(expression: &TypedExpr, windows: &mut Vec<TypedExpr>) {
    if matches!(
        expression.kind,
        ExprKind::WindowRank { .. }
            | ExprKind::WindowAggregate { .. }
            | ExprKind::FirstValue { .. }
    ) {
        if !windows.contains(expression) {
            windows.push(expression.clone());
        }
        return;
    }
    match &expression.kind {
        ExprKind::Column(_)
        | ExprKind::OuterColumn { .. }
        | ExprKind::Literal(_)
        | ExprKind::Exists { .. }
        | ExprKind::ScalarSubquery { .. } => {}
        ExprKind::InSubquery { expressions, .. }
        | ExprKind::Coalesce(expressions)
        | ExprKind::CountDistinctRow { expressions }
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        } => {
            for expression in expressions {
                collect_window_expressions(expression, windows);
            }
        }
        ExprKind::Compare { left, right, .. }
        | ExprKind::Arithmetic { left, right, .. }
        | ExprKind::And(left, right)
        | ExprKind::Or(left, right) => {
            collect_window_expressions(left, windows);
            collect_window_expressions(right, windows);
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => collect_window_expressions(inner, windows),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            for (condition, result) in branches {
                collect_window_expressions(condition, windows);
                collect_window_expressions(result, windows);
            }
            collect_window_expressions(else_result, windows);
        }
        ExprKind::Aggregate {
            expression: Some(expression),
            ..
        } => collect_window_expressions(expression, windows),
        ExprKind::Aggregate {
            expression: None, ..
        } => {}
        ExprKind::WindowRank { .. }
        | ExprKind::WindowAggregate { .. }
        | ExprKind::FirstValue { .. } => unreachable!("window roots return above"),
    }
}

fn replace_window_expressions(
    expression: &mut TypedExpr,
    windows: &[TypedExpr],
    columns: &[ColumnMeta],
    base_width: usize,
) {
    if matches!(
        expression.kind,
        ExprKind::WindowRank { .. }
            | ExprKind::WindowAggregate { .. }
            | ExprKind::FirstValue { .. }
    ) {
        let index = windows
            .iter()
            .position(|window| window == expression)
            .expect("collected window expression must be present");
        *expression = TypedExpr::column(base_width + index, &columns[base_width + index]);
        return;
    }
    let replace = |expression: &mut TypedExpr| {
        replace_window_expressions(expression, windows, columns, base_width);
    };
    match &mut expression.kind {
        ExprKind::Column(_)
        | ExprKind::OuterColumn { .. }
        | ExprKind::Literal(_)
        | ExprKind::Exists { .. }
        | ExprKind::ScalarSubquery { .. } => {}
        ExprKind::InSubquery { expressions, .. }
        | ExprKind::Coalesce(expressions)
        | ExprKind::CountDistinctRow { expressions }
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        } => {
            for expression in expressions {
                replace(expression);
            }
        }
        ExprKind::Compare { left, right, .. }
        | ExprKind::Arithmetic { left, right, .. }
        | ExprKind::And(left, right)
        | ExprKind::Or(left, right) => {
            replace(left);
            replace(right);
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => replace(inner),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            for (condition, result) in branches {
                replace(condition);
                replace(result);
            }
            replace(else_result);
        }
        ExprKind::Aggregate {
            expression: Some(expression),
            ..
        } => replace(expression),
        ExprKind::Aggregate {
            expression: None, ..
        } => {}
        ExprKind::WindowRank { .. }
        | ExprKind::WindowAggregate { .. }
        | ExprKind::FirstValue { .. } => unreachable!("window roots return above"),
    }
}

fn contains_window(expression: &TypedExpr) -> bool {
    match &expression.kind {
        ExprKind::WindowRank { .. }
        | ExprKind::WindowAggregate { .. }
        | ExprKind::FirstValue { .. } => true,
        ExprKind::Column(_)
        | ExprKind::OuterColumn { .. }
        | ExprKind::Literal(_)
        | ExprKind::Exists { .. }
        | ExprKind::ScalarSubquery { .. } => false,
        ExprKind::InSubquery { expressions, .. }
        | ExprKind::Coalesce(expressions)
        | ExprKind::CountDistinctRow { expressions }
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        } => expressions.iter().any(contains_window),
        ExprKind::Compare { left, right, .. }
        | ExprKind::Arithmetic { left, right, .. }
        | ExprKind::And(left, right)
        | ExprKind::Or(left, right) => contains_window(left) || contains_window(right),
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => contains_window(inner),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            branches
                .iter()
                .any(|(condition, result)| contains_window(condition) || contains_window(result))
                || contains_window(else_result)
        }
        ExprKind::Aggregate {
            expression: Some(expression),
            ..
        } => contains_window(expression),
        ExprKind::Aggregate {
            expression: None, ..
        } => false,
    }
}

fn validate_recursive_complexity(
    relation: &Relation,
    max_intermediate_rows: usize,
) -> Result<(), UnsupportedReason> {
    const WORK_MULTIPLIER: usize = 64;
    let budget = max_intermediate_rows
        .saturating_mul(WORK_MULTIPLIER)
        .max(WORK_MULTIPLIER);
    let estimated = relation_work(relation);
    if estimated > budget {
        return Err(unsupported(
            UnsupportedKind::ComplexityLimit,
            format!(
                "recursive query expansion is estimated at {estimated} work units, above the supported limit of {budget}"
            ),
        ));
    }
    Ok(())
}

fn relation_work(relation: &Relation) -> usize {
    let own_rows = relation.max_rows.max(1);
    match &relation.node {
        RelationNode::Unit | RelationNode::Scan { .. } => own_rows,
        RelationNode::Product { left, right } => relation_work(left)
            .saturating_add(relation_work(right))
            .saturating_add(own_rows),
        RelationNode::Join {
            left, right, on, ..
        } => relation_work(left)
            .saturating_add(relation_work(right))
            .saturating_add(own_rows.saturating_mul(expression_work(on))),
        RelationNode::Filter { input, predicate } => relation_work(input).saturating_add(
            input
                .max_rows
                .max(1)
                .saturating_mul(expression_work(predicate)),
        ),
        RelationNode::Project { input, expressions } => relation_work(input).saturating_add(
            input
                .max_rows
                .max(1)
                .saturating_mul(expressions_work(expressions)),
        ),
        RelationNode::Distinct { input } => {
            relation_work(input).saturating_add(own_rows.saturating_mul(own_rows))
        }
        RelationNode::SetOperation { left, right, .. } => relation_work(left)
            .saturating_add(relation_work(right))
            .saturating_add(own_rows.saturating_mul(own_rows)),
        RelationNode::Aggregate {
            input,
            group_by,
            expressions,
            having,
        } => {
            let expression_cost = expressions_work(group_by)
                .saturating_add(expressions_work(expressions))
                .saturating_add(having.as_ref().map_or(0, expression_work))
                .max(1);
            relation_work(input).saturating_add(
                input
                    .max_rows
                    .max(1)
                    .saturating_mul(own_rows)
                    .saturating_mul(expression_cost),
            )
        }
        RelationNode::Sort { input, keys } => {
            let key_cost = keys
                .iter()
                .map(|key| expression_work(&key.expression))
                .fold(0_usize, usize::saturating_add)
                .max(1);
            relation_work(input)
                .saturating_add(own_rows.saturating_mul(own_rows).saturating_mul(key_cost))
        }
        RelationNode::Slice { input, .. } => relation_work(input).saturating_add(own_rows),
    }
}

fn expressions_work(expressions: &[TypedExpr]) -> usize {
    expressions
        .iter()
        .map(expression_work)
        .fold(0_usize, usize::saturating_add)
}

fn expression_work(expression: &TypedExpr) -> usize {
    let nested = match &expression.kind {
        ExprKind::Column(_) | ExprKind::OuterColumn { .. } | ExprKind::Literal(_) => 0,
        ExprKind::Compare { left, right, .. }
        | ExprKind::Arithmetic { left, right, .. }
        | ExprKind::And(left, right)
        | ExprKind::Or(left, right) => expression_work(left).saturating_add(expression_work(right)),
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => expression_work(inner),
        ExprKind::Coalesce(expressions)
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        } => expressions_work(expressions),
        ExprKind::Case {
            branches,
            else_result,
        } => branches
            .iter()
            .map(|(condition, result)| {
                expression_work(condition).saturating_add(expression_work(result))
            })
            .fold(expression_work(else_result), usize::saturating_add),
        ExprKind::Aggregate {
            expression: argument,
            ..
        } => argument.as_deref().map_or(0, expression_work),
        ExprKind::CountDistinctRow { expressions } => expressions_work(expressions),
        ExprKind::Exists { query, .. } | ExprKind::ScalarSubquery { query } => relation_work(query),
        ExprKind::InSubquery {
            expressions, query, ..
        } => expressions_work(expressions).saturating_add(relation_work(query)),
        ExprKind::WindowRank {
            partition_by,
            order_by,
            ..
        } => expressions_work(partition_by).saturating_add(
            order_by
                .iter()
                .map(|key| expression_work(&key.expression))
                .fold(0_usize, usize::saturating_add),
        ),
        ExprKind::WindowAggregate {
            expression,
            partition_by,
            order_by,
            ..
        } => expression
            .as_deref()
            .map_or(0, expression_work)
            .saturating_add(expressions_work(partition_by))
            .saturating_add(
                order_by
                    .iter()
                    .map(|key| expression_work(&key.expression))
                    .fold(0_usize, usize::saturating_add),
            ),
        ExprKind::FirstValue {
            expression,
            partition_by,
            order_by,
        } => expression_work(expression)
            .saturating_add(expressions_work(partition_by))
            .saturating_add(
                order_by
                    .iter()
                    .map(|key| expression_work(&key.expression))
                    .fold(0_usize, usize::saturating_add),
            ),
    };
    1_usize.saturating_add(nested)
}

fn validate_grouped_expression(
    expression: &TypedExpr,
    group_by: &[TypedExpr],
    determined_columns: &HashSet<usize>,
    inside_aggregate: bool,
) -> Result<(), UnsupportedReason> {
    if !inside_aggregate && group_by.contains(expression) {
        return Ok(());
    }
    match &expression.kind {
        ExprKind::Column(index) if !inside_aggregate && determined_columns.contains(index) => {
            Ok(())
        }
        ExprKind::Column(_) if !inside_aggregate => Err(type_error(
            "a projected or HAVING column must occur in GROUP BY",
        )),
        ExprKind::Column(_)
        | ExprKind::OuterColumn { .. }
        | ExprKind::Literal(_)
        | ExprKind::Exists { .. }
        | ExprKind::ScalarSubquery { .. } => Ok(()),
        ExprKind::WindowRank {
            partition_by,
            order_by,
            ..
        } => {
            if inside_aggregate {
                return Err(sql_unsupported(
                    "window functions inside aggregates are unsupported",
                ));
            }
            for expression in partition_by {
                validate_grouped_expression(
                    expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            for key in order_by {
                validate_grouped_expression(
                    &key.expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            Ok(())
        }
        ExprKind::WindowAggregate {
            expression,
            partition_by,
            order_by,
            ..
        } => {
            if inside_aggregate {
                return Err(sql_unsupported(
                    "window functions inside aggregates are unsupported",
                ));
            }
            if let Some(expression) = expression {
                validate_grouped_expression(
                    expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            for expression in partition_by {
                validate_grouped_expression(
                    expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            for key in order_by {
                validate_grouped_expression(
                    &key.expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            Ok(())
        }
        ExprKind::FirstValue {
            expression,
            partition_by,
            order_by,
        } => {
            if inside_aggregate {
                return Err(sql_unsupported(
                    "window functions inside aggregates are unsupported",
                ));
            }
            validate_grouped_expression(
                expression,
                group_by,
                determined_columns,
                inside_aggregate,
            )?;
            for expression in partition_by {
                validate_grouped_expression(
                    expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            for key in order_by {
                validate_grouped_expression(
                    &key.expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            Ok(())
        }
        ExprKind::InSubquery { expressions, .. } => {
            for expression in expressions {
                validate_grouped_expression(
                    expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            Ok(())
        }
        ExprKind::Aggregate {
            expression: argument,
            ..
        } => {
            if inside_aggregate {
                return Err(sql_unsupported("nested aggregates are unsupported"));
            }
            if let Some(argument) = argument {
                validate_grouped_expression(argument, group_by, determined_columns, true)?;
            }
            Ok(())
        }
        ExprKind::CountDistinctRow { expressions } => {
            if inside_aggregate {
                return Err(sql_unsupported("nested aggregates are unsupported"));
            }
            for expression in expressions {
                validate_grouped_expression(expression, group_by, determined_columns, true)?;
            }
            Ok(())
        }
        ExprKind::Compare { left, right, .. } | ExprKind::Arithmetic { left, right, .. } => {
            validate_grouped_expression(left, group_by, determined_columns, inside_aggregate)?;
            validate_grouped_expression(right, group_by, determined_columns, inside_aggregate)
        }
        ExprKind::And(left, right) | ExprKind::Or(left, right) => {
            validate_grouped_expression(left, group_by, determined_columns, inside_aggregate)?;
            validate_grouped_expression(right, group_by, determined_columns, inside_aggregate)
        }
        ExprKind::Not(inner)
        | ExprKind::IsNull(inner)
        | ExprKind::IsNotNull(inner)
        | ExprKind::Negate(inner)
        | ExprKind::Cast {
            expression: inner, ..
        } => validate_grouped_expression(inner, group_by, determined_columns, inside_aggregate),
        ExprKind::Coalesce(expressions)
        | ExprKind::ScalarFunction {
            arguments: expressions,
            ..
        } => {
            for expression in expressions {
                validate_grouped_expression(
                    expression,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            Ok(())
        }
        ExprKind::Case {
            branches,
            else_result,
        } => {
            for (condition, result) in branches {
                validate_grouped_expression(
                    condition,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
                validate_grouped_expression(
                    result,
                    group_by,
                    determined_columns,
                    inside_aggregate,
                )?;
            }
            validate_grouped_expression(else_result, group_by, determined_columns, inside_aggregate)
        }
    }
}

fn lower_projection(
    lowerer: &mut Lowerer<'_>,
    projection: &[SelectItem],
    input_columns: &[ColumnMeta],
) -> Result<(Vec<TypedExpr>, Vec<ColumnMeta>), UnsupportedReason> {
    let mut expressions = Vec::new();
    let mut columns = Vec::new();
    if projection.is_empty() {
        for (index, column) in input_columns.iter().enumerate() {
            if column.wildcard_visible {
                expressions.push(TypedExpr::column(index, column));
                columns.push(column.clone());
            }
        }
    }
    for item in projection {
        match item {
            SelectItem::UnnamedExpr(expression) => {
                let lowered = lower_expr(lowerer, expression, input_columns, None)?;
                let name = expression_name(lowerer, expression, input_columns)?;
                columns.push(projected_column(&name, &lowered, input_columns));
                expressions.push(lowered);
            }
            SelectItem::ExprWithAlias { expr, alias } => {
                let lowered = lower_expr(lowerer, expr, input_columns, None)?;
                let name = display_identifier(alias, "column alias")?;
                columns.push(projected_column(&name, &lowered, input_columns));
                expressions.push(lowered);
            }
            SelectItem::Wildcard(options) => {
                ensure_plain_wildcard(options)?;
                for (index, column) in input_columns.iter().enumerate() {
                    if !column.wildcard_visible {
                        continue;
                    }
                    expressions.push(TypedExpr::column(index, column));
                    columns.push(column.clone());
                }
            }
            SelectItem::QualifiedWildcard(kind, options) => {
                ensure_plain_wildcard(options)?;
                let SelectItemQualifiedWildcardKind::ObjectName(name) = kind else {
                    return Err(sql_unsupported(
                        "wildcards on arbitrary expressions are unsupported",
                    ));
                };
                let qualifier = canonical_name(&single_object_name(name, "wildcard qualifier")?);
                let mut found = false;
                for (index, column) in input_columns.iter().enumerate() {
                    if column.qualifier.as_deref() == Some(qualifier.as_str()) {
                        found = true;
                        expressions.push(TypedExpr::column(index, column));
                        columns.push(column.clone());
                    }
                }
                if !found {
                    return Err(unsupported(
                        UnsupportedKind::NameResolution,
                        format!("unknown table or alias `{qualifier}`"),
                    ));
                }
            }
            SelectItem::ExprWithAliases { .. } => {
                return Err(sql_unsupported(
                    "projections with multiple aliases are unsupported",
                ));
            }
        }
    }
    if expressions.is_empty() {
        return Err(sql_unsupported("the projection cannot be empty"));
    }
    Ok((expressions, columns))
}

fn projected_column(
    name: &str,
    expression: &TypedExpr,
    input_columns: &[ColumnMeta],
) -> ColumnMeta {
    let source = if let ExprKind::Column(index) = expression.kind {
        input_columns.get(index)
    } else {
        None
    };
    ColumnMeta {
        qualifier: None,
        name: name.to_owned(),
        canonical_name: canonical_name(name),
        source_qualifier: source.and_then(|column| {
            column
                .qualifier
                .clone()
                .or_else(|| column.source_qualifier.clone())
        }),
        source_name: source.map(|column| {
            if column.qualifier.is_some() {
                column.canonical_name.clone()
            } else {
                column
                    .source_name
                    .clone()
                    .unwrap_or_else(|| column.canonical_name.clone())
            }
        }),
        data_type: expression.data_type,
        nullable: expression.nullable,
        unqualified_visible: true,
        wildcard_visible: true,
    }
}

fn ensure_plain_wildcard(options: &WildcardAdditionalOptions) -> Result<(), UnsupportedReason> {
    if options != &WildcardAdditionalOptions::default() {
        return Err(sql_unsupported(
            "wildcard EXCLUDE/EXCEPT/REPLACE/RENAME options are unsupported",
        ));
    }
    Ok(())
}

fn expression_name(
    lowerer: &Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<String, UnsupportedReason> {
    match expression {
        SqlExpr::Identifier(_) | SqlExpr::CompoundIdentifier(_) => {
            let column = match resolve_scoped_column(expression, columns, &lowerer.outer_scopes)? {
                ScopedColumn::Local(_, column) | ScopedColumn::Outer { column, .. } => column,
            };
            Ok(column.name.clone())
        }
        SqlExpr::Nested(inner) => expression_name(lowerer, inner, columns),
        _ => Ok(expression.to_string()),
    }
}

fn lower_expr(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
    expected: Option<DataType>,
) -> Result<TypedExpr, UnsupportedReason> {
    let mut lowered = match expression {
        SqlExpr::Identifier(ident) => {
            let name = identifier(ident, "column or clause alias")?;
            let aliases = lowerer
                .clause_aliases
                .iter()
                .filter(|(alias, _)| alias == &name)
                .map(|(_, expression)| expression)
                .collect::<Vec<_>>();
            match aliases.as_slice() {
                [expression] => (*expression).clone(),
                [] => match resolve_scoped_column(expression, columns, &lowerer.outer_scopes)? {
                    ScopedColumn::Local(index, column) => TypedExpr::column(index, column),
                    ScopedColumn::Outer {
                        depth,
                        index,
                        column,
                    } => TypedExpr {
                        data_type: column.data_type,
                        nullable: column.nullable,
                        kind: ExprKind::OuterColumn { depth, index },
                    },
                },
                _ => {
                    return Err(unsupported(
                        UnsupportedKind::NameResolution,
                        format!("ambiguous SELECT alias `{name}`"),
                    ));
                }
            }
        }
        SqlExpr::CompoundIdentifier(_) => {
            match resolve_scoped_column(expression, columns, &lowerer.outer_scopes)? {
                ScopedColumn::Local(index, column) => TypedExpr::column(index, column),
                ScopedColumn::Outer {
                    depth,
                    index,
                    column,
                } => TypedExpr {
                    data_type: column.data_type,
                    nullable: column.nullable,
                    kind: ExprKind::OuterColumn { depth, index },
                },
            }
        }
        SqlExpr::Value(value) => {
            lower_literal_with_coercions(&value.value, expected, lowerer.mysql_coercions)?
        }
        SqlExpr::TypedString(value) => lower_typed_string(value)?,
        SqlExpr::Interval(interval) => lower_day_interval(lowerer, interval, columns)?,
        SqlExpr::Nested(inner) => return lower_expr(lowerer, inner, columns, expected),
        SqlExpr::UnaryOp {
            op: UnaryOperator::Not,
            expr,
        } => {
            let value = lower_expr(lowerer, expr, columns, Some(DataType::Boolean))?;
            TypedExpr {
                data_type: DataType::Boolean,
                nullable: value.nullable,
                kind: ExprKind::Not(Box::new(value)),
            }
        }
        SqlExpr::UnaryOp {
            op: UnaryOperator::Plus,
            expr,
        } => lower_expr(lowerer, expr, columns, expected)?,
        SqlExpr::UnaryOp {
            op: UnaryOperator::Minus,
            expr,
        } => {
            let value = lower_expr(lowerer, expr, columns, expected)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("unary minus requires a numeric operand"));
            }
            TypedExpr {
                data_type: value.data_type,
                nullable: value.nullable,
                kind: ExprKind::Negate(Box::new(value)),
            }
        }
        SqlExpr::BinaryOp { left, op, right } => match op {
            BinaryOperator::And | BinaryOperator::Or => {
                let left = lower_expr(lowerer, left, columns, Some(DataType::Boolean))?;
                let right = lower_expr(lowerer, right, columns, Some(DataType::Boolean))?;
                let nullable = left.nullable || right.nullable;
                let kind = if *op == BinaryOperator::And {
                    ExprKind::And(Box::new(left), Box::new(right))
                } else {
                    ExprKind::Or(Box::new(left), Box::new(right))
                };
                TypedExpr {
                    data_type: DataType::Boolean,
                    nullable,
                    kind,
                }
            }
            BinaryOperator::Eq | BinaryOperator::NotEq
                if matches!(left.as_ref(), SqlExpr::Tuple(_))
                    || matches!(right.as_ref(), SqlExpr::Tuple(_)) =>
            {
                lower_row_comparison(lowerer, left, op, right, columns)?
            }
            BinaryOperator::Eq
            | BinaryOperator::NotEq
            | BinaryOperator::Lt
            | BinaryOperator::LtEq
            | BinaryOperator::Gt
            | BinaryOperator::GtEq => lower_comparison(lowerer, left, op, right, columns)?,
            BinaryOperator::Spaceship => {
                lower_null_safe_comparison(lowerer, left, right, columns, false)?
            }
            BinaryOperator::Plus
            | BinaryOperator::Minus
            | BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Modulo => lower_arithmetic(lowerer, left, op, right, columns)?,
            BinaryOperator::StringConcat => {
                lower_concat(lowerer, [left.as_ref(), right.as_ref()], columns)?
            }
            _ => {
                return Err(sql_unsupported(
                    "this non-standard binary operator is unsupported",
                ));
            }
        },
        SqlExpr::IsNull(inner) | SqlExpr::IsNotNull(inner) => {
            let inferred = infer_type(lowerer, inner, columns)?.unwrap_or(DataType::Boolean);
            let value = lower_expr(lowerer, inner, columns, Some(inferred))?;
            let kind = if matches!(expression, SqlExpr::IsNull(_)) {
                ExprKind::IsNull(Box::new(value))
            } else {
                ExprKind::IsNotNull(Box::new(value))
            };
            TypedExpr {
                data_type: DataType::Boolean,
                nullable: false,
                kind,
            }
        }
        SqlExpr::IsTrue(inner)
        | SqlExpr::IsNotTrue(inner)
        | SqlExpr::IsFalse(inner)
        | SqlExpr::IsNotFalse(inner) => {
            let mut value = lower_expr(lowerer, inner, columns, Some(DataType::Boolean))?;
            if matches!(expression, SqlExpr::IsFalse(_) | SqlExpr::IsNotFalse(_)) {
                value = TypedExpr {
                    data_type: DataType::Boolean,
                    nullable: value.nullable,
                    kind: ExprKind::Not(Box::new(value)),
                };
            }
            let mut result = TypedExpr {
                data_type: DataType::Boolean,
                nullable: false,
                kind: ExprKind::Coalesce(vec![
                    value,
                    TypedExpr::literal(Value::Boolean(false), DataType::Boolean, false),
                ]),
            };
            if matches!(expression, SqlExpr::IsNotTrue(_) | SqlExpr::IsNotFalse(_)) {
                result = TypedExpr {
                    data_type: DataType::Boolean,
                    nullable: false,
                    kind: ExprKind::Not(Box::new(result)),
                };
            }
            result
        }
        SqlExpr::IsUnknown(inner) | SqlExpr::IsNotUnknown(inner) => {
            let inferred = infer_type(lowerer, inner, columns)?.unwrap_or(DataType::Boolean);
            let value = lower_expr(lowerer, inner, columns, Some(inferred))?;
            TypedExpr {
                data_type: DataType::Boolean,
                nullable: false,
                kind: if matches!(expression, SqlExpr::IsUnknown(_)) {
                    ExprKind::IsNull(Box::new(value))
                } else {
                    ExprKind::IsNotNull(Box::new(value))
                },
            }
        }
        SqlExpr::IsDistinctFrom(left, right) | SqlExpr::IsNotDistinctFrom(left, right) => {
            lower_null_safe_comparison(
                lowerer,
                left,
                right,
                columns,
                matches!(expression, SqlExpr::IsDistinctFrom(_, _)),
            )?
        }
        SqlExpr::Like {
            negated,
            any,
            expr,
            pattern,
            escape_char,
        } => {
            if *any || escape_char.is_some() {
                return Err(sql_unsupported(
                    "LIKE ANY and explicit LIKE escapes are unsupported",
                ));
            }
            lower_like(lowerer, expr, pattern, *negated, columns)?
        }
        SqlExpr::InList {
            expr,
            list,
            negated,
        } => lower_in_list(lowerer, expr, list, *negated, columns)?,
        SqlExpr::InSubquery {
            expr,
            subquery,
            negated,
        } => {
            let query = lowerer.lower_subquery(subquery, columns)?;
            let values = lower_row_operands(lowerer, expr, columns, &query.columns)?;
            let nullable = values.iter().any(|value| value.nullable)
                || query.columns.iter().any(|column| column.nullable);
            TypedExpr {
                data_type: DataType::Boolean,
                nullable,
                kind: ExprKind::InSubquery {
                    expressions: values,
                    query: Box::new(query),
                    negated: *negated,
                },
            }
        }
        SqlExpr::AllOp {
            left,
            compare_op,
            right,
        }
        | SqlExpr::AnyOp {
            left,
            compare_op,
            right,
            ..
        } => {
            let negated = match expression {
                SqlExpr::AllOp {
                    compare_op: BinaryOperator::NotEq,
                    ..
                } => true,
                SqlExpr::AnyOp {
                    compare_op: BinaryOperator::Eq,
                    ..
                } => false,
                _ => {
                    return Err(sql_unsupported(
                        "quantified subqueries currently support only `= ANY` and `<> ALL`",
                    ));
                }
            };
            let SqlExpr::Subquery(subquery) = right.as_ref() else {
                return Err(sql_unsupported("quantified comparisons require a subquery"));
            };
            let query = lowerer.lower_subquery(subquery, columns)?;
            let values = lower_row_operands(lowerer, left, columns, &query.columns)?;
            let nullable = values.iter().any(|value| value.nullable)
                || query.columns.iter().any(|column| column.nullable);
            let _ = compare_op;
            TypedExpr {
                data_type: DataType::Boolean,
                nullable,
                kind: ExprKind::InSubquery {
                    expressions: values,
                    query: Box::new(query),
                    negated,
                },
            }
        }
        SqlExpr::Exists { subquery, negated } => TypedExpr {
            data_type: DataType::Boolean,
            nullable: false,
            kind: ExprKind::Exists {
                query: Box::new(lowerer.lower_subquery(subquery, columns)?),
                negated: *negated,
            },
        },
        SqlExpr::Subquery(subquery) => {
            let query = lowerer.lower_subquery(subquery, columns)?;
            let [query_column] = query.columns.as_slice() else {
                return Err(type_error(
                    "a scalar subquery must return exactly one column",
                ));
            };
            if query.max_rows > 1 {
                return Err(sql_unsupported(
                    "a scalar subquery must be statically limited to at most one row",
                ));
            }
            TypedExpr {
                data_type: query_column.data_type,
                nullable: true,
                kind: ExprKind::ScalarSubquery {
                    query: Box::new(query),
                },
            }
        }
        SqlExpr::Between {
            expr,
            negated,
            low,
            high,
        } => lower_between(lowerer, expr, low, high, *negated, columns)?,
        SqlExpr::Function(function) => lower_function(lowerer, function, columns)?,
        SqlExpr::Case {
            operand,
            conditions,
            else_result,
            ..
        } => lower_case(
            lowerer,
            operand.as_deref(),
            conditions,
            else_result.as_deref(),
            columns,
            expected,
        )?,
        SqlExpr::Floor { expr, field } | SqlExpr::Ceil { expr, field } => {
            if field != &CeilFloorKind::DateTimeField(DateTimeField::NoDateTime) {
                return Err(sql_unsupported(
                    "only numeric FLOOR and CEIL without a scale are supported",
                ));
            }
            lower_floor_or_ceil(
                lowerer,
                expr,
                columns,
                matches!(expression, SqlExpr::Ceil { .. }),
            )?
        }
        SqlExpr::Substring {
            expr,
            substring_from,
            substring_for,
            ..
        } => lower_substring(
            lowerer,
            expr,
            substring_from.as_deref(),
            substring_for.as_deref(),
            columns,
        )?,
        SqlExpr::Extract { field, expr, .. } => {
            let function = match field {
                DateTimeField::Year => ScalarFunction::Year,
                DateTimeField::Month => ScalarFunction::Month,
                DateTimeField::Day => ScalarFunction::Day,
                _ => {
                    return Err(sql_unsupported(
                        "EXTRACT supports only YEAR, MONTH, and DAY",
                    ));
                }
            };
            let value = lower_expr(lowerer, expr, columns, Some(DataType::Date))?;
            TypedExpr {
                data_type: DataType::Integer,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function,
                    arguments: vec![value],
                },
            }
        }
        SqlExpr::Cast {
            kind,
            expr,
            data_type,
            array,
            format,
        } => {
            if *kind != CastKind::Cast || *array || format.is_some() {
                return Err(sql_unsupported(
                    "TRY/SAFE casts, array casts, and formatted casts are unsupported",
                ));
            }
            let to = cast_data_type(data_type, lowerer.mysql_coercions)?;
            let value = lower_expr(lowerer, expr, columns, None)?;
            lower_cast(value, to)?
        }
        _ => {
            return Err(sql_unsupported(format!(
                "unsupported expression `{expression}`"
            )));
        }
    };

    if let Some(expected) = expected
        && lowered.data_type != expected
    {
        if lowerer.mysql_coercions
            && expected == DataType::Boolean
            && matches!(lowered.data_type, DataType::Integer | DataType::Numeric)
        {
            lowered = lower_cast(lowered, DataType::Boolean)?;
        } else {
            return Err(type_error(format!(
                "expected {expected:?}, found {:?} in `{expression}`",
                lowered.data_type
            )));
        }
    }
    Ok(lowered)
}

fn lower_arithmetic(
    lowerer: &mut Lowerer<'_>,
    left: &SqlExpr,
    operator: &BinaryOperator,
    right: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let left_type = infer_type(lowerer, left, columns)?;
    let right_type = infer_type(lowerer, right, columns)?;
    let (result_type, left_target, right_target) = match (operator, left_type, right_type) {
        (BinaryOperator::Plus | BinaryOperator::Minus, None, Some(DataType::Integer))
            if matches!(right, SqlExpr::Interval(_)) =>
        {
            (DataType::Date, DataType::Date, DataType::Integer)
        }
        (BinaryOperator::Plus, Some(DataType::Integer), None)
            if matches!(left, SqlExpr::Interval(_)) =>
        {
            (DataType::Date, DataType::Integer, DataType::Date)
        }
        (BinaryOperator::Plus, Some(DataType::Date), Some(DataType::Integer)) => {
            (DataType::Date, DataType::Date, DataType::Integer)
        }
        (BinaryOperator::Plus, Some(DataType::Integer), Some(DataType::Date)) => {
            (DataType::Date, DataType::Integer, DataType::Date)
        }
        (BinaryOperator::Minus, Some(DataType::Date), Some(DataType::Integer)) => {
            (DataType::Date, DataType::Date, DataType::Integer)
        }
        (BinaryOperator::Minus, Some(DataType::Date), Some(DataType::Date)) => {
            (DataType::Integer, DataType::Date, DataType::Date)
        }
        (BinaryOperator::Modulo, _, _) => (DataType::Integer, DataType::Integer, DataType::Integer),
        (BinaryOperator::Divide, _, _) => (DataType::Numeric, DataType::Numeric, DataType::Numeric),
        (
            BinaryOperator::Plus | BinaryOperator::Minus | BinaryOperator::Multiply,
            Some(DataType::Numeric),
            _,
        )
        | (
            BinaryOperator::Plus | BinaryOperator::Minus | BinaryOperator::Multiply,
            _,
            Some(DataType::Numeric),
        ) => (DataType::Numeric, DataType::Numeric, DataType::Numeric),
        (
            BinaryOperator::Plus | BinaryOperator::Minus | BinaryOperator::Multiply,
            Some(DataType::Integer) | None,
            Some(DataType::Integer) | None,
        ) if left_type.is_some() || right_type.is_some() => {
            (DataType::Integer, DataType::Integer, DataType::Integer)
        }
        (BinaryOperator::Plus | BinaryOperator::Minus | BinaryOperator::Multiply, _, _) => {
            return Err(type_error(
                "arithmetic requires compatible numeric or date operands",
            ));
        }
        _ => unreachable!("the caller only passes arithmetic operators"),
    };
    let left = lower_coerced(lowerer, left, columns, left_target)?;
    let right = lower_coerced(lowerer, right, columns, right_target)?;
    let op = match operator {
        BinaryOperator::Plus => ArithmeticOp::Add,
        BinaryOperator::Minus => ArithmeticOp::Subtract,
        BinaryOperator::Multiply => ArithmeticOp::Multiply,
        BinaryOperator::Divide => ArithmeticOp::Divide,
        BinaryOperator::Modulo => ArithmeticOp::Modulo,
        _ => unreachable!("the caller only passes arithmetic operators"),
    };
    Ok(TypedExpr {
        data_type: result_type,
        nullable: left.nullable
            || right.nullable
            || matches!(op, ArithmeticOp::Divide | ArithmeticOp::Modulo)
            || result_type == DataType::Date,
        kind: ExprKind::Arithmetic {
            op,
            left: Box::new(left),
            right: Box::new(right),
        },
    })
}

fn lower_floor_or_ceil(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
    ceil: bool,
) -> Result<TypedExpr, UnsupportedReason> {
    let value = lower_expr(lowerer, expression, columns, None)?;
    if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
        return Err(type_error("FLOOR and CEIL require a numeric argument"));
    }
    let value = lower_cast(value, DataType::Numeric)?;
    Ok(TypedExpr {
        data_type: DataType::Integer,
        nullable: value.nullable,
        kind: ExprKind::ScalarFunction {
            function: if ceil {
                ScalarFunction::Ceil
            } else {
                ScalarFunction::Floor
            },
            arguments: vec![value],
        },
    })
}

fn lower_substring(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    start: Option<&SqlExpr>,
    length: Option<&SqlExpr>,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let start = start
        .ok_or_else(|| sql_unsupported("SUBSTRING requires a positive literal start position"))?;
    let start = literal_usize(lowerer, start, columns, "SUBSTRING start")?;
    if start == 0 {
        return Err(sql_unsupported(
            "SUBSTRING start must be a positive integer literal",
        ));
    }
    let length = length
        .map(|length| literal_usize(lowerer, length, columns, "SUBSTRING length"))
        .transpose()?;
    let value = lower_expr(lowerer, expression, columns, Some(DataType::Text))?;
    Ok(TypedExpr {
        data_type: DataType::Text,
        nullable: value.nullable,
        kind: ExprKind::ScalarFunction {
            function: ScalarFunction::Substring {
                start: start - 1,
                length,
            },
            arguments: vec![value],
        },
    })
}

fn typed_integer_literal(expression: &TypedExpr) -> Option<i64> {
    match &expression.kind {
        ExprKind::Literal(Value::Integer(value)) => Some(*value),
        ExprKind::Negate(value) => typed_integer_literal(value)?.checked_neg(),
        _ => None,
    }
}

fn literal_usize(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
    label: &str,
) -> Result<usize, UnsupportedReason> {
    let value = lower_expr(lowerer, expression, columns, Some(DataType::Integer))?;
    let ExprKind::Literal(Value::Integer(value)) = value.kind else {
        return Err(sql_unsupported(format!(
            "{label} must be a non-negative integer literal"
        )));
    };
    usize::try_from(value)
        .map_err(|_| sql_unsupported(format!("{label} must be a non-negative integer literal")))
}

fn lower_coerced(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
    target: DataType,
) -> Result<TypedExpr, UnsupportedReason> {
    match infer_type(lowerer, expression, columns)? {
        None => lower_expr(lowerer, expression, columns, Some(target)),
        Some(data_type) if data_type == target => {
            lower_expr(lowerer, expression, columns, Some(target))
        }
        Some(_) => lower_cast(lower_expr(lowerer, expression, columns, None)?, target),
    }
}

fn lower_cast(expression: TypedExpr, to: DataType) -> Result<TypedExpr, UnsupportedReason> {
    if expression.data_type == to {
        return Ok(expression);
    }
    if let ExprKind::Literal(Value::Text(value)) = &expression.kind {
        let parsed = match to {
            DataType::Date | DataType::Time | DataType::Numeric => {
                Some(parse_string_value(value, to)?)
            }
            DataType::Integer => Some(Value::Integer(value.trim().parse::<i64>().map_err(
                |_| type_error(format!("string literal `{value}` is not an exact integer")),
            )?)),
            _ => None,
        };
        if let Some(parsed) = parsed {
            return Ok(TypedExpr::literal(parsed, to, false));
        }
    }
    if !matches!(
        (expression.data_type, to),
        (DataType::Integer, DataType::Numeric)
            | (DataType::Boolean, DataType::Integer)
            | (DataType::Integer, DataType::Boolean)
            | (DataType::Numeric, DataType::Boolean)
            | (DataType::Text, DataType::Enum)
            | (DataType::Enum, DataType::Text)
    ) {
        return Err(sql_unsupported(format!(
            "exact casts from {:?} to {to:?} are unsupported",
            expression.data_type
        )));
    }
    Ok(TypedExpr {
        data_type: to,
        nullable: expression.nullable,
        kind: ExprKind::Cast {
            expression: Box::new(expression),
            to,
        },
    })
}

fn lower_row_operands(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
    expected_columns: &[ColumnMeta],
) -> Result<Vec<TypedExpr>, UnsupportedReason> {
    let expressions = match expression {
        SqlExpr::Tuple(expressions) => expressions.as_slice(),
        _ => std::slice::from_ref(expression),
    };
    if expressions.len() != expected_columns.len() {
        return Err(type_error(format!(
            "an IN subquery returns {} columns for a {}-column left operand",
            expected_columns.len(),
            expressions.len()
        )));
    }
    expressions
        .iter()
        .zip(expected_columns)
        .map(|(expression, column)| {
            lower_expr(lowerer, expression, columns, Some(column.data_type))
        })
        .collect()
}

fn lower_in_list(
    lowerer: &mut Lowerer<'_>,
    value: &SqlExpr,
    list: &[SqlExpr],
    negated: bool,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let mut result = TypedExpr::literal(Value::Boolean(false), DataType::Boolean, false);
    for choice in list {
        let equal = lower_row_comparison(lowerer, value, &BinaryOperator::Eq, choice, columns)?;
        let nullable = result.nullable || equal.nullable;
        result = TypedExpr {
            data_type: DataType::Boolean,
            nullable,
            kind: ExprKind::Or(Box::new(result), Box::new(equal)),
        };
    }
    if negated {
        Ok(TypedExpr {
            data_type: DataType::Boolean,
            nullable: result.nullable,
            kind: ExprKind::Not(Box::new(result)),
        })
    } else {
        Ok(result)
    }
}

fn lower_row_comparison(
    lowerer: &mut Lowerer<'_>,
    left: &SqlExpr,
    operator: &BinaryOperator,
    right: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let left = match left {
        SqlExpr::Tuple(expressions) => expressions.as_slice(),
        _ => std::slice::from_ref(left),
    };
    let right = match right {
        SqlExpr::Tuple(expressions) => expressions.as_slice(),
        _ => std::slice::from_ref(right),
    };
    if left.len() != right.len() {
        return Err(type_error("row comparison operands have different arities"));
    }
    if !matches!(operator, BinaryOperator::Eq | BinaryOperator::NotEq) {
        return Err(sql_unsupported("ordered row comparisons are unsupported"));
    }
    let mut result = TypedExpr::literal(Value::Boolean(true), DataType::Boolean, false);
    for (left, right) in left.iter().zip(right) {
        let equal = lower_comparison(lowerer, left, &BinaryOperator::Eq, right, columns)?;
        result = TypedExpr {
            data_type: DataType::Boolean,
            nullable: result.nullable || equal.nullable,
            kind: ExprKind::And(Box::new(result), Box::new(equal)),
        };
    }
    if *operator == BinaryOperator::NotEq {
        Ok(TypedExpr {
            data_type: DataType::Boolean,
            nullable: result.nullable,
            kind: ExprKind::Not(Box::new(result)),
        })
    } else {
        Ok(result)
    }
}

fn lower_like(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    pattern: &SqlExpr,
    negated: bool,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let SqlExpr::Value(pattern) = pattern else {
        return Err(sql_unsupported("LIKE patterns must be string literals"));
    };
    let SqlValue::SingleQuotedString(pattern) = &pattern.value else {
        return Err(sql_unsupported("LIKE patterns must be string literals"));
    };
    if pattern.contains('_') {
        return Err(sql_unsupported(
            "LIKE patterns containing `_` are unsupported",
        ));
    }
    let leading = pattern.starts_with('%');
    let trailing = pattern.ends_with('%');
    let core = pattern
        .strip_prefix('%')
        .unwrap_or(pattern)
        .strip_suffix('%')
        .unwrap_or_else(|| pattern.strip_prefix('%').unwrap_or(pattern));
    if core.contains('%') {
        return Err(sql_unsupported(
            "LIKE supports only one leading and/or trailing `%` wildcard",
        ));
    }
    let value = lower_expr(lowerer, expression, columns, Some(DataType::Text))?;
    let pattern = TypedExpr::literal(Value::Text(core.to_owned()), DataType::Text, false);
    let mut result = if !leading && !trailing {
        TypedExpr {
            data_type: DataType::Boolean,
            nullable: value.nullable,
            kind: ExprKind::Compare {
                op: CompareOp::Equal,
                left: Box::new(value),
                right: Box::new(pattern),
            },
        }
    } else {
        TypedExpr {
            data_type: DataType::Boolean,
            nullable: value.nullable,
            kind: ExprKind::ScalarFunction {
                function: match (leading, trailing) {
                    (false, true) => ScalarFunction::StartsWith,
                    (true, false) => ScalarFunction::EndsWith,
                    (true, true) => ScalarFunction::Contains,
                    (false, false) => unreachable!(),
                },
                arguments: vec![value, pattern],
            },
        }
    };
    if negated {
        result = TypedExpr {
            data_type: DataType::Boolean,
            nullable: result.nullable,
            kind: ExprKind::Not(Box::new(result)),
        };
    }
    Ok(result)
}

fn lower_between(
    lowerer: &mut Lowerer<'_>,
    value: &SqlExpr,
    lower: &SqlExpr,
    upper: &SqlExpr,
    negated: bool,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let lower = lower_comparison(lowerer, value, &BinaryOperator::GtEq, lower, columns)?;
    let upper = lower_comparison(lowerer, value, &BinaryOperator::LtEq, upper, columns)?;
    let mut result = TypedExpr {
        data_type: DataType::Boolean,
        nullable: lower.nullable || upper.nullable,
        kind: ExprKind::And(Box::new(lower), Box::new(upper)),
    };
    if negated {
        result = TypedExpr {
            data_type: DataType::Boolean,
            nullable: result.nullable,
            kind: ExprKind::Not(Box::new(result)),
        };
    }
    Ok(result)
}

fn lower_window_partition_expression(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let expected = matches!(
        expression,
        SqlExpr::Value(value) if value.value == SqlValue::Null
    )
    .then_some(DataType::Boolean);
    lower_expr(lowerer, expression, columns, expected)
}

fn lower_window_rank(
    lowerer: &mut Lowerer<'_>,
    function: &Function,
    rank_function: WindowRankFunction,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    if !lowerer.allow_window_functions {
        return Err(sql_unsupported(
            "window ranking functions are supported only as direct SELECT expressions",
        ));
    }
    if function.filter.is_some()
        || function.null_treatment.is_some()
        || !function.within_group.is_empty()
        || !matches!(function.parameters, FunctionArguments::None)
    {
        return Err(sql_unsupported(
            "window ranking filters, parameters, and ordered arguments are unsupported",
        ));
    }
    let (arguments, distinct) = function_arguments(&function.args)?;
    if distinct || !arguments.is_empty() {
        return Err(type_error("window ranking functions expect no arguments"));
    }
    let Some(WindowType::WindowSpec(specification)) = &function.over else {
        return Err(sql_unsupported(
            "window ranking functions require an inline window specification",
        ));
    };
    if specification.window_name.is_some() || specification.window_frame.is_some() {
        return Err(sql_unsupported(
            "named and explicitly framed ranking windows are unsupported",
        ));
    }
    let partition_by = specification
        .partition_by
        .iter()
        .map(|expression| lower_window_partition_expression(lowerer, expression, columns))
        .collect::<Result<Vec<_>, _>>()?;
    let order_by = specification
        .order_by
        .iter()
        .map(|order| {
            if order.with_fill.is_some() {
                return Err(sql_unsupported(
                    "ranking window ORDER BY WITH FILL is unsupported",
                ));
            }
            Ok(SortKey {
                expression: lower_expr(lowerer, &order.expr, columns, None)?,
                ascending: order.options.asc.unwrap_or(true),
                nulls_first: order
                    .options
                    .nulls_first
                    .unwrap_or(order.options.asc.unwrap_or(true)),
            })
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    if partition_by.iter().any(contains_aggregate)
        || order_by
            .iter()
            .any(|key| contains_aggregate(&key.expression))
    {
        return Err(sql_unsupported(
            "ranking window partition and order expressions cannot contain aggregates",
        ));
    }
    Ok(TypedExpr {
        data_type: DataType::Integer,
        nullable: false,
        kind: ExprKind::WindowRank {
            function: rank_function,
            partition_by,
            order_by,
        },
    })
}

fn lower_window_aggregate(
    lowerer: &mut Lowerer<'_>,
    function: &Function,
    name: &str,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    if !lowerer.allow_window_functions {
        return Err(sql_unsupported(
            "window aggregates are supported only as direct SELECT expressions",
        ));
    }
    if function.filter.is_some()
        || function.null_treatment.is_some()
        || !function.within_group.is_empty()
        || !matches!(function.parameters, FunctionArguments::None)
    {
        return Err(sql_unsupported(
            "window aggregate filters, parameters, and ordered arguments are unsupported",
        ));
    }
    let Some(WindowType::WindowSpec(specification)) = &function.over else {
        return Err(sql_unsupported(
            "window aggregates require an inline window specification",
        ));
    };
    if specification.window_name.is_some() || specification.window_frame.is_some() {
        return Err(sql_unsupported(
            "named and explicitly framed aggregate windows are unsupported",
        ));
    }
    let (arguments, distinct) = function_arguments(&function.args)?;
    let aggregate = lower_aggregate_function(lowerer, name, &arguments, distinct, columns)?;
    let TypedExpr {
        data_type,
        nullable,
        kind:
            ExprKind::Aggregate {
                function,
                expression,
                distinct,
            },
    } = aggregate
    else {
        return Err(unsupported(
            UnsupportedKind::Internal,
            "aggregate lowering did not produce an aggregate expression",
        ));
    };
    let partition_by = specification
        .partition_by
        .iter()
        .map(|expression| lower_window_partition_expression(lowerer, expression, columns))
        .collect::<Result<Vec<_>, _>>()?;
    let order_by = specification
        .order_by
        .iter()
        .map(|order| {
            if order.with_fill.is_some() {
                return Err(sql_unsupported(
                    "aggregate window ORDER BY WITH FILL is unsupported",
                ));
            }
            Ok(SortKey {
                expression: lower_expr(lowerer, &order.expr, columns, None)?,
                ascending: order.options.asc.unwrap_or(true),
                nulls_first: order
                    .options
                    .nulls_first
                    .unwrap_or(order.options.asc.unwrap_or(true)),
            })
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    Ok(TypedExpr {
        data_type,
        nullable,
        kind: ExprKind::WindowAggregate {
            function,
            expression,
            distinct,
            partition_by,
            order_by,
        },
    })
}

fn lower_first_value(
    lowerer: &mut Lowerer<'_>,
    function: &Function,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    if !lowerer.allow_window_functions {
        return Err(sql_unsupported(
            "FIRST_VALUE is supported only as a direct SELECT expression",
        ));
    }
    if function.filter.is_some()
        || function.null_treatment.is_some()
        || !function.within_group.is_empty()
        || !matches!(function.parameters, FunctionArguments::None)
    {
        return Err(sql_unsupported(
            "FIRST_VALUE filters, NULL modifiers, parameters, and ordered arguments are unsupported",
        ));
    }
    let (arguments, distinct) = function_arguments(&function.args)?;
    let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
    let value = lower_expr(lowerer, expressions[0], columns, None)?;
    let Some(WindowType::WindowSpec(specification)) = &function.over else {
        return Err(sql_unsupported(
            "FIRST_VALUE requires an inline window specification",
        ));
    };
    if specification.window_name.is_some() || specification.window_frame.is_some() {
        return Err(sql_unsupported(
            "named and explicitly framed FIRST_VALUE windows are unsupported",
        ));
    }
    if specification.order_by.is_empty() {
        return Err(sql_unsupported("FIRST_VALUE requires ORDER BY"));
    }
    let partition_by = specification
        .partition_by
        .iter()
        .map(|expression| lower_window_partition_expression(lowerer, expression, columns))
        .collect::<Result<Vec<_>, _>>()?;
    let order_by = specification
        .order_by
        .iter()
        .map(|order| {
            if order.with_fill.is_some() {
                return Err(sql_unsupported(
                    "FIRST_VALUE ORDER BY WITH FILL is unsupported",
                ));
            }
            Ok(SortKey {
                expression: lower_expr(lowerer, &order.expr, columns, None)?,
                ascending: order.options.asc.unwrap_or(true),
                nulls_first: order
                    .options
                    .nulls_first
                    .unwrap_or(order.options.asc.unwrap_or(true)),
            })
        })
        .collect::<Result<Vec<_>, UnsupportedReason>>()?;
    Ok(TypedExpr {
        data_type: value.data_type,
        nullable: value.nullable,
        kind: ExprKind::FirstValue {
            expression: Box::new(value),
            partition_by,
            order_by,
        },
    })
}

fn lower_function(
    lowerer: &mut Lowerer<'_>,
    function: &Function,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let name = single_object_name(&function.name, "function")?;
    if function.over.is_some() && matches!(name.as_str(), "row_number" | "rank" | "dense_rank") {
        return lower_window_rank(
            lowerer,
            function,
            match name.as_str() {
                "row_number" => WindowRankFunction::RowNumber,
                "rank" => WindowRankFunction::Rank,
                "dense_rank" => WindowRankFunction::DenseRank,
                _ => unreachable!(),
            },
            columns,
        );
    }
    if name == "first_value" && function.over.is_some() {
        return lower_first_value(lowerer, function, columns);
    }
    if matches!(name.as_str(), "count" | "sum" | "min" | "max" | "avg") && function.over.is_some() {
        return lower_window_aggregate(lowerer, function, &name, columns);
    }
    if function.over.is_some()
        || function.filter.is_some()
        || function.null_treatment.is_some()
        || !function.within_group.is_empty()
        || !matches!(function.parameters, FunctionArguments::None)
    {
        return Err(sql_unsupported(
            "windowed, filtered, parameterized, and ordered functions are unsupported",
        ));
    }
    let (arguments, distinct) = function_arguments(&function.args)?;
    match name.as_str() {
        "count" | "sum" | "min" | "max" | "avg" => {
            lower_aggregate_function(lowerer, &name, &arguments, distinct, columns)
        }
        "coalesce" | "ifnull" => {
            if arguments.len() < 2 || (name == "ifnull" && arguments.len() != 2) {
                return Err(type_error(format!("{name} has the wrong argument count")));
            }
            if distinct {
                return Err(sql_unsupported("DISTINCT is invalid for scalar functions"));
            }
            let expressions = function_expr_arguments(&arguments)?;
            let data_type = common_expression_type(lowerer, &expressions, columns)?;
            let values = expressions
                .iter()
                .map(|expression| lower_coerced(lowerer, expression, columns, data_type))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(TypedExpr {
                data_type,
                nullable: values.iter().all(|value| value.nullable),
                kind: ExprKind::Coalesce(values),
            })
        }
        "if" => {
            if distinct || arguments.len() != 3 {
                return Err(type_error("IF expects exactly three arguments"));
            }
            let expressions = function_expr_arguments(&arguments)?;
            lower_if(
                lowerer,
                expressions[0],
                expressions[1],
                expressions[2],
                columns,
            )
        }
        "abs" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, None)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("ABS requires a numeric argument"));
            }
            Ok(TypedExpr {
                data_type: value.data_type,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::Abs,
                    arguments: vec![value],
                },
            })
        }
        "sign" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, None)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("SIGN requires a numeric argument"));
            }
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::Sign,
                    arguments: vec![value],
                },
            })
        }
        "power" | "pow" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let exponent = lower_expr(lowerer, expressions[1], columns, Some(DataType::Integer))?;
            let ExprKind::Literal(Value::Integer(exponent)) = exponent.kind else {
                return Err(sql_unsupported(
                    "POWER exponent must be a non-negative integer literal",
                ));
            };
            let exponent = u32::try_from(exponent)
                .ok()
                .filter(|exponent| *exponent <= 8)
                .ok_or_else(|| {
                    sql_unsupported("POWER exponent must be an integer literal from 0 through 8")
                })?;
            let value = lower_expr(lowerer, expressions[0], columns, None)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("POWER requires a numeric base"));
            }
            let value = lower_cast(value, DataType::Numeric)?;
            Ok(TypedExpr {
                data_type: DataType::Numeric,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::Power(exponent),
                    arguments: vec![value],
                },
            })
        }
        "floor" | "ceil" | "ceiling" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, None)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("FLOOR and CEIL require a numeric argument"));
            }
            let value = lower_cast(value, DataType::Numeric)?;
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: if name == "floor" {
                        ScalarFunction::Floor
                    } else {
                        ScalarFunction::Ceil
                    },
                    arguments: vec![value],
                },
            })
        }
        "mod" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            lower_arithmetic(
                lowerer,
                expressions[0],
                &BinaryOperator::Modulo,
                expressions[1],
                columns,
            )
        }
        "round" => {
            let expressions = function_expr_arguments(&arguments)?;
            if distinct || !(1..=2).contains(&expressions.len()) {
                return Err(type_error("ROUND expects one or two arguments"));
            }
            let value = lower_expr(lowerer, expressions[0], columns, None)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("ROUND requires a numeric argument"));
            }
            let mut lowered = vec![value.clone()];
            if let Some(scale) = expressions.get(1) {
                let scale = lower_expr(lowerer, scale, columns, Some(DataType::Integer))?;
                let Some(scale) = typed_integer_literal(&scale) else {
                    return Err(sql_unsupported("ROUND scale must be an integer literal"));
                };
                lowered.push(TypedExpr::literal(
                    Value::Integer(scale),
                    DataType::Integer,
                    false,
                ));
            }
            Ok(TypedExpr {
                data_type: value.data_type,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::Round,
                    arguments: lowered,
                },
            })
        }
        "truncate" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let value = lower_expr(lowerer, expressions[0], columns, None)?;
            if !matches!(value.data_type, DataType::Integer | DataType::Numeric) {
                return Err(type_error("TRUNCATE requires a numeric argument"));
            }
            let scale = lower_expr(lowerer, expressions[1], columns, Some(DataType::Integer))?;
            let Some(scale) = typed_integer_literal(&scale) else {
                return Err(sql_unsupported("TRUNCATE scale must be an integer literal"));
            };
            Ok(TypedExpr {
                data_type: value.data_type,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::Truncate,
                    arguments: vec![
                        value,
                        TypedExpr::literal(Value::Integer(scale), DataType::Integer, false),
                    ],
                },
            })
        }
        "concat" => {
            let expressions = function_expr_arguments(&arguments)?;
            if distinct || expressions.is_empty() {
                return Err(type_error("CONCAT expects at least one argument"));
            }
            lower_concat(lowerer, expressions, columns)
        }
        "length" | "char_length" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, Some(DataType::Text))?;
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::Length,
                    arguments: vec![value],
                },
            })
        }
        "left" | "right" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let value = lower_expr(lowerer, expressions[0], columns, Some(DataType::Text))?;
            let length = literal_usize(lowerer, expressions[1], columns, "string length")?;
            Ok(TypedExpr {
                data_type: DataType::Text,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: if name == "left" {
                        ScalarFunction::Left(length)
                    } else {
                        ScalarFunction::Right(length)
                    },
                    arguments: vec![value],
                },
            })
        }
        "datediff" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let left = lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))?;
            let right = lower_expr(lowerer, expressions[1], columns, Some(DataType::Date))?;
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: left.nullable || right.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::DateDiff,
                    arguments: vec![left, right],
                },
            })
        }
        "year" | "month" | "day" | "dayofmonth" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))?;
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: match name.as_str() {
                        "year" => ScalarFunction::Year,
                        "month" => ScalarFunction::Month,
                        "day" | "dayofmonth" => ScalarFunction::Day,
                        _ => unreachable!(),
                    },
                    arguments: vec![value],
                },
            })
        }
        "to_days" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))?;
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::ToDays,
                    arguments: vec![value],
                },
            })
        }
        "str_to_date" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let date = string_literal(expressions[0], "STR_TO_DATE input")?;
            let format = string_literal(expressions[1], "STR_TO_DATE format")?;
            if !matches!(
                format.as_str(),
                "%Y-%m-%d" | "%Y-%M-%D" | "%Y-%c-%e" | "%Y/%m/%d"
            ) {
                return Err(sql_unsupported(
                    "STR_TO_DATE supports only literal year-month-day formats",
                ));
            }
            let date = if format == "%Y/%m/%d" {
                date.replace('/', "-")
            } else {
                date
            };
            Ok(TypedExpr::literal(
                parse_string_value(&date, DataType::Date)?,
                DataType::Date,
                false,
            ))
        }
        "date_format" if lowerer.mysql_coercions => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let format = string_literal(expressions[1], "DATE_FORMAT format")?;
            if !matches!(format.as_str(), "%Y-%m-%d" | "%Y-%M-%D" | "%Y-%c-%e") {
                return Err(sql_unsupported(
                    "DATE_FORMAT compatibility supports only year-month-day formats",
                ));
            }
            lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))
        }
        "last_day" | "weekday" | "dayofweek" | "quarter" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let value = lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))?;
            let function = match name.as_str() {
                "last_day" => ScalarFunction::LastDay,
                "weekday" => ScalarFunction::Weekday,
                "dayofweek" => ScalarFunction::DayOfWeek,
                "quarter" => ScalarFunction::Quarter,
                _ => unreachable!(),
            };
            Ok(TypedExpr {
                data_type: if function == ScalarFunction::LastDay {
                    DataType::Date
                } else {
                    DataType::Integer
                },
                nullable: value.nullable,
                kind: ExprKind::ScalarFunction {
                    function,
                    arguments: vec![value],
                },
            })
        }
        "date_add" | "adddate" | "date_sub" | "subdate" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let date = lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))?;
            let days = lower_expr(lowerer, expressions[1], columns, Some(DataType::Integer))?;
            Ok(TypedExpr {
                data_type: DataType::Date,
                nullable: true,
                kind: ExprKind::Arithmetic {
                    op: if matches!(name.as_str(), "date_sub" | "subdate") {
                        ArithmeticOp::Subtract
                    } else {
                        ArithmeticOp::Add
                    },
                    left: Box::new(date),
                    right: Box::new(days),
                },
            })
        }
        "date" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            lower_expr(lowerer, expressions[0], columns, Some(DataType::Date))
        }
        "timestampdiff" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 3)?;
            let SqlExpr::Identifier(unit) = expressions[0] else {
                return Err(sql_unsupported(
                    "TIMESTAMPDIFF requires a DAY unit identifier",
                ));
            };
            if identifier(unit, "TIMESTAMPDIFF unit")? != "day" {
                return Err(sql_unsupported("only TIMESTAMPDIFF(DAY, ...) is supported"));
            }
            let start = lower_expr(lowerer, expressions[1], columns, Some(DataType::Date))?;
            let end = lower_expr(lowerer, expressions[2], columns, Some(DataType::Date))?;
            Ok(TypedExpr {
                data_type: DataType::Integer,
                nullable: start.nullable || end.nullable,
                kind: ExprKind::ScalarFunction {
                    function: ScalarFunction::DateDiff,
                    arguments: vec![end, start],
                },
            })
        }
        "nullif" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 2)?;
            let data_type = comparison_operand_type(
                expressions[0],
                infer_type(lowerer, expressions[0], columns)?,
                expressions[1],
                infer_type(lowerer, expressions[1], columns)?,
            )?;
            let left = lower_expr(lowerer, expressions[0], columns, Some(data_type))?;
            let equal = lower_comparison(
                lowerer,
                expressions[0],
                &BinaryOperator::Eq,
                expressions[1],
                columns,
            )?;
            Ok(TypedExpr {
                data_type,
                nullable: true,
                kind: ExprKind::Case {
                    branches: vec![(equal, TypedExpr::literal(Value::Null, data_type, true))],
                    else_result: Box::new(left),
                },
            })
        }
        "isnull" => {
            let expressions = exact_scalar_arguments(&arguments, distinct, 1)?;
            let data_type = infer_type(lowerer, expressions[0], columns)?
                .ok_or_else(|| type_error("ISNULL needs a typed argument"))?;
            let value = lower_expr(lowerer, expressions[0], columns, Some(data_type))?;
            Ok(TypedExpr {
                data_type: DataType::Boolean,
                nullable: false,
                kind: ExprKind::IsNull(Box::new(value)),
            })
        }
        _ => Err(sql_unsupported(format!("unsupported function `{name}`"))),
    }
}

fn function_arguments(
    arguments: &FunctionArguments,
) -> Result<(Vec<&FunctionArgExpr>, bool), UnsupportedReason> {
    let FunctionArguments::List(arguments) = arguments else {
        return Err(sql_unsupported("functions require a regular argument list"));
    };
    if !arguments.clauses.is_empty() {
        return Err(sql_unsupported("function argument clauses are unsupported"));
    }
    let distinct = match arguments.duplicate_treatment {
        None | Some(DuplicateTreatment::All) => false,
        Some(DuplicateTreatment::Distinct) => true,
    };
    let arguments = arguments
        .args
        .iter()
        .map(|argument| match argument {
            FunctionArg::Unnamed(argument) => Ok(argument),
            FunctionArg::Named { .. } | FunctionArg::ExprNamed { .. } => {
                Err(sql_unsupported("named function arguments are unsupported"))
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((arguments, distinct))
}

fn function_expr_arguments<'a>(
    arguments: &[&'a FunctionArgExpr],
) -> Result<Vec<&'a SqlExpr>, UnsupportedReason> {
    arguments
        .iter()
        .map(|argument| match argument {
            FunctionArgExpr::Expr(expression) => Ok(expression),
            FunctionArgExpr::Wildcard
            | FunctionArgExpr::QualifiedWildcard(_)
            | FunctionArgExpr::WildcardWithOptions(_) => {
                Err(sql_unsupported("wildcards are only valid in COUNT"))
            }
        })
        .collect()
}

fn string_literal(expression: &SqlExpr, label: &str) -> Result<String, UnsupportedReason> {
    let SqlExpr::Value(value) = expression else {
        return Err(sql_unsupported(format!("{label} must be a string literal")));
    };
    let SqlValue::SingleQuotedString(value) = &value.value else {
        return Err(sql_unsupported(format!("{label} must be a string literal")));
    };
    Ok(value.clone())
}

fn exact_scalar_arguments<'a>(
    arguments: &[&'a FunctionArgExpr],
    distinct: bool,
    expected: usize,
) -> Result<Vec<&'a SqlExpr>, UnsupportedReason> {
    if distinct || arguments.len() != expected {
        return Err(type_error(format!(
            "function expects exactly {expected} scalar arguments"
        )));
    }
    function_expr_arguments(arguments)
}

fn coerce_mysql_numeric_expression(expression: TypedExpr) -> Result<TypedExpr, UnsupportedReason> {
    let nullable = expression.nullable;
    match expression.kind {
        ExprKind::Literal(Value::Text(value)) => Ok(TypedExpr::literal(
            Value::Numeric(parse_numeric(value.trim())?),
            DataType::Numeric,
            false,
        )),
        kind @ ExprKind::Literal(Value::Integer(_) | Value::Numeric(_)) => lower_cast(
            TypedExpr {
                data_type: expression.data_type,
                nullable,
                kind,
            },
            DataType::Numeric,
        ),
        ExprKind::Case {
            branches,
            else_result,
        } => {
            let branches = branches
                .into_iter()
                .map(|(condition, result)| {
                    Ok((condition, coerce_mysql_numeric_expression(result)?))
                })
                .collect::<Result<Vec<_>, UnsupportedReason>>()?;
            let else_result = coerce_mysql_numeric_expression(*else_result)?;
            Ok(TypedExpr {
                data_type: DataType::Numeric,
                nullable,
                kind: ExprKind::Case {
                    branches,
                    else_result: Box::new(else_result),
                },
            })
        }
        ExprKind::Coalesce(expressions) => Ok(TypedExpr {
            data_type: DataType::Numeric,
            nullable,
            kind: ExprKind::Coalesce(
                expressions
                    .into_iter()
                    .map(coerce_mysql_numeric_expression)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        }),
        _ => Err(type_error(
            "exact MySQL text-to-number coercion requires literal CASE/IF/COALESCE results",
        )),
    }
}

fn lower_aggregate_function(
    lowerer: &mut Lowerer<'_>,
    name: &str,
    arguments: &[&FunctionArgExpr],
    distinct: bool,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let function = match name {
        "count" => AggregateFunction::Count,
        "sum" => AggregateFunction::Sum,
        "min" => AggregateFunction::Min,
        "max" => AggregateFunction::Max,
        "avg" => AggregateFunction::Avg,
        _ => unreachable!("the caller recognized this aggregate"),
    };
    if function == AggregateFunction::Count && distinct && arguments.len() > 1 {
        let expressions = function_expr_arguments(arguments)?
            .into_iter()
            .map(|argument| lower_expr(lowerer, argument, columns, None))
            .collect::<Result<Vec<_>, _>>()?;
        if expressions.iter().any(contains_aggregate) {
            return Err(sql_unsupported(
                "nested aggregate functions are unsupported",
            ));
        }
        return Ok(TypedExpr {
            data_type: DataType::Integer,
            nullable: false,
            kind: ExprKind::CountDistinctRow { expressions },
        });
    }
    let mut expression = if function == AggregateFunction::Count
        && matches!(arguments, [FunctionArgExpr::Wildcard])
    {
        if distinct {
            return Err(sql_unsupported("COUNT(DISTINCT *) is unsupported"));
        }
        None
    } else {
        let scalar_arguments = function_expr_arguments(arguments)?;
        let [argument] = scalar_arguments.as_slice() else {
            return Err(type_error(format!("{name} expects exactly one argument")));
        };
        let expression = lower_expr(lowerer, argument, columns, None)?;
        if contains_aggregate(&expression) {
            return Err(sql_unsupported(
                "nested aggregate functions are unsupported",
            ));
        }
        Some(Box::new(expression))
    };
    if matches!(function, AggregateFunction::Sum | AggregateFunction::Avg)
        && expression
            .as_ref()
            .is_some_and(|expression| expression.data_type == DataType::Text)
        && lowerer.mysql_coercions
    {
        let value = expression.take().ok_or_else(|| {
            unsupported(UnsupportedKind::Internal, "aggregate argument is missing")
        })?;
        expression = Some(Box::new(coerce_mysql_numeric_expression(*value)?));
    }
    let input_type = expression.as_ref().map(|expression| expression.data_type);
    let data_type = match function {
        AggregateFunction::Count => DataType::Integer,
        AggregateFunction::Sum => match input_type {
            Some(DataType::Integer | DataType::Boolean) => DataType::Integer,
            Some(DataType::Numeric) => DataType::Numeric,
            _ => return Err(type_error("SUM requires a numeric or boolean argument")),
        },
        AggregateFunction::Avg => match input_type {
            Some(DataType::Integer | DataType::Boolean | DataType::Numeric) => DataType::Numeric,
            _ => return Err(type_error("AVG requires a numeric or boolean argument")),
        },
        AggregateFunction::Min | AggregateFunction::Max => {
            input_type.ok_or_else(|| type_error("MIN/MAX requires an argument"))?
        }
    };
    Ok(TypedExpr {
        data_type,
        nullable: function != AggregateFunction::Count,
        kind: ExprKind::Aggregate {
            function,
            expression,
            distinct,
        },
    })
}

fn lower_concat<'a>(
    lowerer: &mut Lowerer<'_>,
    expressions: impl IntoIterator<Item = &'a SqlExpr>,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let arguments = expressions
        .into_iter()
        .map(|expression| lower_expr(lowerer, expression, columns, Some(DataType::Text)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TypedExpr {
        data_type: DataType::Text,
        nullable: arguments.iter().any(|argument| argument.nullable),
        kind: ExprKind::ScalarFunction {
            function: ScalarFunction::Concat,
            arguments,
        },
    })
}

fn lower_if(
    lowerer: &mut Lowerer<'_>,
    condition: &SqlExpr,
    then_result: &SqlExpr,
    else_result: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let condition = lower_expr(lowerer, condition, columns, Some(DataType::Boolean))?;
    let data_type = common_expression_type(lowerer, &[then_result, else_result], columns)?;
    let then_result = lower_coerced(lowerer, then_result, columns, data_type)?;
    let else_result = lower_coerced(lowerer, else_result, columns, data_type)?;
    Ok(TypedExpr {
        data_type,
        nullable: then_result.nullable || else_result.nullable,
        kind: ExprKind::Case {
            branches: vec![(condition, then_result)],
            else_result: Box::new(else_result),
        },
    })
}

fn lower_case(
    lowerer: &mut Lowerer<'_>,
    operand: Option<&SqlExpr>,
    conditions: &[sqlparser::ast::CaseWhen],
    else_result: Option<&SqlExpr>,
    columns: &[ColumnMeta],
    expected: Option<DataType>,
) -> Result<TypedExpr, UnsupportedReason> {
    if conditions.is_empty() {
        return Err(type_error("CASE requires at least one WHEN branch"));
    }
    let result_expressions = conditions
        .iter()
        .map(|branch| &branch.result)
        .chain(else_result)
        .collect::<Vec<_>>();
    let data_type = match expected {
        Some(expected) => expected,
        None => common_expression_type(lowerer, &result_expressions, columns)?,
    };
    let mut branches = Vec::with_capacity(conditions.len());
    for branch in conditions {
        let condition = match operand {
            Some(operand) => lower_comparison(
                lowerer,
                operand,
                &BinaryOperator::Eq,
                &branch.condition,
                columns,
            )?,
            None => lower_expr(lowerer, &branch.condition, columns, Some(DataType::Boolean))?,
        };
        let result = lower_coerced(lowerer, &branch.result, columns, data_type)?;
        branches.push((condition, result));
    }
    let else_result = match else_result {
        Some(expression) => lower_coerced(lowerer, expression, columns, data_type)?,
        None => TypedExpr::literal(Value::Null, data_type, true),
    };
    Ok(TypedExpr {
        data_type,
        nullable: else_result.nullable || branches.iter().any(|(_, result)| result.nullable),
        kind: ExprKind::Case {
            branches,
            else_result: Box::new(else_result),
        },
    })
}

fn common_expression_type(
    lowerer: &mut Lowerer<'_>,
    expressions: &[&SqlExpr],
    columns: &[ColumnMeta],
) -> Result<DataType, UnsupportedReason> {
    let mut result = None;
    for expression in expressions {
        let current = infer_type(lowerer, expression, columns)?;
        if let Some(current) = current {
            result = match result {
                None => Some(current),
                Some(existing) if existing == current => Some(existing),
                Some(DataType::Integer) if current == DataType::Numeric => Some(DataType::Numeric),
                Some(DataType::Numeric) if current == DataType::Integer => Some(DataType::Numeric),
                _ => {
                    return Err(type_error(
                        "CASE/COALESCE result expressions have incompatible types",
                    ));
                }
            };
        }
    }
    Ok(result.unwrap_or(DataType::Text))
}

fn lower_null_safe_comparison(
    lowerer: &mut Lowerer<'_>,
    left: &SqlExpr,
    right: &SqlExpr,
    columns: &[ColumnMeta],
    distinct: bool,
) -> Result<TypedExpr, UnsupportedReason> {
    let operand_type = comparison_operand_type(
        left,
        infer_type(lowerer, left, columns)?,
        right,
        infer_type(lowerer, right, columns)?,
    )?;
    let left = lower_expr(lowerer, left, columns, Some(operand_type))?;
    let right = lower_expr(lowerer, right, columns, Some(operand_type))?;
    let equal = TypedExpr {
        data_type: DataType::Boolean,
        nullable: left.nullable || right.nullable,
        kind: ExprKind::Compare {
            op: CompareOp::Equal,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
    };
    let known_equal = TypedExpr {
        data_type: DataType::Boolean,
        nullable: false,
        kind: ExprKind::Coalesce(vec![
            equal,
            TypedExpr::literal(Value::Boolean(false), DataType::Boolean, false),
        ]),
    };
    let both_null = TypedExpr {
        data_type: DataType::Boolean,
        nullable: false,
        kind: ExprKind::And(
            Box::new(TypedExpr {
                data_type: DataType::Boolean,
                nullable: false,
                kind: ExprKind::IsNull(Box::new(left)),
            }),
            Box::new(TypedExpr {
                data_type: DataType::Boolean,
                nullable: false,
                kind: ExprKind::IsNull(Box::new(right)),
            }),
        ),
    };
    let not_distinct = TypedExpr {
        data_type: DataType::Boolean,
        nullable: false,
        kind: ExprKind::Or(Box::new(known_equal), Box::new(both_null)),
    };
    Ok(if distinct {
        TypedExpr {
            data_type: DataType::Boolean,
            nullable: false,
            kind: ExprKind::Not(Box::new(not_distinct)),
        }
    } else {
        not_distinct
    })
}

fn lower_comparison(
    lowerer: &mut Lowerer<'_>,
    left: &SqlExpr,
    operator: &BinaryOperator,
    right: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    let left_type = infer_type(lowerer, left, columns)?;
    let right_type = infer_type(lowerer, right, columns)?;
    let operand_type = comparison_operand_type(left, left_type, right, right_type)?;
    if operand_type == DataType::Boolean
        && !matches!(operator, BinaryOperator::Eq | BinaryOperator::NotEq)
    {
        return Err(type_error(
            "boolean values only support equality and inequality comparisons",
        ));
    }
    let left = lower_expr(lowerer, left, columns, Some(operand_type))?;
    let right = lower_expr(lowerer, right, columns, Some(operand_type))?;
    let nullable = left.nullable || right.nullable;
    let op = match operator {
        BinaryOperator::Eq => CompareOp::Equal,
        BinaryOperator::NotEq => CompareOp::NotEqual,
        BinaryOperator::Lt => CompareOp::Less,
        BinaryOperator::LtEq => CompareOp::LessOrEqual,
        BinaryOperator::Gt => CompareOp::Greater,
        BinaryOperator::GtEq => CompareOp::GreaterOrEqual,
        _ => unreachable!("the caller only passes comparison operators"),
    };
    Ok(TypedExpr {
        data_type: DataType::Boolean,
        nullable,
        kind: ExprKind::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        },
    })
}

fn infer_type(
    lowerer: &mut Lowerer<'_>,
    expression: &SqlExpr,
    columns: &[ColumnMeta],
) -> Result<Option<DataType>, UnsupportedReason> {
    match expression {
        SqlExpr::Identifier(ident) => {
            let name = identifier(ident, "column or clause alias")?;
            let aliases = lowerer
                .clause_aliases
                .iter()
                .filter(|(alias, _)| alias == &name)
                .map(|(_, expression)| expression.data_type)
                .collect::<Vec<_>>();
            match aliases.as_slice() {
                [data_type] => Ok(Some(*data_type)),
                [] => Ok(Some(
                    match resolve_scoped_column(expression, columns, &lowerer.outer_scopes)? {
                        ScopedColumn::Local(_, column) | ScopedColumn::Outer { column, .. } => {
                            column.data_type
                        }
                    },
                )),
                _ => Err(unsupported(
                    UnsupportedKind::NameResolution,
                    format!("ambiguous SELECT alias `{name}`"),
                )),
            }
        }
        SqlExpr::CompoundIdentifier(_) => Ok(Some(
            match resolve_scoped_column(expression, columns, &lowerer.outer_scopes)? {
                ScopedColumn::Local(_, column) | ScopedColumn::Outer { column, .. } => {
                    column.data_type
                }
            },
        )),
        SqlExpr::Value(value) => match &value.value {
            SqlValue::Number(number, _) if number.contains('.') => Ok(Some(DataType::Numeric)),
            SqlValue::Number(_, _) => Ok(Some(DataType::Integer)),
            SqlValue::Boolean(_) => Ok(Some(DataType::Boolean)),
            SqlValue::Null => Ok(None),
            SqlValue::SingleQuotedString(_) => Ok(None),
            _ => Err(sql_unsupported("this literal form is unsupported")),
        },
        SqlExpr::TypedString(value) => Ok(Some(sql_data_type(&value.data_type)?)),
        SqlExpr::Interval(_) => Ok(Some(DataType::Integer)),
        SqlExpr::Nested(inner) => infer_type(lowerer, inner, columns),
        SqlExpr::UnaryOp {
            op: UnaryOperator::Not,
            ..
        }
        | SqlExpr::BinaryOp {
            op:
                BinaryOperator::And
                | BinaryOperator::Or
                | BinaryOperator::Eq
                | BinaryOperator::NotEq
                | BinaryOperator::Lt
                | BinaryOperator::LtEq
                | BinaryOperator::Gt
                | BinaryOperator::GtEq
                | BinaryOperator::Spaceship,
            ..
        }
        | SqlExpr::IsTrue(_)
        | SqlExpr::IsNotTrue(_)
        | SqlExpr::IsFalse(_)
        | SqlExpr::IsNotFalse(_)
        | SqlExpr::IsNull(_)
        | SqlExpr::IsNotNull(_)
        | SqlExpr::IsUnknown(_)
        | SqlExpr::IsNotUnknown(_)
        | SqlExpr::IsDistinctFrom(_, _)
        | SqlExpr::IsNotDistinctFrom(_, _)
        | SqlExpr::Like { .. }
        | SqlExpr::InList { .. }
        | SqlExpr::InSubquery { .. }
        | SqlExpr::AllOp { .. }
        | SqlExpr::AnyOp { .. }
        | SqlExpr::Exists { .. }
        | SqlExpr::Between { .. } => Ok(Some(DataType::Boolean)),
        SqlExpr::BinaryOp {
            left,
            op:
                op @ (BinaryOperator::Plus
                | BinaryOperator::Minus
                | BinaryOperator::Multiply
                | BinaryOperator::Divide
                | BinaryOperator::Modulo),
            right,
        } => Ok(Some(
            lower_arithmetic(lowerer, left, op, right, columns)?.data_type,
        )),
        SqlExpr::BinaryOp {
            op: BinaryOperator::StringConcat,
            ..
        } => Ok(Some(DataType::Text)),
        SqlExpr::UnaryOp {
            op: UnaryOperator::Plus | UnaryOperator::Minus,
            expr,
        } => infer_type(lowerer, expr, columns),
        SqlExpr::Floor { .. } | SqlExpr::Ceil { .. } => Ok(Some(DataType::Integer)),
        SqlExpr::Extract { .. } => Ok(Some(DataType::Integer)),
        SqlExpr::Substring { .. } => Ok(Some(DataType::Text)),
        SqlExpr::Function(function) => {
            Ok(Some(lower_function(lowerer, function, columns)?.data_type))
        }
        SqlExpr::Case {
            operand,
            conditions,
            else_result,
            ..
        } => Ok(Some(
            lower_case(
                lowerer,
                operand.as_deref(),
                conditions,
                else_result.as_deref(),
                columns,
                None,
            )?
            .data_type,
        )),
        SqlExpr::Cast { data_type, .. } => {
            Ok(Some(cast_data_type(data_type, lowerer.mysql_coercions)?))
        }
        SqlExpr::Subquery(subquery) => {
            let query = lowerer.lower_subquery(subquery, columns)?;
            let [column] = query.columns.as_slice() else {
                return Err(type_error(
                    "a scalar subquery must return exactly one column",
                ));
            };
            Ok(Some(column.data_type))
        }
        _ => Err(sql_unsupported(format!(
            "unsupported expression `{expression}`"
        ))),
    }
}

fn lower_day_interval(
    lowerer: &mut Lowerer<'_>,
    interval: &sqlparser::ast::Interval,
    columns: &[ColumnMeta],
) -> Result<TypedExpr, UnsupportedReason> {
    if interval.leading_field != Some(DateTimeField::Day)
        || interval.last_field.is_some()
        || interval.fractional_seconds_precision.is_some()
    {
        return Err(sql_unsupported(
            "only single-field DAY intervals are supported",
        ));
    }
    if let SqlExpr::Value(value) = interval.value.as_ref()
        && let SqlValue::SingleQuotedString(value) = &value.value
    {
        return Ok(TypedExpr::literal(
            Value::Integer(parse_integer(value.trim(), false)?),
            DataType::Integer,
            false,
        ));
    }
    lower_expr(
        lowerer,
        interval.value.as_ref(),
        columns,
        Some(DataType::Integer),
    )
}

fn lower_literal_with_coercions(
    value: &SqlValue,
    expected: Option<DataType>,
    mysql_coercions: bool,
) -> Result<TypedExpr, UnsupportedReason> {
    if mysql_coercions {
        match (value, expected) {
            (SqlValue::Number(number, _), Some(DataType::Boolean)) => {
                let numeric = parse_numeric(number)?;
                return Ok(TypedExpr::literal(
                    Value::Boolean(numeric.numerator() != 0),
                    DataType::Boolean,
                    false,
                ));
            }
            (SqlValue::Number(number, _), Some(DataType::Integer)) if number.contains('.') => {
                let numeric = parse_numeric(number)?;
                if numeric.denominator() == 1 {
                    return Ok(TypedExpr::literal(
                        Value::Integer(numeric.numerator()),
                        DataType::Integer,
                        false,
                    ));
                }
            }
            (SqlValue::SingleQuotedString(value), Some(DataType::Integer)) => {
                let integer = value.trim().parse::<i64>().map_err(|_| {
                    type_error(format!("string literal `{value}` is not an exact integer"))
                })?;
                return Ok(TypedExpr::literal(
                    Value::Integer(integer),
                    DataType::Integer,
                    false,
                ));
            }
            (SqlValue::SingleQuotedString(value), Some(DataType::Boolean)) => {
                let numeric = parse_numeric(value.trim())?;
                return Ok(TypedExpr::literal(
                    Value::Boolean(numeric.numerator() != 0),
                    DataType::Boolean,
                    false,
                ));
            }
            _ => {}
        }
    }
    lower_literal(value, expected)
}

fn lower_literal(
    value: &SqlValue,
    expected: Option<DataType>,
) -> Result<TypedExpr, UnsupportedReason> {
    match value {
        SqlValue::Number(number, _) => Ok(TypedExpr::literal(
            match expected {
                Some(DataType::Boolean) if number == "0" || number == "1" => {
                    Value::Boolean(number == "1")
                }
                Some(DataType::Numeric) => Value::Numeric(parse_numeric(number)?),
                _ if number.contains('.') => Value::Numeric(parse_numeric(number)?),
                _ => Value::Integer(parse_integer(number, false)?),
            },
            match expected {
                Some(DataType::Boolean) if number == "0" || number == "1" => DataType::Boolean,
                Some(DataType::Numeric) => DataType::Numeric,
                _ if number.contains('.') => DataType::Numeric,
                _ => DataType::Integer,
            },
            false,
        )),
        SqlValue::Boolean(value) => Ok(TypedExpr::literal(
            Value::Boolean(*value),
            DataType::Boolean,
            false,
        )),
        SqlValue::Null => {
            let data_type =
                expected.ok_or_else(|| type_error("a projected NULL needs a type context"))?;
            Ok(TypedExpr::literal(Value::Null, data_type, true))
        }
        SqlValue::SingleQuotedString(value) => {
            let data_type = expected.unwrap_or(DataType::Text);
            let value = parse_string_value(value, data_type)?;
            Ok(TypedExpr::literal(value, data_type, false))
        }
        _ => Err(sql_unsupported("this literal form is unsupported")),
    }
}

fn lower_typed_string(value: &sqlparser::ast::TypedString) -> Result<TypedExpr, UnsupportedReason> {
    let data_type = sql_data_type(&value.data_type)?;
    let SqlValue::SingleQuotedString(value) = &value.value.value else {
        return Err(sql_unsupported(
            "typed date/time/numeric literals must use single quotes",
        ));
    };
    Ok(TypedExpr::literal(
        parse_string_value(value, data_type)?,
        data_type,
        false,
    ))
}

fn cast_data_type(
    data_type: &SqlDataType,
    mysql_coercions: bool,
) -> Result<DataType, UnsupportedReason> {
    if mysql_coercions
        && matches!(
            data_type,
            SqlDataType::Float(_)
                | SqlDataType::FloatUnsigned(_)
                | SqlDataType::Float4
                | SqlDataType::Float8
                | SqlDataType::Float32
                | SqlDataType::Float64
                | SqlDataType::Real
                | SqlDataType::RealUnsigned
                | SqlDataType::Double(_)
                | SqlDataType::DoubleUnsigned(_)
                | SqlDataType::DoublePrecision
                | SqlDataType::DoublePrecisionUnsigned
        )
    {
        return Ok(DataType::Numeric);
    }
    sql_data_type(data_type)
}

fn sql_data_type(data_type: &SqlDataType) -> Result<DataType, UnsupportedReason> {
    match data_type {
        SqlDataType::Date => Ok(DataType::Date),
        SqlDataType::Time(_, _) => Ok(DataType::Time),
        SqlDataType::Numeric(_)
        | SqlDataType::Decimal(_)
        | SqlDataType::DecimalUnsigned(_)
        | SqlDataType::Dec(_)
        | SqlDataType::DecUnsigned(_) => Ok(DataType::Numeric),
        SqlDataType::TinyInt(_)
        | SqlDataType::SmallInt(_)
        | SqlDataType::Int(_)
        | SqlDataType::Int2(_)
        | SqlDataType::Int4(_)
        | SqlDataType::Int8(_)
        | SqlDataType::Integer(_)
        | SqlDataType::BigInt(_) => Ok(DataType::Integer),
        SqlDataType::Boolean | SqlDataType::Bool => Ok(DataType::Boolean),
        SqlDataType::Character(_)
        | SqlDataType::Char(_)
        | SqlDataType::CharacterVarying(_)
        | SqlDataType::CharVarying(_)
        | SqlDataType::Varchar(_)
        | SqlDataType::Nvarchar(_) => Ok(DataType::Text),
        _ => Err(sql_unsupported(format!(
            "typed literal data type `{data_type}` is unsupported"
        ))),
    }
}

fn parse_string_value(value: &str, data_type: DataType) -> Result<Value, UnsupportedReason> {
    match data_type {
        DataType::Text => Ok(Value::Text(value.to_owned())),
        DataType::Enum => Ok(Value::Enum(value.to_owned())),
        DataType::Date => DateValue::from_str(value.trim())
            .map(Value::Date)
            .map_err(|error| type_error(format!("invalid date literal `{value}`: {error}"))),
        DataType::Time => TimeValue::from_str(value.trim())
            .map(Value::Time)
            .map_err(|error| type_error(format!("invalid time literal `{value}`: {error}"))),
        DataType::Numeric => parse_numeric(value).map(Value::Numeric),
        DataType::Integer | DataType::Boolean => Err(type_error(format!(
            "string literal `{value}` cannot be used as {data_type:?}"
        ))),
    }
}

fn parse_numeric(number: &str) -> Result<ExactNumeric, UnsupportedReason> {
    ExactNumeric::from_str(number)
        .map_err(|error| type_error(format!("invalid exact numeric literal `{number}`: {error}")))
}

fn is_string_literal(expression: &SqlExpr) -> bool {
    matches!(
        expression,
        SqlExpr::Value(value) if matches!(value.value, SqlValue::SingleQuotedString(_))
    )
}

fn comparison_operand_type(
    left: &SqlExpr,
    left_type: Option<DataType>,
    right: &SqlExpr,
    right_type: Option<DataType>,
) -> Result<DataType, UnsupportedReason> {
    match (left_type, right_type) {
        (Some(left_type), Some(right_type)) if left_type == right_type => Ok(left_type),
        (Some(data_type), None) | (None, Some(data_type)) => Ok(data_type),
        (None, None) if is_string_literal(left) || is_string_literal(right) => Ok(DataType::Text),
        (Some(DataType::Numeric), Some(DataType::Integer)) if is_integer_literal(right) => {
            Ok(DataType::Numeric)
        }
        (Some(DataType::Integer), Some(DataType::Numeric)) if is_integer_literal(left) => {
            Ok(DataType::Numeric)
        }
        (Some(DataType::Boolean), Some(DataType::Integer)) if is_boolean_integer_literal(right) => {
            Ok(DataType::Boolean)
        }
        (Some(DataType::Integer), Some(DataType::Boolean)) if is_boolean_integer_literal(left) => {
            Ok(DataType::Boolean)
        }
        _ => Err(type_error(format!(
            "comparison operands have different types in `{left}` and `{right}`"
        ))),
    }
}

fn is_integer_literal(expression: &SqlExpr) -> bool {
    matches!(
        expression,
        SqlExpr::Value(value)
            if matches!(&value.value, SqlValue::Number(number, _) if !number.contains('.'))
    )
}

fn is_boolean_integer_literal(expression: &SqlExpr) -> bool {
    matches!(
        expression,
        SqlExpr::Value(value)
            if matches!(&value.value, SqlValue::Number(number, _) if number == "0" || number == "1")
    )
}

fn parse_integer(number: &str, negative: bool) -> Result<i64, UnsupportedReason> {
    let magnitude = number.parse::<i128>().map_err(|_| {
        type_error(format!(
            "numeric literal `{number}` is not a supported 64-bit integer"
        ))
    })?;
    let signed = if negative {
        magnitude.checked_neg()
    } else {
        Some(magnitude)
    }
    .ok_or_else(|| type_error(format!("integer literal `-{number}` is out of range")))?;
    i64::try_from(signed).map_err(|_| {
        type_error(format!(
            "integer literal `{}{number}` is out of the 64-bit range",
            if negative { "-" } else { "" }
        ))
    })
}

fn parse_slice_value(expression: &SqlExpr, clause: &str) -> Result<usize, UnsupportedReason> {
    let SqlExpr::Value(value) = expression else {
        return Err(sql_unsupported(format!(
            "{clause} must be a non-negative integer literal"
        )));
    };
    let SqlValue::Number(value, _) = &value.value else {
        return Err(sql_unsupported(format!(
            "{clause} must be a non-negative integer literal"
        )));
    };
    value.parse::<usize>().map_err(|_| {
        type_error(format!(
            "{clause} literal `{value}` is outside the supported range"
        ))
    })
}

enum ScopedColumn<'columns> {
    Local(usize, &'columns ColumnMeta),
    Outer {
        depth: usize,
        index: usize,
        column: &'columns ColumnMeta,
    },
}

fn resolve_scoped_column<'columns>(
    expression: &SqlExpr,
    columns: &'columns [ColumnMeta],
    outer_scopes: &'columns [Vec<ColumnMeta>],
) -> Result<ScopedColumn<'columns>, UnsupportedReason> {
    if let Some((index, column)) = resolve_column_in_scope(expression, columns)? {
        return Ok(ScopedColumn::Local(index, column));
    }
    for (depth, scope) in outer_scopes.iter().rev().enumerate() {
        if let Some((index, column)) = resolve_column_in_scope(expression, scope)? {
            return Ok(ScopedColumn::Outer {
                depth,
                index,
                column,
            });
        }
    }
    let (qualifier, name) = column_name(expression)?;
    Err(unknown_column(qualifier.as_deref(), &name))
}

fn resolve_column_in_scope<'columns>(
    expression: &SqlExpr,
    columns: &'columns [ColumnMeta],
) -> Result<Option<(usize, &'columns ColumnMeta)>, UnsupportedReason> {
    let (qualifier, name) = column_name(expression)?;
    let matches = columns
        .iter()
        .enumerate()
        .filter(|(_, column)| {
            let primary_matches = column.canonical_name == name
                && (qualifier.is_some() || column.unqualified_visible)
                && qualifier
                    .as_ref()
                    .is_none_or(|qualifier| column.qualifier.as_ref() == Some(qualifier));
            let source_matches = qualifier.as_ref().is_some_and(|qualifier| {
                column.source_qualifier.as_ref() == Some(qualifier)
                    && column.source_name.as_ref() == Some(&name)
            });
            primary_matches || source_matches
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [(index, column)] => Ok(Some((*index, *column))),
        [] => Ok(None),
        _ => Err(unsupported(
            UnsupportedKind::NameResolution,
            format!("ambiguous column `{name}`"),
        )),
    }
}

fn column_name(expression: &SqlExpr) -> Result<(Option<String>, String), UnsupportedReason> {
    Ok(match expression {
        SqlExpr::Identifier(name) => (None, identifier(name, "column")?),
        SqlExpr::CompoundIdentifier(parts) if parts.len() == 2 => (
            Some(identifier(&parts[0], "table qualifier")?),
            identifier(&parts[1], "column")?,
        ),
        SqlExpr::CompoundIdentifier(_) => {
            return Err(sql_unsupported(
                "only table.column qualified names are supported",
            ));
        }
        _ => {
            return Err(unsupported(
                UnsupportedKind::Internal,
                "column resolution received a non-column expression",
            ));
        }
    })
}

fn unknown_column(qualifier: Option<&str>, name: &str) -> UnsupportedReason {
    unsupported(
        UnsupportedKind::NameResolution,
        match qualifier {
            Some(qualifier) => format!("unknown column `{qualifier}.{name}`"),
            None => format!("unknown column `{name}`"),
        },
    )
}

fn single_object_name(name: &ObjectName, context: &str) -> Result<String, UnsupportedReason> {
    let [ObjectNamePart::Identifier(ident)] = name.0.as_slice() else {
        return Err(sql_unsupported(format!(
            "qualified or computed {context} names are unsupported"
        )));
    };
    identifier(ident, context)
}

fn identifier(identifier: &Ident, context: &str) -> Result<String, UnsupportedReason> {
    Ok(canonical_name(&display_identifier(identifier, context)?))
}

fn display_identifier(identifier: &Ident, context: &str) -> Result<String, UnsupportedReason> {
    if identifier.quote_style.is_some() {
        return Err(sql_unsupported(format!(
            "quoted {context} identifiers are unsupported"
        )));
    }
    Ok(identifier.value.clone())
}

fn type_error(message: impl Into<String>) -> UnsupportedReason {
    unsupported(UnsupportedKind::TypeError, message)
}

fn sql_unsupported(message: impl Into<String>) -> UnsupportedReason {
    unsupported(UnsupportedKind::UnsupportedSql, message)
}

fn unsupported(kind: UnsupportedKind, message: impl Into<String>) -> UnsupportedReason {
    UnsupportedReason::new(kind, message)
}
