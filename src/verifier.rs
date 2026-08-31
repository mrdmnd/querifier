use std::time::Duration;

use z3::{Config, SatResult, Solver, with_z3_config};

use crate::concrete::{ConcreteDatabase, bags_equal, evaluate, lists_equal, validate_database};
use crate::counterexample::{Counterexample, CounterexampleTable};
use crate::ir::TypedQuery;
use crate::outcome::{UnsupportedKind, UnsupportedReason, VerificationResult};
use crate::query::parse_query;
use crate::schema::Schema;
use crate::symbolic::{bag_equal, build_database, encode_query, extract_database, list_equal};

/// Controls how a top-level `ORDER BY` affects query equivalence.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OrderingPolicy {
    /// Require both queries to have an ordered result contract.
    #[default]
    Strict,
    /// Ignore top-level `ORDER BY` and compare result bags when neither query is sliced.
    ///
    /// This treats top-level ordering as presentation for all unsliced queries, including when
    /// both queries have `ORDER BY`. `LIMIT` and `OFFSET` are never relaxed by this policy.
    IgnoreTopLevelOrder,
}

/// Controls validation of non-aggregate expressions in grouped queries.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum GroupingPolicy {
    /// Require every non-aggregate expression to be grouped or functionally determined.
    #[default]
    Strict,
    /// Evaluate otherwise ungrouped expressions against the first row in each bounded group.
    ///
    /// This models the deterministic representative-row behavior used by the VeriEQL corpus. It
    /// is an explicit compatibility profile, not a portable SQL guarantee.
    PermissiveFirstRow,
}

/// Controls implicit scalar coercions accepted while lowering SQL.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CoercionPolicy {
    /// Require operands and predicates to have their declared SQL types.
    #[default]
    Strict,
    /// Accept exact MySQL-style numeric truthiness and integral literal coercions.
    ///
    /// Approximate `FLOAT`/`DOUBLE` casts are idealized as exact `NUMERIC` values, and canonical
    /// year-month-day `DATE_FORMAT` calls retain their source `DATE` representation.
    MySqlCompatible,
}

/// Resource limits for a verification attempt.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifyOptions {
    /// Maximum number of live rows represented for each base table.
    pub max_rows_per_table: usize,
    /// Wall-clock limit passed to Z3 for each solver check.
    pub timeout: Duration,
    /// Maximum number of symbolic rows produced by a query's Cartesian product.
    pub max_intermediate_rows: usize,
    /// Policy for a top-level `ORDER BY` present on only one side.
    pub ordering_policy: OrderingPolicy,
    /// Policy for non-aggregate expressions in grouped queries.
    pub grouping_policy: GroupingPolicy,
    /// Policy for implicit scalar coercions.
    pub coercion_policy: CoercionPolicy,
}

impl Default for VerifyOptions {
    fn default() -> Self {
        Self {
            max_rows_per_table: 2,
            timeout: Duration::from_secs(5),
            max_intermediate_rows: 10_000,
            ordering_policy: OrderingPolicy::Strict,
            grouping_policy: GroupingPolicy::Strict,
            coercion_policy: CoercionPolicy::Strict,
        }
    }
}

/// A reusable bounded SQL equivalence verifier.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Verifier {
    options: VerifyOptions,
}

impl Verifier {
    #[must_use]
    pub const fn new(options: VerifyOptions) -> Self {
        Self { options }
    }

    #[must_use]
    pub const fn options(&self) -> &VerifyOptions {
        &self.options
    }

    /// Searches for a database that makes the two typed query result bags differ.
    #[must_use]
    pub fn verify(&self, schema: &Schema, left_sql: &str, right_sql: &str) -> VerificationResult {
        if let Err(reason) = self.validate_inputs(schema) {
            return reason.into();
        }

        let left = match parse_query(
            schema,
            left_sql,
            self.options.max_rows_per_table,
            self.options.max_intermediate_rows,
            self.options.ordering_policy == OrderingPolicy::IgnoreTopLevelOrder,
            self.options.grouping_policy == GroupingPolicy::PermissiveFirstRow,
            self.options.coercion_policy == CoercionPolicy::MySqlCompatible,
        ) {
            Ok(query) => query,
            Err(reason) => return reason.into(),
        };
        let right = match parse_query(
            schema,
            right_sql,
            self.options.max_rows_per_table,
            self.options.max_intermediate_rows,
            self.options.ordering_policy == OrderingPolicy::IgnoreTopLevelOrder,
            self.options.grouping_policy == GroupingPolicy::PermissiveFirstRow,
            self.options.coercion_policy == CoercionPolicy::MySqlCompatible,
        ) {
            Ok(query) => query,
            Err(reason) => return reason.into(),
        };

        let left_types = left.output_types().collect::<Vec<_>>();
        let right_types = right.output_types().collect::<Vec<_>>();
        if left_types != right_types {
            return self.build_counterexample(
                schema,
                &left,
                &right,
                ConcreteDatabase {
                    tables: vec![Vec::new(); schema.tables.len()],
                },
                false,
            );
        }
        let compare_as_list = match (
            left.requires_list_comparison(),
            right.requires_list_comparison(),
        ) {
            (left_list, right_list) if left_list == right_list => left_list,
            _ if self.options.ordering_policy == OrderingPolicy::IgnoreTopLevelOrder
                && !left.semantics.sliced
                && !right.semantics.sliced =>
            {
                false
            }
            _ => {
                return UnsupportedReason::new(
                    UnsupportedKind::UnsupportedSql,
                    "ordered/sliced results cannot be compared with an unordered result",
                )
                .into();
            }
        };

        let mut config = Config::new();
        let timeout_millis = u64::try_from(self.options.timeout.as_millis()).unwrap_or(u64::MAX);
        config.set_timeout_msec(timeout_millis);
        with_z3_config(&config, || {
            self.verify_typed(schema, &left, &right, compare_as_list)
        })
    }

    fn validate_inputs(&self, schema: &Schema) -> Result<(), UnsupportedReason> {
        schema.validate()?;
        if self.options.max_rows_per_table == 0 {
            return Err(UnsupportedReason::new(
                UnsupportedKind::ComplexityLimit,
                "max_rows_per_table must be greater than zero",
            ));
        }
        if self.options.max_intermediate_rows == 0 {
            return Err(UnsupportedReason::new(
                UnsupportedKind::ComplexityLimit,
                "max_intermediate_rows must be greater than zero",
            ));
        }
        if self.options.timeout.is_zero() {
            return Err(UnsupportedReason::new(
                UnsupportedKind::Solver,
                "the solver timeout must be greater than zero",
            ));
        }
        Ok(())
    }

    fn verify_typed(
        &self,
        schema: &Schema,
        left: &TypedQuery,
        right: &TypedQuery,
        compare_as_list: bool,
    ) -> VerificationResult {
        let (database, schema_constraints) =
            match build_database(schema, self.options.max_rows_per_table) {
                Ok(encoded) => encoded,
                Err(reason) => return reason.into(),
            };

        let solver = Solver::new();
        for constraint in &schema_constraints {
            solver.assert(constraint);
        }
        match solver.check() {
            SatResult::Unsat => {
                return UnsupportedReason::new(
                    UnsupportedKind::InvalidSchema,
                    "schema integrity constraints are inconsistent",
                )
                .into();
            }
            SatResult::Unknown => return solver_unknown(&solver).into(),
            SatResult::Sat => {}
        }

        let left_relation = match encode_query(left, &database) {
            Ok(relation) => relation,
            Err(reason) => return reason.into(),
        };
        let right_relation = match encode_query(right, &database) {
            Ok(relation) => relation,
            Err(reason) => return reason.into(),
        };
        let equal = match if compare_as_list {
            list_equal(&left_relation, &right_relation)
        } else {
            bag_equal(&left_relation, &right_relation)
        } {
            Ok(equal) => equal,
            Err(reason) => return reason.into(),
        };

        solver.assert(equal.not());

        match solver.check() {
            SatResult::Unsat => VerificationResult::True {
                bound: self.options.max_rows_per_table,
            },
            SatResult::Unknown => solver_unknown(&solver).into(),
            SatResult::Sat => {
                let Some(model) = solver.get_model() else {
                    return internal("Z3 reported SAT without a model").into();
                };
                let concrete = match extract_database(schema, &database, &model) {
                    Ok(database) => database,
                    Err(reason) => return reason.into(),
                };
                self.build_counterexample(schema, left, right, concrete, compare_as_list)
            }
        }
    }

    fn build_counterexample(
        &self,
        schema: &Schema,
        left: &TypedQuery,
        right: &TypedQuery,
        database: ConcreteDatabase,
        compare_as_list: bool,
    ) -> VerificationResult {
        if let Err(reason) = validate_database(schema, &database) {
            return reason.into();
        }
        let left_result = match evaluate(left, &database) {
            Ok(result) => result,
            Err(reason) => return reason.into(),
        };
        let right_result = match evaluate(right, &database) {
            Ok(result) => result,
            Err(reason) => return reason.into(),
        };
        let replay_equal = if compare_as_list {
            lists_equal(&left_result, &right_result)
        } else {
            bags_equal(&left_result, &right_result)
        };
        if replay_equal {
            return internal("the extracted Z3 model did not reproduce a query result difference")
                .into();
        }

        let tables = schema
            .tables
            .iter()
            .zip(database.tables)
            .map(|(table, rows)| CounterexampleTable {
                name: table.name.clone(),
                columns: table
                    .columns
                    .iter()
                    .map(|column| column.name.clone())
                    .collect(),
                rows,
            })
            .collect();
        VerificationResult::False {
            counterexample: Counterexample {
                tables,
                left_result,
                right_result,
            },
        }
    }
}

fn solver_unknown(solver: &Solver) -> UnsupportedReason {
    UnsupportedReason::new(
        UnsupportedKind::Solver,
        format!(
            "Z3 could not decide the formula: {}",
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown reason".to_owned())
        ),
    )
}

fn internal(message: impl Into<String>) -> UnsupportedReason {
    UnsupportedReason::new(UnsupportedKind::Internal, message)
}
