use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use z3::ast::Bool;
use z3::{Config, SatResult, Solver, with_z3_config};

use crate::concrete::{ConcreteDatabase, bags_equal, evaluate, lists_equal, validate_database};
use crate::counterexample::{Counterexample, CounterexampleTable};
use crate::ir::TypedQuery;
use crate::metrics::{Counter, MetricsRecorder, Phase, VerificationReport, measure};
use crate::outcome::{UnsupportedKind, UnsupportedReason, VerificationResult};
use crate::query::parse_query;
use crate::schema::Schema;
use crate::symbolic::{
    SymbolicDatabase, bag_equal, build_database, encode_query, extract_database, list_equal,
};

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

/// Order used when solving a set of row bounds.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum BoundSearchOrder {
    /// Solve the largest unresolved bound first. A proof resolves every smaller bound.
    #[default]
    LargestFirst,
    /// Solve the smallest unresolved bound first. A counterexample resolves every larger bound.
    SmallestFirst,
}

/// Result for one requested bound, including the bound that performed the solver work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundVerification {
    pub bound: usize,
    pub source_bound: usize,
    pub result: VerificationResult,
}

impl BoundVerification {
    /// Whether this bound was solved directly rather than inferred monotonically.
    #[must_use]
    pub const fn was_solved(&self) -> bool {
        self.bound == self.source_bound
    }
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

#[derive(Clone, Copy)]
enum PairCheck {
    Assert,
    PushPop,
}

struct SolverScope<'solver> {
    solver: &'solver Solver,
}

impl Drop for SolverScope<'_> {
    fn drop(&mut self) {
        self.solver.pop(1);
    }
}

/// A thread-affine verification session with a pre-encoded schema and symbolic database.
///
/// Instances are only available within [`Verifier::with_prepared`] because Z3 objects
/// must remain in the context that created them. Long-running callers should periodically
/// return from `with_prepared` and create a fresh session so Z3 can release accumulated state.
#[derive(Debug)]
pub struct PreparedVerifier<'a> {
    verifier: &'a Verifier,
    schema: &'a Schema,
    database: SymbolicDatabase,
    schema_constraints: Vec<Bool>,
    solver: Solver,
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

    /// Runs multiple verifications against one prepared schema and row bound.
    ///
    /// The callback receives a session that reuses one Z3 context, symbolic base
    /// database, and schema solver. Calls on the session are serialized by the
    /// callback and isolate pair-specific assertions with solver push/pop scopes.
    /// A solver timeout rebuilds the base solver before the next pair.
    ///
    /// Z3 retains some internal state after scopes are popped. Keep batches bounded
    /// (100 heterogeneous pairs is a conservative starting point) and return from
    /// this method between batches when memory usage must remain flat. This API does
    /// not impose a hard batch limit; the caller is responsible for refreshing it.
    pub fn with_prepared<T, F>(&self, schema: &Schema, operation: F) -> Result<T, UnsupportedReason>
    where
        T: Send + Sync,
        F: FnOnce(&mut PreparedVerifier<'_>) -> T + Send + Sync,
    {
        self.validate_inputs(schema)?;
        let config = self.z3_config();
        with_z3_config(&config, || {
            let (database, schema_constraints) =
                build_database(schema, self.options.max_rows_per_table, None)?;
            let solver = Solver::new();
            for constraint in &schema_constraints {
                solver.assert(constraint);
            }
            match solver.check() {
                SatResult::Unsat => {
                    return Err(UnsupportedReason::new(
                        UnsupportedKind::InvalidSchema,
                        "schema integrity constraints are inconsistent",
                    ));
                }
                SatResult::Unknown => return Err(solver_unknown(&solver)),
                SatResult::Sat => {}
            }

            let mut prepared = PreparedVerifier {
                verifier: self,
                schema,
                database,
                schema_constraints,
                solver,
            };
            Ok(operation(&mut prepared))
        })
    }

    /// Searches for a database that makes the two typed query result bags differ.
    #[must_use]
    pub fn verify(&self, schema: &Schema, left_sql: &str, right_sql: &str) -> VerificationResult {
        self.verify_internal(schema, left_sql, right_sql, None)
    }

    /// Runs a verification with opt-in phase timings and structural counters.
    #[must_use]
    pub fn verify_with_metrics(
        &self,
        schema: &Schema,
        left_sql: &str,
        right_sql: &str,
    ) -> VerificationReport {
        let metrics = MetricsRecorder::default();
        let result = metrics.measure(Phase::Total, || {
            self.verify_internal(schema, left_sql, right_sql, Some(&metrics))
        });
        let (phases, counters) = metrics.snapshot();
        VerificationReport {
            result,
            phases,
            counters,
        }
    }

    /// Verifies multiple bounds while reusing monotonic proofs and counterexamples.
    ///
    /// The returned entries are sorted by bound. `Unsupported` outcomes are never
    /// propagated to another bound.
    pub fn verify_bounds(
        &self,
        schema: &Schema,
        left_sql: &str,
        right_sql: &str,
        bounds: &[usize],
        order: BoundSearchOrder,
    ) -> Result<Vec<BoundVerification>, UnsupportedReason> {
        if bounds.contains(&0) {
            return Err(UnsupportedReason::new(
                UnsupportedKind::ComplexityLimit,
                "verification bounds must be greater than zero",
            ));
        }
        let mut requested = bounds.to_vec();
        requested.sort_unstable();
        requested.dedup();
        let mut solve_order = requested.clone();
        if order == BoundSearchOrder::LargestFirst {
            solve_order.reverse();
        }

        let mut results = BTreeMap::new();
        for bound in solve_order {
            if results.contains_key(&bound) {
                continue;
            }
            let mut options = self.options.clone();
            options.max_rows_per_table = bound;
            let result = Self::new(options).verify(schema, left_sql, right_sql);
            results.insert(
                bound,
                BoundVerification {
                    bound,
                    source_bound: bound,
                    result: result.clone(),
                },
            );

            match result {
                VerificationResult::True { .. } => {
                    for inferred_bound in requested.iter().copied().filter(|value| *value < bound) {
                        results.entry(inferred_bound).or_insert(BoundVerification {
                            bound: inferred_bound,
                            source_bound: bound,
                            result: VerificationResult::True {
                                bound: inferred_bound,
                            },
                        });
                    }
                }
                VerificationResult::False { counterexample } => {
                    let witness_bound = counterexample
                        .tables
                        .iter()
                        .map(|table| table.rows.len())
                        .max()
                        .unwrap_or(0);
                    for inferred_bound in requested
                        .iter()
                        .copied()
                        .filter(|value| *value >= witness_bound && *value != bound)
                    {
                        results.entry(inferred_bound).or_insert(BoundVerification {
                            bound: inferred_bound,
                            source_bound: bound,
                            result: VerificationResult::False {
                                counterexample: counterexample.clone(),
                            },
                        });
                    }
                }
                VerificationResult::Unsupported { .. } => {}
            }
        }

        Ok(results.into_values().collect())
    }

    fn verify_internal(
        &self,
        schema: &Schema,
        left_sql: &str,
        right_sql: &str,
        metrics: Option<&MetricsRecorder>,
    ) -> VerificationResult {
        if let Err(reason) = self.validate_inputs(schema) {
            return reason.into();
        }

        self.with_lowered_pair(
            schema,
            left_sql,
            right_sql,
            metrics,
            |left, right, compare_as_list| {
                let config = self.z3_config();
                match metrics {
                    Some(metrics) => {
                        let context_started = Instant::now();
                        let result = with_z3_config(&config, || {
                            metrics.measure(Phase::Z3CallbackBody, || {
                                self.verify_typed(
                                    schema,
                                    left,
                                    right,
                                    compare_as_list,
                                    Some(metrics),
                                )
                            })
                        });
                        metrics.add_phase(
                            Phase::Z3ContextLifecycle,
                            context_started
                                .elapsed()
                                .saturating_sub(metrics.phase_duration(Phase::Z3CallbackBody)),
                        );
                        result
                    }
                    None => with_z3_config(&config, || {
                        self.verify_typed(schema, left, right, compare_as_list, None)
                    }),
                }
            },
        )
    }

    fn with_lowered_pair(
        &self,
        schema: &Schema,
        left_sql: &str,
        right_sql: &str,
        metrics: Option<&MetricsRecorder>,
        verify: impl FnOnce(&TypedQuery, &TypedQuery, bool) -> VerificationResult,
    ) -> VerificationResult {
        let left = match measure(metrics, Phase::LeftParseLowering, || {
            parse_query(
                schema,
                left_sql,
                self.options.max_rows_per_table,
                self.options.max_intermediate_rows,
                self.options.ordering_policy == OrderingPolicy::IgnoreTopLevelOrder,
                self.options.grouping_policy == GroupingPolicy::PermissiveFirstRow,
                self.options.coercion_policy == CoercionPolicy::MySqlCompatible,
            )
        }) {
            Ok(query) => query,
            Err(reason) => return reason.into(),
        };
        let right = match measure(metrics, Phase::RightParseLowering, || {
            parse_query(
                schema,
                right_sql,
                self.options.max_rows_per_table,
                self.options.max_intermediate_rows,
                self.options.ordering_policy == OrderingPolicy::IgnoreTopLevelOrder,
                self.options.grouping_policy == GroupingPolicy::PermissiveFirstRow,
                self.options.coercion_policy == CoercionPolicy::MySqlCompatible,
            )
        }) {
            Ok(query) => query,
            Err(reason) => return reason.into(),
        };
        if let Some(metrics) = metrics {
            metrics.set(Counter::LeftOutputWidth, left.root.columns.len());
            metrics.set(Counter::RightOutputWidth, right.root.columns.len());
        }

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
                metrics,
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
        verify(&left, &right, compare_as_list)
    }

    fn z3_config(&self) -> Config {
        let mut config = Config::new();
        let timeout_millis = u64::try_from(self.options.timeout.as_millis()).unwrap_or(u64::MAX);
        config.set_timeout_msec(timeout_millis);
        config
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
        metrics: Option<&MetricsRecorder>,
    ) -> VerificationResult {
        let (database, schema_constraints) =
            match build_database(schema, self.options.max_rows_per_table, metrics) {
                Ok(encoded) => encoded,
                Err(reason) => return reason.into(),
            };

        let solver = Solver::new();
        measure(metrics, Phase::SchemaAssertion, || {
            for constraint in &schema_constraints {
                solver.assert(constraint);
            }
        });
        match measure(metrics, Phase::SchemaSolverCheck, || solver.check()) {
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

        self.verify_pair(
            schema,
            left,
            right,
            compare_as_list,
            &database,
            &solver,
            PairCheck::Assert,
            metrics,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_pair(
        &self,
        schema: &Schema,
        left: &TypedQuery,
        right: &TypedQuery,
        compare_as_list: bool,
        database: &SymbolicDatabase,
        solver: &Solver,
        check: PairCheck,
        metrics: Option<&MetricsRecorder>,
    ) -> VerificationResult {
        if left == right {
            if let Some(metrics) = metrics {
                metrics.increment(Counter::IdenticalPlanFastPaths);
            }
            return VerificationResult::True {
                bound: self.options.max_rows_per_table,
            };
        }

        let left_relation = match measure(metrics, Phase::LeftRelationEncoding, || {
            encode_query(left, database, metrics)
        }) {
            Ok(relation) => relation,
            Err(reason) => return reason.into(),
        };
        if let Some(metrics) = metrics {
            metrics.set(Counter::LeftRelationRows, left_relation.rows.len());
        }
        let right_relation = match measure(metrics, Phase::RightRelationEncoding, || {
            encode_query(right, database, metrics)
        }) {
            Ok(relation) => relation,
            Err(reason) => return reason.into(),
        };
        if let Some(metrics) = metrics {
            metrics.set(Counter::RightRelationRows, right_relation.rows.len());
        }
        let equal = match measure(metrics, Phase::ComparisonFormulaConstruction, || {
            if compare_as_list {
                list_equal(&left_relation, &right_relation, metrics)
            } else {
                bag_equal(&left_relation, &right_relation, metrics)
            }
        }) {
            Ok(equal) => equal,
            Err(reason) => return reason.into(),
        };

        let _scope = measure(metrics, Phase::FinalAssertion, || {
            if matches!(check, PairCheck::PushPop) {
                solver.push();
                let scope = SolverScope { solver };
                solver.assert(equal.not());
                Some(scope)
            } else {
                solver.assert(equal.not());
                None
            }
        });

        let solver_result = measure(metrics, Phase::FinalSolverCheck, || match check {
            PairCheck::Assert | PairCheck::PushPop => solver.check(),
        });
        match solver_result {
            SatResult::Unsat => VerificationResult::True {
                bound: self.options.max_rows_per_table,
            },
            SatResult::Unknown => solver_unknown(solver).into(),
            SatResult::Sat => {
                match measure(metrics, Phase::ModelExtraction, || {
                    let model = solver
                        .get_model()
                        .ok_or_else(|| internal("Z3 reported SAT without a model"))?;
                    extract_database(schema, database, &model)
                }) {
                    Ok(concrete) => self.build_counterexample(
                        schema,
                        left,
                        right,
                        concrete,
                        compare_as_list,
                        metrics,
                    ),
                    Err(reason) => reason.into(),
                }
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
        metrics: Option<&MetricsRecorder>,
    ) -> VerificationResult {
        measure(metrics, Phase::ConcreteReplay, || {
            self.build_counterexample_inner(schema, left, right, database, compare_as_list)
        })
    }

    fn build_counterexample_inner(
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

impl PreparedVerifier<'_> {
    /// Verifies a query pair while reusing the prepared schema state.
    #[must_use]
    pub fn verify(&mut self, left_sql: &str, right_sql: &str) -> VerificationResult {
        self.verify_internal(left_sql, right_sql, None)
    }

    /// Verifies a query pair with per-pair timings and structural counters.
    ///
    /// Schema preparation is intentionally excluded because it occurs once before
    /// the callback passed to [`Verifier::with_prepared`].
    #[must_use]
    pub fn verify_with_metrics(&mut self, left_sql: &str, right_sql: &str) -> VerificationReport {
        let metrics = MetricsRecorder::default();
        let result = metrics.measure(Phase::Total, || {
            self.verify_internal(left_sql, right_sql, Some(&metrics))
        });
        let (phases, counters) = metrics.snapshot();
        VerificationReport {
            result,
            phases,
            counters,
        }
    }

    fn verify_internal(
        &mut self,
        left_sql: &str,
        right_sql: &str,
        metrics: Option<&MetricsRecorder>,
    ) -> VerificationResult {
        let verifier = self.verifier;
        let schema = self.schema;
        let database = &self.database;
        let solver = &self.solver;
        let result = verifier.with_lowered_pair(
            schema,
            left_sql,
            right_sql,
            metrics,
            |left, right, compare_as_list| {
                verifier.verify_pair(
                    schema,
                    left,
                    right,
                    compare_as_list,
                    database,
                    solver,
                    PairCheck::PushPop,
                    metrics,
                )
            },
        );
        if matches!(
            &result,
            VerificationResult::Unsupported { reason }
                if reason.kind == UnsupportedKind::Solver
        ) {
            self.reset_solver();
        }
        result
    }

    fn reset_solver(&mut self) {
        self.solver = Solver::new();
        for constraint in &self.schema_constraints {
            self.solver.assert(constraint);
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

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;

    #[test]
    fn solver_scope_pops_when_unwinding() {
        with_z3_config(&Config::new(), || {
            let solver = Solver::new();
            let unwind = catch_unwind(AssertUnwindSafe(|| {
                solver.push();
                let _scope = SolverScope { solver: &solver };
                solver.assert(Bool::from_bool(false));
                panic!("exercise solver-scope cleanup");
            }));

            assert!(unwind.is_err());
            assert_eq!(solver.check(), SatResult::Sat);
        });
    }
}
