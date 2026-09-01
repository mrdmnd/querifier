use std::array;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use crate::outcome::VerificationResult;

/// Timings for the major stages of one verification.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VerificationPhaseTimings {
    pub left_parse_lowering: Duration,
    pub right_parse_lowering: Duration,
    pub symbolic_database_construction: Duration,
    pub schema_constraint_construction: Duration,
    pub schema_assertion: Duration,
    pub schema_solver_check: Duration,
    pub left_relation_encoding: Duration,
    pub right_relation_encoding: Duration,
    pub comparison_formula_construction: Duration,
    pub final_assertion: Duration,
    pub final_solver_check: Duration,
    pub model_extraction: Duration,
    pub concrete_replay: Duration,
    /// Context creation, thread-local installation/restoration, and teardown.
    ///
    /// The upstream Z3 helper owns these operations as one scope, so they cannot be
    /// measured separately without changing the default context lifecycle.
    pub z3_context_lifecycle: Duration,
    pub total: Duration,
}

/// Structural work performed while constructing one verification formula.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VerificationCounters {
    pub base_rows: u64,
    pub schema_constraints: u64,
    pub unit_rows: u64,
    pub scan_rows: u64,
    pub product_rows: u64,
    pub join_rows: u64,
    pub filter_rows: u64,
    pub project_rows: u64,
    pub distinct_rows: u64,
    pub set_operation_rows: u64,
    pub aggregate_rows: u64,
    pub sort_rows: u64,
    pub slice_rows: u64,
    pub cartesian_product_pairs: u64,
    pub row_value_comparisons: u64,
    pub group_key_comparisons: u64,
    pub group_key_expression_evaluations: u64,
    pub on_predicate_evaluations: u64,
    pub nested_subquery_encodings: u64,
    /// Uncorrelated subquery roots found before encoding.
    ///
    /// Correlated subquery bodies are traversed recursively instead of being
    /// counted at their root.
    pub invariant_subquery_subtrees: u64,
    pub nested_relation_rows: u64,
    pub matching_count_formulas: u64,
    pub matching_count_terms: u64,
    pub identical_plan_fast_paths: u64,
    pub left_relation_rows: u64,
    pub right_relation_rows: u64,
    pub left_output_width: u64,
    pub right_output_width: u64,
}

/// Result and opt-in measurements for one verification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerificationReport {
    pub result: VerificationResult,
    pub phases: VerificationPhaseTimings,
    pub counters: VerificationCounters,
}

#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum Phase {
    LeftParseLowering,
    RightParseLowering,
    SymbolicDatabaseConstruction,
    SchemaConstraintConstruction,
    SchemaAssertion,
    SchemaSolverCheck,
    LeftRelationEncoding,
    RightRelationEncoding,
    ComparisonFormulaConstruction,
    FinalAssertion,
    FinalSolverCheck,
    ModelExtraction,
    ConcreteReplay,
    Z3CallbackBody,
    Z3ContextLifecycle,
    Total,
}

const PHASE_COUNT: usize = Phase::Total as usize + 1;

#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum Counter {
    BaseRows,
    SchemaConstraints,
    UnitRows,
    ScanRows,
    ProductRows,
    JoinRows,
    FilterRows,
    ProjectRows,
    DistinctRows,
    SetOperationRows,
    AggregateRows,
    SortRows,
    SliceRows,
    CartesianProductPairs,
    RowValueComparisons,
    GroupKeyComparisons,
    GroupKeyExpressionEvaluations,
    OnPredicateEvaluations,
    NestedSubqueryEncodings,
    InvariantSubquerySubtrees,
    NestedRelationRows,
    MatchingCountFormulas,
    MatchingCountTerms,
    IdenticalPlanFastPaths,
    LeftRelationRows,
    RightRelationRows,
    LeftOutputWidth,
    RightOutputWidth,
}

const COUNTER_COUNT: usize = Counter::RightOutputWidth as usize + 1;

pub(crate) struct MetricsRecorder {
    phases: [AtomicU64; PHASE_COUNT],
    counters: [AtomicU64; COUNTER_COUNT],
}

impl Default for MetricsRecorder {
    fn default() -> Self {
        Self {
            phases: array::from_fn(|_| AtomicU64::new(0)),
            counters: array::from_fn(|_| AtomicU64::new(0)),
        }
    }
}

impl MetricsRecorder {
    pub(crate) fn measure<T>(&self, phase: Phase, operation: impl FnOnce() -> T) -> T {
        let started = Instant::now();
        let result = operation();
        self.add_phase(phase, started.elapsed());
        result
    }

    pub(crate) fn add_phase(&self, phase: Phase, duration: Duration) {
        self.phases[phase as usize].fetch_add(duration_nanos(duration), Ordering::Relaxed);
    }

    pub(crate) fn phase_duration(&self, phase: Phase) -> Duration {
        Duration::from_nanos(self.phase_value(phase))
    }

    pub(crate) fn add(&self, counter: Counter, value: usize) {
        self.counters[counter as usize].fetch_add(usize_as_u64(value), Ordering::Relaxed);
    }

    pub(crate) fn increment(&self, counter: Counter) {
        self.counters[counter as usize].fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn set(&self, counter: Counter, value: usize) {
        self.counters[counter as usize].store(usize_as_u64(value), Ordering::Relaxed);
    }

    pub(crate) fn snapshot(&self) -> (VerificationPhaseTimings, VerificationCounters) {
        let phase = |phase| Duration::from_nanos(self.phase_value(phase));
        let counter = |counter| self.counter_value(counter);
        (
            VerificationPhaseTimings {
                left_parse_lowering: phase(Phase::LeftParseLowering),
                right_parse_lowering: phase(Phase::RightParseLowering),
                symbolic_database_construction: phase(Phase::SymbolicDatabaseConstruction),
                schema_constraint_construction: phase(Phase::SchemaConstraintConstruction),
                schema_assertion: phase(Phase::SchemaAssertion),
                schema_solver_check: phase(Phase::SchemaSolverCheck),
                left_relation_encoding: phase(Phase::LeftRelationEncoding),
                right_relation_encoding: phase(Phase::RightRelationEncoding),
                comparison_formula_construction: phase(Phase::ComparisonFormulaConstruction),
                final_assertion: phase(Phase::FinalAssertion),
                final_solver_check: phase(Phase::FinalSolverCheck),
                model_extraction: phase(Phase::ModelExtraction),
                concrete_replay: phase(Phase::ConcreteReplay),
                z3_context_lifecycle: phase(Phase::Z3ContextLifecycle),
                total: phase(Phase::Total),
            },
            VerificationCounters {
                base_rows: counter(Counter::BaseRows),
                schema_constraints: counter(Counter::SchemaConstraints),
                unit_rows: counter(Counter::UnitRows),
                scan_rows: counter(Counter::ScanRows),
                product_rows: counter(Counter::ProductRows),
                join_rows: counter(Counter::JoinRows),
                filter_rows: counter(Counter::FilterRows),
                project_rows: counter(Counter::ProjectRows),
                distinct_rows: counter(Counter::DistinctRows),
                set_operation_rows: counter(Counter::SetOperationRows),
                aggregate_rows: counter(Counter::AggregateRows),
                sort_rows: counter(Counter::SortRows),
                slice_rows: counter(Counter::SliceRows),
                cartesian_product_pairs: counter(Counter::CartesianProductPairs),
                row_value_comparisons: counter(Counter::RowValueComparisons),
                group_key_comparisons: counter(Counter::GroupKeyComparisons),
                group_key_expression_evaluations: counter(Counter::GroupKeyExpressionEvaluations),
                on_predicate_evaluations: counter(Counter::OnPredicateEvaluations),
                nested_subquery_encodings: counter(Counter::NestedSubqueryEncodings),
                invariant_subquery_subtrees: counter(Counter::InvariantSubquerySubtrees),
                nested_relation_rows: counter(Counter::NestedRelationRows),
                matching_count_formulas: counter(Counter::MatchingCountFormulas),
                matching_count_terms: counter(Counter::MatchingCountTerms),
                identical_plan_fast_paths: counter(Counter::IdenticalPlanFastPaths),
                left_relation_rows: counter(Counter::LeftRelationRows),
                right_relation_rows: counter(Counter::RightRelationRows),
                left_output_width: counter(Counter::LeftOutputWidth),
                right_output_width: counter(Counter::RightOutputWidth),
            },
        )
    }

    fn phase_value(&self, phase: Phase) -> u64 {
        self.phases[phase as usize].load(Ordering::Relaxed)
    }

    fn counter_value(&self, counter: Counter) -> u64 {
        self.counters[counter as usize].load(Ordering::Relaxed)
    }
}

pub(crate) fn measure<T>(
    metrics: Option<&MetricsRecorder>,
    phase: Phase,
    operation: impl FnOnce() -> T,
) -> T {
    match metrics {
        Some(metrics) => metrics.measure(phase, operation),
        None => operation(),
    }
}

fn duration_nanos(duration: Duration) -> u64 {
    u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
}

fn usize_as_u64(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}
