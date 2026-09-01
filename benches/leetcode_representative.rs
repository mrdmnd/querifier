#[path = "../tests/support/mod.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use querifier::{
    CoercionPolicy, GroupingPolicy, OrderingPolicy, Schema, VerificationCounters,
    VerificationPhaseTimings, VerificationResult, Verifier, VerifyOptions,
};
use support::leetcode::{CorpusRecord, adapt_schema, load_corpus, validate_corpus};

const TARGET_BOUND: usize = 3;
const NEAR_TAIL_MIN_MS: f64 = 250.0;
const NEAR_TAIL_MAX_MS: f64 = 1_000.0;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Feature {
    Join,
    Aggregate,
    Window,
    Subquery,
    SetOperation,
    Ordering,
    Composite,
}

impl Feature {
    const ALL: [Self; 7] = [
        Self::Join,
        Self::Aggregate,
        Self::Window,
        Self::Subquery,
        Self::SetOperation,
        Self::Ordering,
        Self::Composite,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::Join => "join",
            Self::Aggregate => "aggregate",
            Self::Window => "window",
            Self::Subquery => "subquery",
            Self::SetOperation => "set_operation",
            Self::Ordering => "ordering",
            Self::Composite => "composite",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PerformanceTier {
    Typical,
    NearTail,
    SolverTail,
}

impl PerformanceTier {
    const fn label(self) -> &'static str {
        match self {
            Self::Typical => "typical",
            Self::NearTail => "near_tail",
            Self::SolverTail => "solver_tail",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum VerdictTarget {
    True,
    False,
    Solver,
}

impl VerdictTarget {
    const fn label(self) -> &'static str {
        match self {
            Self::True => "true",
            Self::False => "false",
            Self::Solver => "solver",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CaseId {
    file: &'static str,
    index: usize,
    feature: Feature,
    tier: PerformanceTier,
    expected_verdicts: [VerdictTarget; 3],
}

impl CaseId {
    fn label(self) -> String {
        format!("{}:{}", self.file, self.index)
    }

    fn matches_filter(self, filter: &str) -> bool {
        self.label().contains(filter)
            || self.feature.label().contains(filter)
            || self.tier.label().contains(filter)
            || self
                .expected_verdicts
                .iter()
                .any(|verdict| verdict.label().contains(filter))
    }

    fn expected_verdict(self, bound: usize) -> Option<VerdictTarget> {
        bound
            .checked_sub(1)
            .and_then(|index| self.expected_verdicts.get(index))
            .copied()
    }

    fn target_verdict(self) -> VerdictTarget {
        self.expected_verdict(TARGET_BOUND)
            .expect("the target bound must have a calibrated verdict")
    }
}

// Verdicts for bounds 1-3 and performance tiers at TARGET_BOUND are calibrated with the default
// timeout. The faster feature cases protect breadth; the near- and solver-tail cases expose scaling.
const REPRESENTATIVE_CASES: &[CaseId] = &[
    CaseId {
        file: "benchmark/leetcode/raw_data/175.csv",
        index: 16,
        feature: Feature::Join,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/175.csv",
        index: 8,
        feature: Feature::Join,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::False; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/182.csv",
        index: 2,
        feature: Feature::Aggregate,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/182.csv",
        index: 38,
        feature: Feature::Aggregate,
        tier: PerformanceTier::Typical,
        expected_verdicts: [
            VerdictTarget::True,
            VerdictTarget::False,
            VerdictTarget::False,
        ],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/182.csv",
        index: 0,
        feature: Feature::Window,
        tier: PerformanceTier::Typical,
        expected_verdicts: [
            VerdictTarget::True,
            VerdictTarget::False,
            VerdictTarget::False,
        ],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/550.csv",
        index: 97,
        feature: Feature::Window,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/182.csv",
        index: 151,
        feature: Feature::Subquery,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/183.csv",
        index: 0,
        feature: Feature::Subquery,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::False; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/595.csv",
        index: 34,
        feature: Feature::SetOperation,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/595.csv",
        index: 10,
        feature: Feature::SetOperation,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::False; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/175.csv",
        index: 56,
        feature: Feature::Ordering,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/182.csv",
        index: 40,
        feature: Feature::Ordering,
        tier: PerformanceTier::Typical,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 391,
        feature: Feature::Composite,
        tier: PerformanceTier::NearTail,
        expected_verdicts: [VerdictTarget::False; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 559,
        feature: Feature::Composite,
        tier: PerformanceTier::NearTail,
        expected_verdicts: [VerdictTarget::False; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 415,
        feature: Feature::Composite,
        tier: PerformanceTier::NearTail,
        expected_verdicts: [VerdictTarget::False; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1777.csv",
        index: 123,
        feature: Feature::Composite,
        tier: PerformanceTier::NearTail,
        expected_verdicts: [VerdictTarget::True; 3],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1783.csv",
        index: 485,
        feature: Feature::Aggregate,
        tier: PerformanceTier::SolverTail,
        expected_verdicts: [
            VerdictTarget::True,
            VerdictTarget::Solver,
            VerdictTarget::Solver,
        ],
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1440.csv",
        index: 105,
        feature: Feature::Join,
        tier: PerformanceTier::SolverTail,
        expected_verdicts: [
            VerdictTarget::True,
            VerdictTarget::True,
            VerdictTarget::Solver,
        ],
    },
];

#[derive(Clone, Debug)]
struct BenchmarkConfig {
    bounds: Vec<usize>,
    timeout: Duration,
    max_intermediate_rows: usize,
    iterations: usize,
    warmup_iterations: usize,
    filter: Option<String>,
    instrumentation: bool,
    workers: usize,
    require_expected_outcomes: bool,
}

impl BenchmarkConfig {
    fn from_env() -> Self {
        Self {
            bounds: env_bounds("QUERIFIER_REPRESENTATIVE_BOUNDS", &[1, 2, 3]),
            timeout: Duration::from_millis(env_u64("QUERIFIER_REPRESENTATIVE_TIMEOUT_MS", 1_000)),
            max_intermediate_rows: env_usize("QUERIFIER_REPRESENTATIVE_MAX_ROWS", 10_000),
            iterations: env_usize("QUERIFIER_REPRESENTATIVE_ITERATIONS", 1).max(1),
            warmup_iterations: env_usize("QUERIFIER_REPRESENTATIVE_WARMUP", 0),
            filter: env::var("QUERIFIER_REPRESENTATIVE_FILTER")
                .ok()
                .filter(|value| !value.is_empty()),
            instrumentation: env_bool("QUERIFIER_REPRESENTATIVE_INSTRUMENTATION", false),
            workers: env_usize("QUERIFIER_REPRESENTATIVE_WORKERS", 1).max(1),
            require_expected_outcomes: env_bool("QUERIFIER_REPRESENTATIVE_REQUIRE_EXPECTED", true),
        }
    }

    fn verifier(&self, bound: usize) -> Verifier {
        Verifier::new(VerifyOptions {
            max_rows_per_table: bound,
            timeout: self.timeout,
            max_intermediate_rows: self.max_intermediate_rows,
            ordering_policy: OrderingPolicy::IgnoreTopLevelOrder,
            grouping_policy: GroupingPolicy::PermissiveFirstRow,
            coercion_policy: CoercionPolicy::MySqlCompatible,
        })
    }
}

#[derive(Debug)]
struct PreparedCase {
    id: CaseId,
    schema: Schema,
    left_sql: String,
    right_sql: String,
}

#[derive(Clone, Debug)]
struct Observation {
    case: CaseId,
    bound: usize,
    feature: Feature,
    tier: PerformanceTier,
    target_verdict: VerdictTarget,
    expected_verdict: Option<VerdictTarget>,
    runtime: Duration,
    outcome: String,
}

struct Measurement {
    sequence: usize,
    iteration: usize,
    observation: Observation,
    metrics: Option<(VerificationPhaseTimings, VerificationCounters)>,
}

fn main() {
    validate_case_set();
    let config = BenchmarkConfig::from_env();
    let cases = prepare_cases(config.filter.as_deref());

    println!(
        "representative_config bounds={:?} target_bound={TARGET_BOUND} timeout_ms={} iterations={} warmup={} cases={} filter={:?} instrumentation={} workers={} latency_mode={} require_expected_outcomes={}",
        config.bounds,
        config.timeout.as_millis(),
        config.iterations,
        config.warmup_iterations,
        cases.len(),
        config.filter,
        config.instrumentation,
        config.workers,
        if config.workers == 1 {
            "sequential"
        } else {
            "contended_throughput"
        },
        config.require_expected_outcomes,
    );

    for bound in &config.bounds {
        warm_up_bound(&config, &cases, *bound);
    }

    let benchmark_started = Instant::now();
    let mut observations =
        Vec::with_capacity(cases.len() * config.bounds.len() * config.iterations);
    let mut sequence = 0;
    for bound in &config.bounds {
        let mut measurements = measure_bound(&config, &cases, *bound, sequence);
        sequence += measurements.len();
        measurements.sort_by_key(|measurement| measurement.sequence);
        for measurement in measurements {
            print_measurement(&measurement);
            observations.push(measurement.observation);
        }
    }

    let mismatches = print_summaries(&observations, benchmark_started.elapsed());
    if config.require_expected_outcomes {
        assert_eq!(
            mismatches, 0,
            "representative benchmark produced unexpected solver outcomes"
        );
    }
}

fn warm_up_bound(config: &BenchmarkConfig, cases: &[PreparedCase], bound: usize) {
    if config.warmup_iterations == 0 {
        return;
    }
    if config.workers == 1 {
        let verifier = config.verifier(bound);
        for _ in 0..config.warmup_iterations {
            for case in cases {
                black_box(verify_case(case, &verifier));
            }
        }
        return;
    }

    for _ in 0..config.warmup_iterations {
        let next_case = AtomicUsize::new(0);
        thread::scope(|scope| {
            let mut workers = Vec::with_capacity(config.workers.min(cases.len()));
            for _ in 0..config.workers.min(cases.len()) {
                let next_case = &next_case;
                workers.push(scope.spawn(move || {
                    let verifier = config.verifier(bound);
                    loop {
                        let case_index = next_case.fetch_add(1, Ordering::Relaxed);
                        let Some(case) = cases.get(case_index) else {
                            break;
                        };
                        black_box(verify_case(case, &verifier));
                    }
                }));
            }
            for worker in workers {
                worker
                    .join()
                    .expect("a representative warmup worker panicked");
            }
        });
    }
}

fn measure_bound(
    config: &BenchmarkConfig,
    cases: &[PreparedCase],
    bound: usize,
    sequence_start: usize,
) -> Vec<Measurement> {
    if config.workers == 1 {
        let verifier = config.verifier(bound);
        return cases
            .iter()
            .enumerate()
            .flat_map(|(case_index, case)| {
                let verifier = &verifier;
                (1..=config.iterations).map(move |iteration| {
                    let sequence = sequence_start
                        + case_index * config.iterations
                        + iteration.saturating_sub(1);
                    measure_case(config, case, verifier, bound, iteration, sequence)
                })
            })
            .collect();
    }

    let mut measurements = Vec::with_capacity(cases.len() * config.iterations);
    for iteration in 1..=config.iterations {
        let next_case = AtomicUsize::new(0);
        let mut iteration_measurements = thread::scope(|scope| {
            let mut workers = Vec::with_capacity(config.workers.min(cases.len()));
            for _ in 0..config.workers.min(cases.len()) {
                let next_case = &next_case;
                workers.push(scope.spawn(move || {
                    let verifier = config.verifier(bound);
                    let mut measurements = Vec::new();
                    loop {
                        let case_index = next_case.fetch_add(1, Ordering::Relaxed);
                        let Some(case) = cases.get(case_index) else {
                            break;
                        };
                        let sequence = sequence_start
                            + case_index * config.iterations
                            + iteration.saturating_sub(1);
                        measurements.push(measure_case(
                            config, case, &verifier, bound, iteration, sequence,
                        ));
                    }
                    measurements
                }));
            }

            workers
                .into_iter()
                .flat_map(|worker| {
                    worker
                        .join()
                        .expect("a representative benchmark worker panicked")
                })
                .collect::<Vec<_>>()
        });
        measurements.append(&mut iteration_measurements);
    }
    measurements
}

fn measure_case(
    config: &BenchmarkConfig,
    case: &PreparedCase,
    verifier: &Verifier,
    bound: usize,
    iteration: usize,
    sequence: usize,
) -> Measurement {
    let started = Instant::now();
    let (result, metrics) = if config.instrumentation {
        let report = verifier.verify_with_metrics(&case.schema, &case.left_sql, &case.right_sql);
        (report.result, Some((report.phases, report.counters)))
    } else {
        (verify_case(case, verifier), None)
    };
    let runtime = started.elapsed();
    let outcome = outcome_label(&result);
    black_box(&result);
    Measurement {
        sequence,
        iteration,
        observation: Observation {
            case: case.id,
            bound,
            feature: case.id.feature,
            tier: case.id.tier,
            target_verdict: case.id.target_verdict(),
            expected_verdict: case.id.expected_verdict(bound),
            runtime,
            outcome,
        },
        metrics,
    }
}

fn print_measurement(measurement: &Measurement) {
    let observation = &measurement.observation;
    let expected_label = observation
        .expected_verdict
        .map_or("untracked", VerdictTarget::label);
    println!(
        "representative_case file={:?} index={} feature={} tier={} target_verdict={} expected_verdict={expected_label} bound={} iteration={} runtime_ms={:.3} outcome={}",
        observation.case.file,
        observation.case.index,
        observation.feature.label(),
        observation.tier.label(),
        observation.target_verdict.label(),
        observation.bound,
        measurement.iteration,
        observation.runtime.as_secs_f64() * 1_000.0,
        observation.outcome,
    );
    if let Some((phases, counters)) = &measurement.metrics {
        print_metrics(
            observation.case,
            observation.bound,
            measurement.iteration,
            phases,
            counters,
        );
    }
}

fn validate_case_set() {
    let mut ids = BTreeSet::new();
    for case in REPRESENTATIVE_CASES {
        assert!(
            ids.insert((case.file, case.index)),
            "duplicate representative case {}",
            case.label()
        );
    }
    for feature in Feature::ALL {
        let count = REPRESENTATIVE_CASES
            .iter()
            .filter(|case| case.feature == feature)
            .count();
        assert!(
            count >= 2,
            "representative case set needs at least two {} cases",
            feature.label()
        );
    }
    assert!(
        REPRESENTATIVE_CASES
            .iter()
            .filter(|case| case.tier == PerformanceTier::NearTail)
            .count()
            >= 4,
        "representative case set needs at least four near-tail cases"
    );
    let true_cases = REPRESENTATIVE_CASES
        .iter()
        .filter(|case| case.target_verdict() == VerdictTarget::True)
        .count();
    let false_cases = REPRESENTATIVE_CASES
        .iter()
        .filter(|case| case.target_verdict() == VerdictTarget::False)
        .count();
    let solver_cases = REPRESENTATIVE_CASES
        .iter()
        .filter(|case| case.target_verdict() == VerdictTarget::Solver)
        .count();
    assert_eq!(
        true_cases, false_cases,
        "representative true and false targets must be balanced"
    );
    assert!(
        solver_cases >= 2,
        "representative case set needs at least two solver targets"
    );
}

fn prepare_cases(filter: Option<&str>) -> Vec<PreparedCase> {
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    validate_corpus(&records).expect("the vendored VeriEQL corpus should be valid");
    let selected = REPRESENTATIVE_CASES
        .iter()
        .copied()
        .filter(|id| filter.is_none_or(|value| id.matches_filter(value)))
        .map(|id| prepare_case(&records, id))
        .collect::<Vec<_>>();
    assert!(
        !selected.is_empty(),
        "the representative filter selected no cases"
    );
    selected
}

fn prepare_case(records: &[CorpusRecord], id: CaseId) -> PreparedCase {
    let record = records
        .iter()
        .find(|record| record.file == id.file && record.index == id.index)
        .unwrap_or_else(|| panic!("missing representative corpus record {}", id.label()));
    PreparedCase {
        id,
        schema: adapt_schema(record)
            .unwrap_or_else(|error| panic!("cannot adapt {}: {error}", id.label())),
        left_sql: record.pair[0].clone(),
        right_sql: record.pair[1].clone(),
    }
}

fn verify_case(case: &PreparedCase, verifier: &Verifier) -> VerificationResult {
    verifier.verify(&case.schema, &case.left_sql, &case.right_sql)
}

fn print_metrics(
    case: CaseId,
    bound: usize,
    iteration: usize,
    phases: &VerificationPhaseTimings,
    counters: &VerificationCounters,
) {
    println!(
        "representative_metrics file={:?} index={} feature={} tier={} bound={} iteration={} \
         left_parse_lowering_ns={} right_parse_lowering_ns={} \
         symbolic_database_construction_ns={} schema_constraint_construction_ns={} \
         schema_assertion_ns={} schema_solver_check_ns={} left_relation_encoding_ns={} \
         right_relation_encoding_ns={} comparison_formula_construction_ns={} \
         final_assertion_ns={} final_solver_check_ns={} model_extraction_ns={} \
         concrete_replay_ns={} z3_context_lifecycle_ns={} total_ns={} \
         base_rows={} schema_constraints={} unit_rows={} scan_rows={} product_rows={} \
         join_rows={} filter_rows={} project_rows={} distinct_rows={} set_operation_rows={} \
         aggregate_rows={} sort_rows={} slice_rows={} cartesian_product_pairs={} \
         row_value_comparisons={} group_key_comparisons={} \
         group_key_expression_evaluations={} on_predicate_evaluations={} \
         nested_subquery_encodings={} invariant_subquery_subtrees={} nested_relation_rows={} \
         matching_count_formulas={} matching_count_terms={} identical_plan_fast_paths={} \
         left_relation_rows={} right_relation_rows={} \
         left_output_width={} right_output_width={}",
        case.file,
        case.index,
        case.feature.label(),
        case.tier.label(),
        bound,
        iteration,
        phases.left_parse_lowering.as_nanos(),
        phases.right_parse_lowering.as_nanos(),
        phases.symbolic_database_construction.as_nanos(),
        phases.schema_constraint_construction.as_nanos(),
        phases.schema_assertion.as_nanos(),
        phases.schema_solver_check.as_nanos(),
        phases.left_relation_encoding.as_nanos(),
        phases.right_relation_encoding.as_nanos(),
        phases.comparison_formula_construction.as_nanos(),
        phases.final_assertion.as_nanos(),
        phases.final_solver_check.as_nanos(),
        phases.model_extraction.as_nanos(),
        phases.concrete_replay.as_nanos(),
        phases.z3_context_lifecycle.as_nanos(),
        phases.total.as_nanos(),
        counters.base_rows,
        counters.schema_constraints,
        counters.unit_rows,
        counters.scan_rows,
        counters.product_rows,
        counters.join_rows,
        counters.filter_rows,
        counters.project_rows,
        counters.distinct_rows,
        counters.set_operation_rows,
        counters.aggregate_rows,
        counters.sort_rows,
        counters.slice_rows,
        counters.cartesian_product_pairs,
        counters.row_value_comparisons,
        counters.group_key_comparisons,
        counters.group_key_expression_evaluations,
        counters.on_predicate_evaluations,
        counters.nested_subquery_encodings,
        counters.invariant_subquery_subtrees,
        counters.nested_relation_rows,
        counters.matching_count_formulas,
        counters.matching_count_terms,
        counters.identical_plan_fast_paths,
        counters.left_relation_rows,
        counters.right_relation_rows,
        counters.left_output_width,
        counters.right_output_width,
    );
}

fn outcome_label(result: &VerificationResult) -> String {
    match result {
        VerificationResult::True { .. } => "true".to_owned(),
        VerificationResult::False { .. } => "false".to_owned(),
        VerificationResult::Unsupported { reason } => format!("unsupported:{}", reason.code()),
    }
}

fn print_summaries(observations: &[Observation], wall_time: Duration) -> usize {
    let mut by_case: BTreeMap<(CaseId, usize), Vec<&Observation>> = BTreeMap::new();
    let mut by_bound: BTreeMap<usize, Vec<&Observation>> = BTreeMap::new();
    let mut by_feature: BTreeMap<(Feature, usize), Vec<&Observation>> = BTreeMap::new();
    let mut by_tier: BTreeMap<(PerformanceTier, usize), Vec<&Observation>> = BTreeMap::new();
    let mut by_expected_verdict: BTreeMap<(VerdictTarget, usize), Vec<&Observation>> =
        BTreeMap::new();
    let mut verdicts: BTreeMap<(usize, &str), usize> = BTreeMap::new();
    for observation in observations {
        by_case
            .entry((observation.case, observation.bound))
            .or_default()
            .push(observation);
        by_bound
            .entry(observation.bound)
            .or_default()
            .push(observation);
        by_feature
            .entry((observation.feature, observation.bound))
            .or_default()
            .push(observation);
        by_tier
            .entry((observation.tier, observation.bound))
            .or_default()
            .push(observation);
        if let Some(expected_verdict) = observation.expected_verdict {
            by_expected_verdict
                .entry((expected_verdict, observation.bound))
                .or_default()
                .push(observation);
        }
        *verdicts
            .entry((observation.bound, observation.outcome.as_str()))
            .or_default() += 1;
    }

    for ((case, bound), group) in by_case {
        print_distribution("case", &case.label(), Some(bound), &group);
    }
    for (bound, group) in by_bound {
        print_distribution("bound", &bound.to_string(), None, &group);
    }
    for ((feature, bound), group) in by_feature {
        print_distribution("feature", feature.label(), Some(bound), &group);
    }
    for ((tier, bound), group) in by_tier {
        print_distribution("tier", tier.label(), Some(bound), &group);
    }
    for ((verdict, bound), group) in by_expected_verdict {
        print_distribution("expected_verdict", verdict.label(), Some(bound), &group);
    }
    for ((bound, outcome), count) in verdicts {
        println!("representative_verdict bound={bound} outcome={outcome} count={count}");
    }
    let mismatches = print_target_checks(observations);
    println!(
        "representative_wall_time runtime_ms={:.3}",
        wall_time.as_secs_f64() * 1_000.0
    );
    mismatches
}

fn print_target_checks(observations: &[Observation]) -> usize {
    let mut calibrated_by_bound: BTreeMap<usize, Vec<&Observation>> = BTreeMap::new();
    let mut total_mismatches = 0;
    for observation in observations
        .iter()
        .filter(|observation| observation.expected_verdict.is_some())
    {
        calibrated_by_bound
            .entry(observation.bound)
            .or_default()
            .push(observation);
    }
    for (bound, calibrated) in calibrated_by_bound {
        let matches = calibrated
            .iter()
            .filter(|observation| {
                verdict_matches(
                    observation
                        .expected_verdict
                        .expect("calibrated observations have an expected verdict"),
                    &observation.outcome,
                )
            })
            .count();
        let mismatches = calibrated.len() - matches;
        total_mismatches += mismatches;
        println!(
            "representative_expected_check bound={bound} matching_observations={matches} mismatching_observations={mismatches} total_observations={}",
            calibrated.len(),
        );
    }

    let target_observations = observations
        .iter()
        .filter(|observation| observation.bound == TARGET_BOUND)
        .collect::<Vec<_>>();
    let near_tail = target_observations
        .iter()
        .filter(|observation| observation.tier == PerformanceTier::NearTail)
        .collect::<Vec<_>>();
    let within_range = near_tail
        .iter()
        .filter(|observation| {
            let runtime_ms = observation.runtime.as_secs_f64() * 1_000.0;
            (NEAR_TAIL_MIN_MS..NEAR_TAIL_MAX_MS).contains(&runtime_ms)
        })
        .count();
    println!(
        "representative_near_tail_check bound={TARGET_BOUND} min_ms={NEAR_TAIL_MIN_MS:.0} max_ms={NEAR_TAIL_MAX_MS:.0} within_range={within_range} observed={}",
        near_tail.len(),
    );
    total_mismatches
}

fn verdict_matches(target: VerdictTarget, outcome: &str) -> bool {
    match target {
        VerdictTarget::True => outcome == "true",
        VerdictTarget::False => outcome == "false",
        VerdictTarget::Solver => outcome == "unsupported:solver",
    }
}

fn print_distribution(
    dimension: &str,
    value: &str,
    bound: Option<usize>,
    observations: &[&Observation],
) {
    let mut runtime_ms = observations
        .iter()
        .map(|observation| observation.runtime.as_secs_f64() * 1_000.0)
        .collect::<Vec<_>>();
    runtime_ms.sort_by(f64::total_cmp);
    let total_ms = runtime_ms.iter().sum::<f64>();
    let mean_ms = total_ms / runtime_ms.len() as f64;
    let bound_field = bound.map_or_else(String::new, |bound| format!(" bound={bound}"));
    println!(
        "representative_summary dimension={dimension} value={value}{bound_field} count={} mean_ms={mean_ms:.3} p50_ms={:.3} p90_ms={:.3} p99_ms={:.3} max_ms={:.3} total_ms={total_ms:.3}",
        runtime_ms.len(),
        percentile(&runtime_ms, 50),
        percentile(&runtime_ms, 90),
        percentile(&runtime_ms, 99),
        runtime_ms[runtime_ms.len() - 1],
    );
}

fn percentile(sorted_values: &[f64], percentage: usize) -> f64 {
    let rank = sorted_values
        .len()
        .saturating_mul(percentage)
        .div_ceil(100)
        .saturating_sub(1)
        .min(sorted_values.len() - 1);
    sorted_values[rank]
}

fn env_bounds(name: &str, default: &[usize]) -> Vec<usize> {
    let mut bounds = match env::var(name) {
        Ok(value) => value
            .split(',')
            .map(str::trim)
            .map(|bound| {
                bound.parse::<usize>().unwrap_or_else(|error| {
                    panic!("{name} contains invalid bound {bound:?}: {error}")
                })
            })
            .collect::<Vec<_>>(),
        Err(_) => default.to_vec(),
    };
    assert!(!bounds.is_empty(), "{name} must contain at least one bound");
    assert!(
        bounds.iter().all(|bound| *bound > 0),
        "{name} bounds must be greater than zero"
    );
    bounds.sort_unstable();
    bounds.dedup();
    bounds
}

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn env_u64(name: &str, default: u64) -> u64 {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn env_bool(name: &str, default: bool) -> bool {
    env::var(name)
        .ok()
        .and_then(|value| match value.as_str() {
            "1" | "true" | "TRUE" | "yes" | "YES" => Some(true),
            "0" | "false" | "FALSE" | "no" | "NO" => Some(false),
            _ => None,
        })
        .unwrap_or(default)
}
