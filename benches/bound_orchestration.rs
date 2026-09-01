#[path = "../tests/support/mod.rs"]
mod support;

use std::env;
use std::hint::black_box;
use std::time::{Duration, Instant};

use querifier::{
    BoundSearchOrder, BoundVerification, CoercionPolicy, GroupingPolicy, OrderingPolicy, Schema,
    VerificationResult, Verifier, VerifyOptions,
};
use support::leetcode::{CorpusRecord, adapt_schema, load_corpus, validate_corpus};

#[derive(Clone, Copy)]
enum Expected {
    True,
    False,
}

#[derive(Clone, Copy)]
struct CaseId {
    name: &'static str,
    file: &'static str,
    index: usize,
    expected: [Expected; 3],
}

const CASES: [CaseId; 3] = [
    CaseId {
        name: "false_at_smallest",
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 391,
        expected: [Expected::False; 3],
    },
    CaseId {
        name: "true_at_largest",
        file: "benchmark/leetcode/raw_data/1777.csv",
        index: 123,
        expected: [Expected::True; 3],
    },
    CaseId {
        name: "bound_transition",
        file: "benchmark/leetcode/raw_data/182.csv",
        index: 38,
        expected: [Expected::True, Expected::False, Expected::False],
    },
];

struct PreparedCase {
    id: CaseId,
    schema: Schema,
    left_sql: String,
    right_sql: String,
}

#[derive(Clone, Copy)]
enum Mode {
    Independent,
    LargestFirst,
    SmallestFirst,
}

impl Mode {
    const ALL: [Self; 3] = [Self::Independent, Self::LargestFirst, Self::SmallestFirst];

    const fn label(self) -> &'static str {
        match self {
            Self::Independent => "independent",
            Self::LargestFirst => "largest_first",
            Self::SmallestFirst => "smallest_first",
        }
    }
}

fn main() {
    let iterations = env_usize("QUERIFIER_BOUNDS_ITERATIONS", 3).max(1);
    let warmup = env_usize("QUERIFIER_BOUNDS_WARMUP", 1);
    let timeout = Duration::from_millis(env_u64("QUERIFIER_BOUNDS_TIMEOUT_MS", 2_000).max(1));
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    validate_corpus(&records).expect("the vendored VeriEQL corpus should be valid");
    let cases = CASES
        .iter()
        .copied()
        .map(|id| prepare_case(&records, id))
        .collect::<Vec<_>>();

    println!(
        "bounds_config bounds=[1,2,3] timeout_ms={} iterations={iterations} warmup={warmup} cases={}",
        timeout.as_millis(),
        cases.len()
    );
    for mode in Mode::ALL {
        for case in &cases {
            for _ in 0..warmup {
                black_box(run_case(case, mode, timeout));
            }
            for iteration in 1..=iterations {
                let started = Instant::now();
                let results = run_case(case, mode, timeout);
                let runtime = started.elapsed();
                assert_expected(case, &results);
                let solved = results.iter().filter(|result| result.was_solved()).count();
                println!(
                    "bounds_case name={} mode={} iteration={iteration} runtime_ms={:.3} requested={} solved={} inferred={}",
                    case.id.name,
                    mode.label(),
                    runtime.as_secs_f64() * 1_000.0,
                    results.len(),
                    solved,
                    results.len() - solved,
                );
                black_box(results);
            }
        }
    }
}

fn prepare_case(records: &[CorpusRecord], id: CaseId) -> PreparedCase {
    let record = records
        .iter()
        .find(|record| record.file == id.file && record.index == id.index)
        .unwrap_or_else(|| panic!("missing bounds benchmark case {}", id.name));
    PreparedCase {
        id,
        schema: adapt_schema(record)
            .unwrap_or_else(|error| panic!("cannot adapt {}: {error}", id.name)),
        left_sql: record.pair[0].clone(),
        right_sql: record.pair[1].clone(),
    }
}

fn run_case(case: &PreparedCase, mode: Mode, timeout: Duration) -> Vec<BoundVerification> {
    let verifier = |bound| {
        Verifier::new(VerifyOptions {
            max_rows_per_table: bound,
            timeout,
            max_intermediate_rows: 10_000,
            ordering_policy: OrderingPolicy::IgnoreTopLevelOrder,
            grouping_policy: GroupingPolicy::PermissiveFirstRow,
            coercion_policy: CoercionPolicy::MySqlCompatible,
        })
    };
    match mode {
        Mode::Independent => (1..=3)
            .map(|bound| BoundVerification {
                bound,
                source_bound: bound,
                result: verifier(bound).verify(&case.schema, &case.left_sql, &case.right_sql),
            })
            .collect(),
        Mode::LargestFirst | Mode::SmallestFirst => verifier(3)
            .verify_bounds(
                &case.schema,
                &case.left_sql,
                &case.right_sql,
                &[1, 2, 3],
                match mode {
                    Mode::LargestFirst => BoundSearchOrder::LargestFirst,
                    Mode::SmallestFirst => BoundSearchOrder::SmallestFirst,
                    Mode::Independent => unreachable!("independent mode returned above"),
                },
            )
            .expect("the benchmark uses positive bounds"),
    }
}

fn assert_expected(case: &PreparedCase, results: &[BoundVerification]) {
    assert_eq!(results.len(), case.id.expected.len());
    for (result, expected) in results.iter().zip(case.id.expected) {
        let matches = match expected {
            Expected::True => matches!(result.result, VerificationResult::True { .. }),
            Expected::False => matches!(result.result, VerificationResult::False { .. }),
        };
        assert!(
            matches,
            "{} at bound {} returned {:?}",
            case.id.name, result.bound, result.result
        );
    }
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
