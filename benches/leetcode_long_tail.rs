#[path = "../tests/support/mod.rs"]
mod support;

use std::env;
use std::hint::black_box;
use std::time::{Duration, Instant};

use querifier::{
    CoercionPolicy, GroupingPolicy, OrderingPolicy, Schema, UnsupportedKind, VerificationResult,
    Verifier, VerifyOptions,
};
use support::leetcode::{CorpusRecord, adapt_schema, load_corpus, validate_corpus};

#[derive(Clone, Copy, Debug)]
struct CaseId {
    file: &'static str,
    index: usize,
    discovery_ms: u64,
}

impl CaseId {
    fn label(self) -> String {
        format!("{}:{}", self.file, self.index)
    }
}

const LONG_TAIL_CASES: [CaseId; 10] = [
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 679,
        discovery_ms: 19_926,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 391,
        discovery_ms: 19_698,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 559,
        discovery_ms: 12_037,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1783.csv",
        index: 485,
        discovery_ms: 7_045,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 415,
        discovery_ms: 6_147,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 319,
        discovery_ms: 2_831,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 295,
        discovery_ms: 2_821,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1364.csv",
        index: 247,
        discovery_ms: 2_814,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1777.csv",
        index: 123,
        discovery_ms: 2_363,
    },
    CaseId {
        file: "benchmark/leetcode/raw_data/1440.csv",
        index: 105,
        discovery_ms: 2_195,
    },
];

#[derive(Clone, Debug)]
struct BenchmarkConfig {
    bound: usize,
    timeout: Duration,
    retry_timeout: Duration,
    max_intermediate_rows: usize,
    iterations: usize,
    warmup_iterations: usize,
    filter: Option<String>,
}

impl BenchmarkConfig {
    fn from_env() -> Self {
        Self {
            bound: env_usize("QUERIFIER_LONG_TAIL_BOUND", 3),
            timeout: Duration::from_millis(env_u64("QUERIFIER_LONG_TAIL_TIMEOUT_MS", 2_000)),
            retry_timeout: Duration::from_millis(env_u64(
                "QUERIFIER_LONG_TAIL_RETRY_TIMEOUT_MS",
                0,
            )),
            max_intermediate_rows: env_usize("QUERIFIER_LONG_TAIL_MAX_ROWS", 10_000),
            iterations: env_usize("QUERIFIER_LONG_TAIL_ITERATIONS", 1).max(1),
            warmup_iterations: env_usize("QUERIFIER_LONG_TAIL_WARMUP", 0),
            filter: env::var("QUERIFIER_LONG_TAIL_FILTER")
                .ok()
                .filter(|value| !value.is_empty()),
        }
    }

    fn verifier(&self, timeout: Duration) -> Verifier {
        Verifier::new(VerifyOptions {
            max_rows_per_table: self.bound,
            timeout,
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

fn main() {
    let config = BenchmarkConfig::from_env();
    let cases = prepare_cases(config.filter.as_deref());
    let verifier = config.verifier(config.timeout);
    let retry_verifier =
        (config.retry_timeout > config.timeout).then(|| config.verifier(config.retry_timeout));

    println!(
        "long_tail_config bound={} timeout_ms={} retry_timeout_ms={} iterations={} warmup={} cases={} filter={:?}",
        config.bound,
        config.timeout.as_millis(),
        config.retry_timeout.as_millis(),
        config.iterations,
        config.warmup_iterations,
        cases.len(),
        config.filter,
    );

    for _ in 0..config.warmup_iterations {
        for case in &cases {
            black_box(verify_case(case, &verifier, retry_verifier.as_ref()));
        }
    }

    let benchmark_started = Instant::now();
    let mut runtimes = Vec::with_capacity(cases.len() * config.iterations);
    for case in &cases {
        for iteration in 1..=config.iterations {
            let started = Instant::now();
            let result = verify_case(case, &verifier, retry_verifier.as_ref());
            let runtime = started.elapsed();
            let outcome = outcome_label(&result);
            black_box(result);
            runtimes.push(runtime);
            println!(
                "long_tail_case file={:?} index={} discovery_ms={} iteration={} runtime_ms={:.3} outcome={outcome}",
                case.id.file,
                case.id.index,
                case.id.discovery_ms,
                iteration,
                runtime.as_secs_f64() * 1_000.0,
            );
        }
    }

    print_summary(config.bound, &runtimes, benchmark_started.elapsed());
}

fn prepare_cases(filter: Option<&str>) -> Vec<PreparedCase> {
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    validate_corpus(&records).expect("the vendored VeriEQL corpus should be valid");
    let selected: Vec<PreparedCase> = LONG_TAIL_CASES
        .iter()
        .copied()
        .filter(|id| filter.is_none_or(|value| id.label().contains(value)))
        .map(|id| prepare_case(&records, id))
        .collect();
    assert!(
        !selected.is_empty(),
        "the long-tail filter selected no cases"
    );
    selected
}

fn prepare_case(records: &[CorpusRecord], id: CaseId) -> PreparedCase {
    let record = records
        .iter()
        .find(|record| record.file == id.file && record.index == id.index)
        .unwrap_or_else(|| panic!("missing long-tail corpus record {}", id.label()));
    PreparedCase {
        id,
        schema: adapt_schema(record)
            .unwrap_or_else(|error| panic!("cannot adapt {}: {error}", id.label())),
        left_sql: record.pair[0].clone(),
        right_sql: record.pair[1].clone(),
    }
}

fn verify_case(
    case: &PreparedCase,
    verifier: &Verifier,
    retry_verifier: Option<&Verifier>,
) -> VerificationResult {
    let result = verifier.verify(&case.schema, &case.left_sql, &case.right_sql);
    if matches!(
        &result,
        VerificationResult::Unsupported { reason } if reason.kind == UnsupportedKind::Solver
    ) && let Some(retry_verifier) = retry_verifier
    {
        return retry_verifier.verify(&case.schema, &case.left_sql, &case.right_sql);
    }
    result
}

fn outcome_label(result: &VerificationResult) -> String {
    match result {
        VerificationResult::True { .. } => "true".to_owned(),
        VerificationResult::False { .. } => "false".to_owned(),
        VerificationResult::Unsupported { reason } => {
            format!("unsupported:{}", reason.code())
        }
    }
}

fn print_summary(bound: usize, runtimes: &[Duration], wall_time: Duration) {
    let mut runtime_ms: Vec<f64> = runtimes
        .iter()
        .map(|runtime| runtime.as_secs_f64() * 1_000.0)
        .collect();
    runtime_ms.sort_by(f64::total_cmp);
    let total_ms = runtime_ms.iter().sum::<f64>();
    let mean_ms = total_ms / runtime_ms.len() as f64;
    println!(
        "long_tail_summary bound={bound} count={} mean_ms={mean_ms:.3} p50_ms={:.3} p90_ms={:.3} max_ms={:.3} measured_total_ms={total_ms:.3} wall_ms={:.3}",
        runtime_ms.len(),
        percentile(&runtime_ms, 50),
        percentile(&runtime_ms, 90),
        runtime_ms[runtime_ms.len() - 1],
        wall_time.as_secs_f64() * 1_000.0,
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
