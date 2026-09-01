mod support;

use std::collections::BTreeMap;
use std::env;
use std::io::{self, IsTerminal, Write};
use std::time::{Duration, Instant};

use querifier::{
    CoercionPolicy, GroupingPolicy, OrderingPolicy, UnsupportedKind, VerificationResult, Verifier,
    VerifyOptions,
};
use support::leetcode::{
    CorpusRecord, EXPECTED_RECORDS, adapt_schema, load_corpus, validate_corpus,
};

#[test]
fn vendored_leetcode_corpus_is_well_formed() {
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    validate_corpus(&records).expect("the vendored VeriEQL corpus invariants should hold");
    assert_eq!(records.len(), EXPECTED_RECORDS);
    for record in &records {
        adapt_schema(record).unwrap_or_else(|error| {
            panic!(
                "schema adapter failed for {}:{}: {error}",
                record.file, record.index
            )
        });
    }
}

#[test]
fn reviewed_corpus_cases_have_expected_bounded_verdicts() {
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    let equivalent = corpus_record(&records, "benchmark/leetcode/raw_data/175.csv", 1);
    let different = corpus_record(&records, "benchmark/leetcode/raw_data/175.csv", 8);
    let verifier = Verifier::new(VerifyOptions {
        max_rows_per_table: 1,
        timeout: Duration::from_secs(2),
        max_intermediate_rows: 10_000,
        ..VerifyOptions::default()
    });

    for record in [equivalent, different] {
        adapt_schema(record).expect("reviewed corpus schemas should adapt");
    }
    assert!(matches!(
        verifier.verify(
            &adapt_schema(equivalent).expect("reviewed corpus schema should adapt"),
            &equivalent.pair[0],
            &equivalent.pair[1],
        ),
        VerificationResult::True { bound: 1 }
    ));
    assert!(matches!(
        verifier.verify(
            &adapt_schema(different).expect("reviewed corpus schema should adapt"),
            &different.pair[0],
            &different.pair[1],
        ),
        VerificationResult::False { .. }
    ));
}

fn corpus_record<'records>(
    records: &'records [CorpusRecord],
    file: &str,
    index: usize,
) -> &'records CorpusRecord {
    records
        .iter()
        .find(|record| record.file == file && record.index == index)
        .unwrap_or_else(|| panic!("missing reviewed corpus record {file}:{index}"))
}

#[derive(Debug, Default)]
struct Coverage {
    bounded_true: usize,
    false_with_witness: usize,
    adapter_unsupported: usize,
    internal_errors: usize,
    resource_retries: usize,
    recovered_by_retry: usize,
    unsupported_by_kind: BTreeMap<&'static str, usize>,
    unsupported_reasons: BTreeMap<String, usize>,
    false_examples: Vec<String>,
    internal_examples: Vec<String>,
    unsupported_examples: BTreeMap<String, Vec<String>>,
}

#[derive(Debug)]
struct SlowRecord {
    runtime: Duration,
    corpus_index: usize,
    file: String,
    record_index: usize,
}

const PROGRESS_BAR_WIDTH: usize = 30;

struct ProgressReporter {
    total: usize,
    update_every: usize,
    started: Instant,
    interactive: bool,
}

impl ProgressReporter {
    fn new(total: usize) -> Self {
        Self {
            total,
            update_every: env_usize("QUERIFIER_LEETCODE_PROGRESS_EVERY", 100).max(1),
            started: Instant::now(),
            interactive: io::stderr().is_terminal(),
        }
    }

    fn update(&self, completed: usize) {
        if !completed.is_multiple_of(self.update_every) && completed != self.total {
            return;
        }

        let elapsed = self.started.elapsed();
        let records_per_second = completed as f64 / elapsed.as_secs_f64();
        let remaining = self.total.saturating_sub(completed);
        let eta = if records_per_second.is_finite() && records_per_second > 0.0 {
            Duration::from_secs_f64(remaining as f64 / records_per_second)
        } else {
            Duration::ZERO
        };
        let filled = completed.saturating_mul(PROGRESS_BAR_WIDTH) / self.total;
        let bar = format!(
            "{}{}",
            "#".repeat(filled),
            "-".repeat(PROGRESS_BAR_WIDTH - filled)
        );
        let line = format!(
            "LeetCode [{bar}] {completed}/{total} ({percent:5.1}%) \
             {records_per_second:6.1} records/s elapsed={elapsed} ETA={eta}",
            total = self.total,
            percent = completed as f64 * 100.0 / self.total as f64,
            elapsed = format_duration(elapsed),
            eta = format_duration(eta),
        );
        let mut stderr = io::stderr().lock();
        if self.interactive {
            write!(stderr, "\r{line}").expect("writing LeetCode progress should succeed");
            if completed == self.total {
                writeln!(stderr).expect("finishing LeetCode progress should succeed");
            }
        } else {
            writeln!(stderr, "{line}").expect("writing LeetCode progress should succeed");
        }
        stderr
            .flush()
            .expect("flushing LeetCode progress should succeed");
    }
}

fn format_duration(duration: Duration) -> String {
    let total_seconds = duration.as_secs();
    let hours = total_seconds / 3_600;
    let minutes = total_seconds % 3_600 / 60;
    let seconds = total_seconds % 60;
    if hours > 0 {
        format!("{hours:02}:{minutes:02}:{seconds:02}")
    } else {
        format!("{minutes:02}:{seconds:02}")
    }
}

fn selected_record_indices(record_count: usize) -> (Vec<usize>, String) {
    let sample_size = env_usize("QUERIFIER_LEETCODE_SAMPLE_SIZE", 0).min(record_count);
    if sample_size > 0 {
        let indices = (0..sample_size)
            .map(|position| ((position * 2 + 1) * record_count) / (sample_size * 2))
            .collect();
        return (
            indices,
            format!("evenly spaced sample of {sample_size}/{record_count} records"),
        );
    }

    let start = env_usize("QUERIFIER_LEETCODE_START", 0).min(record_count);
    let limit = env_usize("QUERIFIER_LEETCODE_LIMIT", 100);
    let end = start.saturating_add(limit).min(record_count);
    assert!(start < end, "the selected corpus shard is empty");
    ((start..end).collect(), format!("records {start}..{end}"))
}

const RUNTIME_BUCKET_LIMITS_MS: [f64; 12] = [
    1.0, 5.0, 10.0, 25.0, 50.0, 100.0, 250.0, 500.0, 1_000.0, 2_000.0, 5_000.0, 10_000.0,
];
const RUNTIME_BUCKET_LABELS: [&str; 13] = [
    "<1ms",
    "1-5ms",
    "5-10ms",
    "10-25ms",
    "25-50ms",
    "50-100ms",
    "100-250ms",
    "250-500ms",
    "500ms-1s",
    "1-2s",
    "2-5s",
    "5-10s",
    ">=10s",
];

fn percentile(sorted_values: &[f64], percentage: usize) -> f64 {
    let rank = sorted_values
        .len()
        .saturating_mul(percentage)
        .div_ceil(100)
        .saturating_sub(1)
        .min(sorted_values.len() - 1);
    sorted_values[rank]
}

fn print_runtime_distribution(bound: usize, runtimes: &[Duration]) {
    assert!(!runtimes.is_empty(), "runtime distribution cannot be empty");
    let mut runtime_ms: Vec<f64> = runtimes
        .iter()
        .map(|runtime| runtime.as_secs_f64() * 1_000.0)
        .collect();
    runtime_ms.sort_by(f64::total_cmp);

    let total_ms = runtime_ms.iter().sum::<f64>();
    let mean_ms = total_ms / runtime_ms.len() as f64;
    let mut bucket_counts = [0_usize; RUNTIME_BUCKET_LABELS.len()];
    for runtime in &runtime_ms {
        let bucket = RUNTIME_BUCKET_LIMITS_MS
            .iter()
            .position(|limit| runtime < limit)
            .unwrap_or(RUNTIME_BUCKET_LIMITS_MS.len());
        bucket_counts[bucket] += 1;
    }
    let histogram: Vec<(&str, usize)> = RUNTIME_BUCKET_LABELS
        .iter()
        .copied()
        .zip(bucket_counts)
        .collect();

    println!(
        "LeetCode runtime distribution: bound={bound}, count={}, \
         mean_ms={mean_ms:.3}, p50_ms={:.3}, p75_ms={:.3}, p90_ms={:.3}, \
         p95_ms={:.3}, p99_ms={:.3}, max_ms={:.3}, total_ms={total_ms:.3}, \
         histogram={histogram:?}",
        runtime_ms.len(),
        percentile(&runtime_ms, 50),
        percentile(&runtime_ms, 75),
        percentile(&runtime_ms, 90),
        percentile(&runtime_ms, 95),
        percentile(&runtime_ms, 99),
        runtime_ms[runtime_ms.len() - 1],
    );
}

fn print_slow_records(slow_records: &mut [SlowRecord]) {
    if slow_records.is_empty() {
        return;
    }

    slow_records.sort_by_key(|record| std::cmp::Reverse(record.runtime));
    let limit = env_usize("QUERIFIER_LEETCODE_SLOW_LIMIT", slow_records.len());
    for record in slow_records.iter().take(limit) {
        println!(
            "LeetCode slow record: runtime_ms={:.3}, corpus_index={}, file={:?}, record_index={}",
            record.runtime.as_secs_f64() * 1_000.0,
            record.corpus_index,
            record.file,
            record.record_index,
        );
    }
}

#[test]
#[ignore = "opt-in corpus shard test (100 records by default); run with --ignored and optional QUERIFIER_LEETCODE_* settings"]
fn run_leetcode_corpus_shard() {
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    let (record_indices, selection) = selected_record_indices(records.len());
    let bound = env_usize("QUERIFIER_LEETCODE_BOUND", 1);
    let allow_internal_errors = env_bool("QUERIFIER_LEETCODE_ALLOW_INTERNAL_ERRORS", false);
    let slow_threshold = Duration::from_millis(env_u64("QUERIFIER_LEETCODE_SLOW_MS", 0));

    let options = VerifyOptions {
        max_rows_per_table: bound,
        timeout: Duration::from_millis(env_u64("QUERIFIER_LEETCODE_TIMEOUT_MS", 2_000)),
        max_intermediate_rows: env_usize("QUERIFIER_LEETCODE_MAX_ROWS", 10_000),
        ordering_policy: if env_bool("QUERIFIER_LEETCODE_IGNORE_TOP_LEVEL_ORDER", true) {
            OrderingPolicy::IgnoreTopLevelOrder
        } else {
            OrderingPolicy::Strict
        },
        grouping_policy: if env_bool("QUERIFIER_LEETCODE_PERMISSIVE_GROUPING", true) {
            GroupingPolicy::PermissiveFirstRow
        } else {
            GroupingPolicy::Strict
        },
        coercion_policy: if env_bool("QUERIFIER_LEETCODE_MYSQL_COERCIONS", true) {
            CoercionPolicy::MySqlCompatible
        } else {
            CoercionPolicy::Strict
        },
    };
    let verifier = Verifier::new(options.clone());
    let retry_timeout = Duration::from_millis(env_u64("QUERIFIER_LEETCODE_RETRY_TIMEOUT_MS", 0));
    let retry_verifier = (retry_timeout > options.timeout).then(|| {
        Verifier::new(VerifyOptions {
            timeout: retry_timeout,
            ..options
        })
    });
    let mut coverage = Coverage::default();
    let started = Instant::now();
    let progress = ProgressReporter::new(record_indices.len());
    let mut runtimes = Vec::with_capacity(record_indices.len());
    let mut slow_records = Vec::new();
    for (offset, record_index) in record_indices.iter().enumerate() {
        let record_started = Instant::now();
        let record = &records[*record_index];
        run_record(
            record,
            &verifier,
            retry_verifier.as_ref(),
            allow_internal_errors,
            &mut coverage,
        );
        let runtime = record_started.elapsed();
        runtimes.push(runtime);
        if slow_threshold > Duration::ZERO && runtime >= slow_threshold {
            slow_records.push(SlowRecord {
                runtime,
                corpus_index: *record_index,
                file: record.file.clone(),
                record_index: record.index,
            });
        }
        progress.update(offset + 1);
    }

    println!(
        "LeetCode {selection}: true={}, false={}, adapter_unsupported={}, internal_errors={}, retries={}, retry_recovered={}, unsupported_by_kind={:?}, unsupported_reasons={:?}, false_examples={:?}, internal_examples={:?}, unsupported_examples={:?}, elapsed_ms={}",
        coverage.bounded_true,
        coverage.false_with_witness,
        coverage.adapter_unsupported,
        coverage.internal_errors,
        coverage.resource_retries,
        coverage.recovered_by_retry,
        coverage.unsupported_by_kind,
        coverage.unsupported_reasons,
        coverage.false_examples,
        coverage.internal_examples,
        coverage.unsupported_examples,
        started.elapsed().as_millis(),
    );
    print_runtime_distribution(bound, &runtimes);
    print_slow_records(&mut slow_records);
}

fn run_record(
    record: &CorpusRecord,
    verifier: &Verifier,
    retry_verifier: Option<&Verifier>,
    allow_internal_errors: bool,
    coverage: &mut Coverage,
) {
    let schema = match adapt_schema(record) {
        Ok(schema) => schema,
        Err(_) => {
            coverage.adapter_unsupported += 1;
            return;
        }
    };
    let mut result = verifier.verify(&schema, &record.pair[0], &record.pair[1]);
    if matches!(
        &result,
        VerificationResult::Unsupported { reason } if reason.kind == UnsupportedKind::Solver
    ) && let Some(retry_verifier) = retry_verifier
    {
        coverage.resource_retries += 1;
        result = retry_verifier.verify(&schema, &record.pair[0], &record.pair[1]);
        if !matches!(
            &result,
            VerificationResult::Unsupported { reason } if reason.kind == UnsupportedKind::Solver
        ) {
            coverage.recovered_by_retry += 1;
        }
    }
    match result {
        VerificationResult::True { .. } => coverage.bounded_true += 1,
        VerificationResult::False { .. } => {
            coverage.false_with_witness += 1;
            if coverage.false_examples.len() < 5 {
                coverage
                    .false_examples
                    .push(format!("{}:{}", record.file, record.index));
            }
        }
        VerificationResult::Unsupported { reason } => {
            if reason.kind == UnsupportedKind::Internal {
                assert!(
                    allow_internal_errors,
                    "internal error for {}:{}: {}",
                    record.file,
                    record.index,
                    format_args!(
                        "{}\nleft: {}\nright: {}",
                        reason.message, record.pair[0], record.pair[1]
                    )
                );
                coverage.internal_errors += 1;
                if coverage.internal_examples.len() < 5 {
                    coverage.internal_examples.push(format!(
                        "{}:{}: {}",
                        record.file, record.index, reason.message
                    ));
                }
                return;
            }
            *coverage
                .unsupported_by_kind
                .entry(reason.code())
                .or_default() += 1;
            let key = format!("{:?}: {}", reason.kind, reason.message);
            *coverage.unsupported_reasons.entry(key.clone()).or_default() += 1;
            let examples = coverage.unsupported_examples.entry(key).or_default();
            if examples.len() < 3 {
                examples.push(format!("{}:{}", record.file, record.index));
            }
            if env_bool("QUERIFIER_LEETCODE_SHOW_SQL", false) {
                println!(
                    "unsupported {}:{} [{}]\nleft: {}\nright: {}",
                    record.file,
                    record.index,
                    reason.code(),
                    record.pair[0],
                    record.pair[1],
                );
            }
        }
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

fn env_bool(name: &str, default: bool) -> bool {
    env::var(name)
        .ok()
        .and_then(|value| match value.to_ascii_lowercase().as_str() {
            "1" | "true" | "yes" | "on" => Some(true),
            "0" | "false" | "no" | "off" => Some(false),
            _ => None,
        })
        .unwrap_or(default)
}
