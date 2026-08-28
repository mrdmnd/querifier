mod support;

use std::collections::BTreeMap;
use std::env;
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
    resource_retries: usize,
    recovered_by_retry: usize,
    unsupported_by_kind: BTreeMap<&'static str, usize>,
    unsupported_reasons: BTreeMap<String, usize>,
    false_examples: Vec<String>,
    unsupported_examples: BTreeMap<String, Vec<String>>,
}

#[test]
#[ignore = "large opt-in corpus benchmark; configure with QUERIFIER_LEETCODE_* variables"]
fn run_leetcode_corpus_shard() {
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    let start = env_usize("QUERIFIER_LEETCODE_START", 0).min(records.len());
    let limit = env_usize("QUERIFIER_LEETCODE_LIMIT", 100);
    let end = start.saturating_add(limit).min(records.len());
    assert!(start < end, "the selected corpus shard is empty");

    let options = VerifyOptions {
        max_rows_per_table: env_usize("QUERIFIER_LEETCODE_BOUND", 1),
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
    for record in &records[start..end] {
        run_record(record, &verifier, retry_verifier.as_ref(), &mut coverage);
    }

    println!(
        "LeetCode records {start}..{end}: true={}, false={}, adapter_unsupported={}, retries={}, retry_recovered={}, unsupported_by_kind={:?}, unsupported_reasons={:?}, false_examples={:?}, unsupported_examples={:?}, elapsed_ms={}",
        coverage.bounded_true,
        coverage.false_with_witness,
        coverage.adapter_unsupported,
        coverage.resource_retries,
        coverage.recovered_by_retry,
        coverage.unsupported_by_kind,
        coverage.unsupported_reasons,
        coverage.false_examples,
        coverage.unsupported_examples,
        started.elapsed().as_millis(),
    );
}

fn run_record(
    record: &CorpusRecord,
    verifier: &Verifier,
    retry_verifier: Option<&Verifier>,
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
            assert_ne!(
                reason.kind,
                UnsupportedKind::Internal,
                "internal error for {}:{}: {}",
                record.file,
                record.index,
                format_args!(
                    "{}\nleft: {}\nright: {}",
                    reason.message, record.pair[0], record.pair[1]
                )
            );
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
