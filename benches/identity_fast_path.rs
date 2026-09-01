#[path = "../tests/support/mod.rs"]
mod support;

use std::env;
use std::hint::black_box;
use std::time::{Duration, Instant};

use querifier::{
    CoercionPolicy, GroupingPolicy, OrderingPolicy, VerificationResult, Verifier, VerifyOptions,
};
use support::leetcode::{adapt_schema, load_corpus, validate_corpus};

const SOURCE_FILE: &str = "benchmark/leetcode/raw_data/1364.csv";
const SOURCE_INDEX: usize = 391;

struct IdentityCase {
    name: &'static str,
    left_sql: String,
    right_sql: String,
    expected_fast_path: bool,
}

fn main() {
    let iterations = env_usize("QUERIFIER_IDENTITY_ITERATIONS", 10).max(1);
    let warmup = env_usize("QUERIFIER_IDENTITY_WARMUP", 1);
    let bound = env_usize("QUERIFIER_IDENTITY_BOUND", 3).max(1);
    let validate_fast_path = env_bool("QUERIFIER_IDENTITY_VALIDATE_FAST_PATH", true);
    let records = load_corpus().expect("the vendored VeriEQL corpus should load");
    validate_corpus(&records).expect("the vendored VeriEQL corpus should be valid");
    let record = records
        .iter()
        .find(|record| record.file == SOURCE_FILE && record.index == SOURCE_INDEX)
        .expect("the identity benchmark source case should exist");
    let schema = adapt_schema(record).expect("the identity benchmark schema should adapt");
    let source = record.pair[0].clone();
    let cases = [
        IdentityCase {
            name: "byte_identical_complex",
            left_sql: source.clone(),
            right_sql: source.clone(),
            expected_fast_path: true,
        },
        IdentityCase {
            name: "formatting_only_complex",
            left_sql: source.clone(),
            right_sql: format!("\n  {source}\n"),
            expected_fast_path: true,
        },
        IdentityCase {
            name: "alias_only_fallback",
            left_sql: "SELECT I.INVOICE_ID FROM INVOICES I".to_owned(),
            right_sql: "SELECT J.INVOICE_ID FROM INVOICES J".to_owned(),
            expected_fast_path: false,
        },
        IdentityCase {
            name: "structural_equivalence_fallback",
            left_sql: "SELECT INVOICE_ID FROM INVOICES WHERE PRICE > 0".to_owned(),
            right_sql: "SELECT INVOICE_ID FROM INVOICES WHERE NOT NOT (PRICE > 0)".to_owned(),
            expected_fast_path: false,
        },
    ];
    let verifier = Verifier::new(VerifyOptions {
        max_rows_per_table: bound,
        timeout: Duration::from_secs(5),
        max_intermediate_rows: 10_000,
        ordering_policy: OrderingPolicy::IgnoreTopLevelOrder,
        grouping_policy: GroupingPolicy::PermissiveFirstRow,
        coercion_policy: CoercionPolicy::MySqlCompatible,
    });

    println!(
        "identity_config bound={bound} iterations={iterations} warmup={warmup} cases={} validate_fast_path={validate_fast_path}",
        cases.len()
    );
    for case in &cases {
        for _ in 0..warmup {
            black_box(verifier.verify(&schema, &case.left_sql, &case.right_sql));
        }
        for iteration in 1..=iterations {
            let started = Instant::now();
            let report = verifier.verify_with_metrics(&schema, &case.left_sql, &case.right_sql);
            let runtime = started.elapsed();
            assert!(
                matches!(report.result, VerificationResult::True { .. }),
                "{} returned {:?}",
                case.name,
                report.result
            );
            let fast_path = report.counters.identical_plan_fast_paths == 1;
            if validate_fast_path {
                assert_eq!(
                    fast_path, case.expected_fast_path,
                    "{} took an unexpected path",
                    case.name
                );
            }
            println!(
                "identity_case name={} bound={bound} iteration={iteration} runtime_ms={:.3} fast_path={fast_path} schema_check_ms={:.3} left_encode_ms={:.3} right_encode_ms={:.3} final_check_ms={:.3}",
                case.name,
                runtime.as_secs_f64() * 1_000.0,
                report.phases.schema_solver_check.as_secs_f64() * 1_000.0,
                report.phases.left_relation_encoding.as_secs_f64() * 1_000.0,
                report.phases.right_relation_encoding.as_secs_f64() * 1_000.0,
                report.phases.final_solver_check.as_secs_f64() * 1_000.0,
            );
            black_box(report);
        }
    }
}

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn env_bool(name: &str, default: bool) -> bool {
    env::var(name)
        .ok()
        .and_then(|value| match value.as_str() {
            "1" | "true" | "TRUE" => Some(true),
            "0" | "false" | "FALSE" => Some(false),
            _ => None,
        })
        .unwrap_or(default)
}
