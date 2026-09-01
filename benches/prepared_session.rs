use std::env;
use std::hint::black_box;
use std::time::{Duration, Instant};

use querifier::{Column, DataType, Schema, Table, VerificationResult, Verifier, VerifyOptions};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Outcome {
    True,
    False,
    Unsupported,
}

#[derive(Clone, Copy)]
enum UniqueMode {
    Compare,
    Fresh,
    Prepared,
}

#[derive(Clone, Copy)]
struct QueryPair {
    name: &'static str,
    left: &'static str,
    right: &'static str,
}

struct OwnedQueryPair {
    left: String,
    right: String,
    expected: Outcome,
}

const PAIRS: &[QueryPair] = &[
    QueryPair {
        name: "false_filter",
        left: "SELECT id FROM items WHERE value > 1",
        right: "SELECT id FROM items WHERE value > 2",
    },
    QueryPair {
        name: "true_predicate",
        left: "SELECT id FROM items WHERE NOT (value > 25)",
        right: "SELECT id FROM items WHERE value <= 25",
    },
    QueryPair {
        name: "true_boolean",
        left: "SELECT id FROM items WHERE flag",
        right: "SELECT id FROM items WHERE NOT NOT flag",
    },
    QueryPair {
        name: "true_aggregate",
        left: "SELECT flag, COUNT(*) FROM items GROUP BY flag",
        right: "SELECT flag, COUNT(1) FROM items GROUP BY flag",
    },
    QueryPair {
        name: "false_join",
        left: "SELECT a.id FROM items a JOIN items b ON a.id = b.id",
        right: "SELECT id FROM items",
    },
];

fn main() {
    let trials = env_usize("QUERIFIER_PREPARED_TRIALS", 5).max(1);
    let repetitions = env_usize("QUERIFIER_PREPARED_REPETITIONS", 20).max(1);
    let unique_pairs = env_usize("QUERIFIER_PREPARED_UNIQUE_PAIRS", 100).max(1);
    let refresh_calls = env_usize("QUERIFIER_PREPARED_REFRESH_CALLS", 25).max(1);
    let verifier = Verifier::new(VerifyOptions {
        max_rows_per_table: 2,
        ..VerifyOptions::default()
    });
    let schema = Schema::new([Table::new(
        "items",
        [
            Column::not_null("id", DataType::Integer),
            Column::nullable("value", DataType::Integer),
            Column::nullable("flag", DataType::Boolean),
        ],
    )]);
    let jobs = build_jobs(repetitions);

    black_box(run_fresh(&verifier, &schema, &jobs));
    black_box(run_prepared(&verifier, &schema, &jobs));

    let mut fresh_trials = Vec::with_capacity(trials);
    let mut prepared_trials = Vec::with_capacity(trials);
    let mut preparation_trials = Vec::with_capacity(trials);
    for trial in 1..=trials {
        if trial % 2 == 1 {
            fresh_trials.push(run_fresh(&verifier, &schema, &jobs));
            let (total, preparation) = run_prepared(&verifier, &schema, &jobs);
            prepared_trials.push(total);
            preparation_trials.push(preparation);
        } else {
            let (total, preparation) = run_prepared(&verifier, &schema, &jobs);
            prepared_trials.push(total);
            preparation_trials.push(preparation);
            fresh_trials.push(run_fresh(&verifier, &schema, &jobs));
        }
        println!(
            "prepared_session_trial trial={trial} calls={} fresh_ms={:.3} prepared_ms={:.3} preparation_ms={:.3}",
            jobs.len(),
            fresh_trials[trial - 1].as_secs_f64() * 1_000.0,
            prepared_trials[trial - 1].as_secs_f64() * 1_000.0,
            preparation_trials[trial - 1].as_secs_f64() * 1_000.0,
        );
    }

    fresh_trials.sort_unstable();
    prepared_trials.sort_unstable();
    preparation_trials.sort_unstable();
    let fresh = median(&fresh_trials);
    let prepared = median(&prepared_trials);
    let preparation = median(&preparation_trials);
    println!(
        "prepared_session_summary trials={trials} calls={} fresh_median_ms={:.3} prepared_median_ms={:.3} preparation_median_ms={:.3} speedup={:.3}",
        jobs.len(),
        fresh.as_secs_f64() * 1_000.0,
        prepared.as_secs_f64() * 1_000.0,
        preparation.as_secs_f64() * 1_000.0,
        fresh.as_secs_f64() / prepared.as_secs_f64(),
    );

    benchmark_unique_pairs(&verifier, &schema, trials, unique_pairs, refresh_calls);
}

fn benchmark_unique_pairs(
    verifier: &Verifier,
    schema: &Schema,
    trials: usize,
    pair_count: usize,
    refresh_calls: usize,
) {
    let jobs = (0..pair_count)
        .map(|index| {
            let threshold = i64::try_from(index).unwrap_or(i64::MAX - 1);
            if index % 2 == 0 {
                OwnedQueryPair {
                    left: format!("SELECT id FROM items WHERE value > {threshold}"),
                    right: format!(
                        "SELECT id FROM items WHERE value >= {}",
                        threshold.saturating_add(1)
                    ),
                    expected: Outcome::True,
                }
            } else {
                OwnedQueryPair {
                    left: format!("SELECT id FROM items WHERE value > {threshold}"),
                    right: format!(
                        "SELECT id FROM items WHERE value > {}",
                        threshold.saturating_add(1)
                    ),
                    expected: Outcome::False,
                }
            }
        })
        .collect::<Vec<_>>();

    match unique_mode() {
        UniqueMode::Fresh => {
            let elapsed = run_unique_fresh(verifier, schema, &jobs, false);
            println!(
                "prepared_session_unique_isolated mode=fresh calls={} runtime_ms={:.3}",
                jobs.len(),
                elapsed.as_secs_f64() * 1_000.0,
            );
            return;
        }
        UniqueMode::Prepared => {
            let (elapsed, preparation) =
                run_unique_prepared(verifier, schema, &jobs, false, refresh_calls);
            println!(
                "prepared_session_unique_isolated mode=prepared calls={} refresh_calls={refresh_calls} runtime_ms={:.3} preparation_ms={:.3}",
                jobs.len(),
                elapsed.as_secs_f64() * 1_000.0,
                preparation.as_secs_f64() * 1_000.0,
            );
            return;
        }
        UniqueMode::Compare => {}
    }

    black_box(run_unique_fresh(verifier, schema, &jobs, false));
    black_box(run_unique_prepared(
        verifier,
        schema,
        &jobs,
        false,
        refresh_calls,
    ));
    let mut fresh_trials = Vec::with_capacity(trials);
    let mut prepared_trials = Vec::with_capacity(trials);
    let mut preparation_trials = Vec::with_capacity(trials);
    for trial in 1..=trials {
        let reverse = trial % 2 == 0;
        if trial % 2 == 1 {
            fresh_trials.push(run_unique_fresh(verifier, schema, &jobs, reverse));
            let (prepared, preparation) =
                run_unique_prepared(verifier, schema, &jobs, reverse, refresh_calls);
            prepared_trials.push(prepared);
            preparation_trials.push(preparation);
        } else {
            let (prepared, preparation) =
                run_unique_prepared(verifier, schema, &jobs, reverse, refresh_calls);
            prepared_trials.push(prepared);
            preparation_trials.push(preparation);
            fresh_trials.push(run_unique_fresh(verifier, schema, &jobs, reverse));
        }
        println!(
            "prepared_session_unique_trial trial={trial} calls={} refresh_calls={refresh_calls} fresh_ms={:.3} prepared_ms={:.3} preparation_ms={:.3}",
            jobs.len(),
            fresh_trials[trial - 1].as_secs_f64() * 1_000.0,
            prepared_trials[trial - 1].as_secs_f64() * 1_000.0,
            preparation_trials[trial - 1].as_secs_f64() * 1_000.0,
        );
    }
    fresh_trials.sort_unstable();
    prepared_trials.sort_unstable();
    preparation_trials.sort_unstable();
    let fresh = median(&fresh_trials);
    let prepared = median(&prepared_trials);
    let preparation = median(&preparation_trials);
    println!(
        "prepared_session_unique_summary trials={trials} calls={} refresh_calls={refresh_calls} fresh_median_ms={:.3} prepared_median_ms={:.3} preparation_median_ms={:.3} speedup={:.3}",
        jobs.len(),
        fresh.as_secs_f64() * 1_000.0,
        prepared.as_secs_f64() * 1_000.0,
        preparation.as_secs_f64() * 1_000.0,
        fresh.as_secs_f64() / prepared.as_secs_f64(),
    );
}

fn build_jobs(repetitions: usize) -> Vec<QueryPair> {
    let mut jobs = Vec::with_capacity(PAIRS.len() * repetitions);
    for repetition in 0..repetitions {
        for offset in 0..PAIRS.len() {
            jobs.push(PAIRS[(offset + repetition) % PAIRS.len()]);
        }
    }
    jobs
}

fn run_fresh(verifier: &Verifier, schema: &Schema, jobs: &[QueryPair]) -> Duration {
    let started = Instant::now();
    let outcomes = jobs
        .iter()
        .map(|pair| {
            black_box(pair.name);
            outcome(verifier.verify(schema, pair.left, pair.right))
        })
        .collect::<Vec<_>>();
    let elapsed = started.elapsed();
    validate_outcomes(jobs, &outcomes);
    elapsed
}

fn run_prepared(verifier: &Verifier, schema: &Schema, jobs: &[QueryPair]) -> (Duration, Duration) {
    let started = Instant::now();
    let (body, outcomes) = verifier
        .with_prepared(schema, |prepared| {
            let body_started = Instant::now();
            let outcomes = jobs
                .iter()
                .map(|pair| {
                    black_box(pair.name);
                    outcome(prepared.verify(pair.left, pair.right))
                })
                .collect::<Vec<_>>();
            (body_started.elapsed(), outcomes)
        })
        .expect("the benchmark schema should be preparable");
    let elapsed = started.elapsed();
    validate_outcomes(jobs, &outcomes);
    (elapsed, elapsed.saturating_sub(body))
}

fn run_unique_fresh(
    verifier: &Verifier,
    schema: &Schema,
    jobs: &[OwnedQueryPair],
    reverse: bool,
) -> Duration {
    let started = Instant::now();
    let outcomes = (0..jobs.len())
        .map(|offset| {
            let pair = &jobs[ordered_index(jobs.len(), offset, reverse)];
            outcome(verifier.verify(schema, &pair.left, &pair.right))
        })
        .collect::<Vec<_>>();
    let elapsed = started.elapsed();
    validate_unique_outcomes(jobs, &outcomes, reverse);
    elapsed
}

fn run_unique_prepared(
    verifier: &Verifier,
    schema: &Schema,
    jobs: &[OwnedQueryPair],
    reverse: bool,
    refresh_calls: usize,
) -> (Duration, Duration) {
    let started = Instant::now();
    let mut body = Duration::ZERO;
    let mut outcomes = Vec::with_capacity(jobs.len());
    for chunk_start in (0..jobs.len()).step_by(refresh_calls) {
        let chunk_end = chunk_start.saturating_add(refresh_calls).min(jobs.len());
        let (chunk_body, chunk_outcomes) = verifier
            .with_prepared(schema, |prepared| {
                let body_started = Instant::now();
                let outcomes = (chunk_start..chunk_end)
                    .map(|offset| {
                        let pair = &jobs[ordered_index(jobs.len(), offset, reverse)];
                        outcome(prepared.verify(&pair.left, &pair.right))
                    })
                    .collect::<Vec<_>>();
                (body_started.elapsed(), outcomes)
            })
            .expect("the benchmark schema should be preparable");
        body += chunk_body;
        outcomes.extend(chunk_outcomes);
    }
    let elapsed = started.elapsed();
    validate_unique_outcomes(jobs, &outcomes, reverse);
    (elapsed, elapsed.saturating_sub(body))
}

fn ordered_index(length: usize, offset: usize, reverse: bool) -> usize {
    if reverse { length - offset - 1 } else { offset }
}

fn validate_unique_outcomes(jobs: &[OwnedQueryPair], outcomes: &[Outcome], reverse: bool) {
    assert_eq!(jobs.len(), outcomes.len());
    for (offset, actual) in outcomes.iter().enumerate() {
        let pair = &jobs[ordered_index(jobs.len(), offset, reverse)];
        assert_eq!(
            *actual,
            pair.expected,
            "prepared-session unique outcome changed at job index {}",
            ordered_index(jobs.len(), offset, reverse)
        );
    }
}

fn validate_outcomes(jobs: &[QueryPair], outcomes: &[Outcome]) {
    for (pair, actual) in jobs.iter().zip(outcomes) {
        let expected = match pair.name {
            "false_filter" | "false_join" => Outcome::False,
            "true_predicate" | "true_boolean" | "true_aggregate" => Outcome::True,
            _ => unreachable!("all benchmark pairs have calibrated outcomes"),
        };
        assert_eq!(
            *actual, expected,
            "prepared-session benchmark outcome changed for {}",
            pair.name
        );
    }
}

fn outcome(result: VerificationResult) -> Outcome {
    match result {
        VerificationResult::True { .. } => Outcome::True,
        VerificationResult::False { .. } => Outcome::False,
        VerificationResult::Unsupported { .. } => Outcome::Unsupported,
    }
}

fn median(values: &[Duration]) -> Duration {
    let middle = values.len() / 2;
    if values.len().is_multiple_of(2) {
        (values[middle - 1] + values[middle]) / 2
    } else {
        values[middle]
    }
}

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn unique_mode() -> UniqueMode {
    match env::var("QUERIFIER_PREPARED_UNIQUE_MODE").as_deref() {
        Ok("fresh") => UniqueMode::Fresh,
        Ok("prepared") => UniqueMode::Prepared,
        Ok("compare") | Err(_) => UniqueMode::Compare,
        Ok(value) => panic!(
            "QUERIFIER_PREPARED_UNIQUE_MODE must be fresh, prepared, or compare; got {value:?}"
        ),
    }
}
