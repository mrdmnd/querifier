# LeetCode corpus coverage

This file records coverage of the vendored VeriEQL LeetCode workload. The corpus is not a correctness oracle: its query pairs have no authoritative equivalence labels. `True` below means bounded equivalence, and every `False` includes a counterexample that was replayed by the independent concrete evaluator.

## 2026-08-27 post-expansion sample

Four disjoint 1,000-record regions were rerun after the feature-parity expansion.

Configuration:

- Records: `0..1000`, `6000..7000`, `10000..11000`, and `18000..19000`
- Bound: 1 row per base table
- Initial solver timeout: 2 seconds
- Retry timeout: 10 seconds
- Maximum symbolic intermediate rows: 10,000
- Compatibility profile: ignore unsliced top-level ordering, deterministic first-row grouping, and exact MySQL coercions
- Build: debug test profile on macOS

Aggregate outcomes:

- `True`: 2,522 (63.05%)
- `False` with a replayed witness: 1,416 (35.40%)
- `Unsupported`: 62 (1.55%)
- Records reaching a bounded verdict: 3,938 (98.45%)
- Solver retries: 7; recovered by retry: 3; remaining solver timeouts: 4
- Schema-adapter failures: 0
- Internal verifier errors after the representative-row replay fix: 0

Shard outcomes:

- Records `0..1000`: 817 true, 178 false, 5 unsupported.
- Records `6000..7000`: 863 true, 101 false, 36 unsupported, including 4 solver timeouts after retry.
- Records `10000..11000`: 302 true, 682 false, 16 unsupported.
- Records `18000..19000`: 540 true, 455 false, 5 unsupported.

The remaining sample failures are concentrated in malformed or ambiguous submissions, unquoted tokens used as `LIKE` patterns, case conversion and string aggregation, deliberately unsupported implicit text/number conversion, nested aggregates, and four resource-limited solver checks. Compatibility behavior is selected explicitly; strict library defaults remain unchanged.

## 2026-08-27 baseline full run

Configuration:

- Corpus: all 23,994 records in four contiguous shards
- Bound: 1 row per base table
- Per-solver timeout: 250 ms
- Maximum symbolic intermediate rows: 10,000
- Build: debug test profile on macOS

Aggregate outcomes:

- `True`: 8,084 (33.69%)
- `False` with a replayed witness: 3,073 (12.81%)
- `Unsupported`: 12,837 (53.50%)
- Schema-adapter failures: 0
- Records reaching a bounded verdict: 11,157 (46.50%)
- Internal verifier errors: 0

Shard outcomes and elapsed process time:

- Records 0..6000: 1,904 true, 758 false, 3,338 unsupported; 77.188 s
- Records 6000..12000: 1,875 true, 885 false, 3,240 unsupported; 149.925 s
- Records 12000..18000: 2,569 true, 811 false, 2,620 unsupported; 260.635 s
- Records 18000..23994: 1,736 true, 619 false, 3,639 unsupported; 48.356 s

The shards ran concurrently, so their elapsed times must not be added to estimate wall-clock duration. The slowest shard completed in about 261 seconds.

## Dominant remaining gaps

The runner reports exact counts and sample `(file, index)` keys for every unsupported reason. The largest families in this run were:

- MySQL grouping behavior not captured by strict grouped-expression validation: 3,668 records reported a projected or `HAVING` column outside `GROUP BY`.
- Unsupported arithmetic coercions, especially date/time and permissive MySQL coercions: 1,276 records.
- Ordered-versus-unordered query pairs whose result contracts cannot safely be compared: 1,031 records.
- Multi-column or otherwise invalid-for-scalar `IN` subqueries: 945 records.
- Solver timeout at the deliberately short 250 ms limit: 832 records.
- Windowed/ordered/filtered functions: 814 records.
- Dialect-specific `SELECT` modifiers or window clauses: 773 records.
- Name-resolution differences, malformed submissions, `LIKE`/regular expressions, date arithmetic/functions, `GROUP_CONCAT`, tuple expressions, recursive CTEs, and permissive string/numeric coercions account for most of the remainder.

The baseline used strict semantics and predates the explicit compatibility profiles. Unsupported syntax is not silently approximated: the compatibility runner selects every relaxation explicitly, and increasing the timeout only changes resource-limited outcomes.

## Reproduction

Run one shard with:

```sh
QUERIFIER_LEETCODE_START=0 \
QUERIFIER_LEETCODE_LIMIT=6000 \
QUERIFIER_LEETCODE_BOUND=1 \
QUERIFIER_LEETCODE_TIMEOUT_MS=250 \
QUERIFIER_LEETCODE_RETRY_TIMEOUT_MS=2000 \
QUERIFIER_LEETCODE_MAX_ROWS=10000 \
cargo test --test leetcode_corpus run_leetcode_corpus_shard -- --ignored --exact --nocapture
```

Use starts `0`, `6000`, `12000`, and `18000`, with limits `6000`, `6000`, `6000`, and `5994`, to run the complete corpus. Set the three compatibility environment variables documented in the project README to `false` when reproducing the historical strict baseline.
