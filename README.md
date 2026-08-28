# querifier

`querifier` is a small Rust library for bounded SQL query equivalence checking. It follows the central idea from [VeriEQL](https://github.com/VeriEQL/VeriEQL): represent every database up to a row bound symbolically, ask Z3 for a database on which two queries differ, and decode a satisfying model into a counterexample.

This is a clean-room implementation of the bounded algorithm described in the [VeriEQL paper](https://arxiv.org/abs/2403.03193), not a translation of the upstream implementation.

## Result contract

`Verifier::verify` returns one of three results:

- `True { bound }`: the typed result bags are equal for every database with at most `bound` rows in each base table. This is not a proof of unbounded equivalence.
- `False { counterexample }`: the included concrete database makes the typed result bags differ. The library re-evaluates both typed queries over the decoded model before returning it.
- `Unsupported { reason }`: the schema, SQL, resource limits, or solver fell outside the supported boundary. No equivalence claim is made.

An unsatisfiable search proves bounded equivalence. A satisfying search gives a genuine non-equivalence witness, regardless of the bound used to find it.

## Example

```rust
use querifier::{
    Column, DataType, Schema, Table, VerificationResult, Verifier,
};

let schema = Schema::new([
    Table::new(
        "items",
        [
            Column::not_null("id", DataType::Integer),
            Column::nullable("value", DataType::Integer),
        ],
    )
    .with_primary_key(["id"]),
]);

let result = Verifier::default().verify(
    &schema,
    "SELECT id FROM items WHERE NOT (value > 25)",
    "SELECT id FROM items WHERE value <= 25",
);

match result {
    VerificationResult::True { bound } => {
        println!("equivalent through {bound} rows per table");
    }
    VerificationResult::False { counterexample } => {
        println!("different on: {counterexample:#?}");
    }
    VerificationResult::Unsupported { reason } => {
        println!("unsupported: {reason}");
    }
}
```

The default bound is 2 rows per table. Use `Verifier::new(VerifyOptions { .. })` to configure the bound, Z3 timeout, maximum symbolic intermediate relation size, and explicit ordering, grouping, and coercion policies. Strict SQL behavior is the library default; corpus-compatibility behavior is opt-in.

## Supported SQL

The implemented bounded fragment includes:

- Bag semantics for projection, filtering, `DISTINCT`, and `UNION`/`INTERSECT`/`EXCEPT`, including `ALL` variants.
- Inner, cross, left/right/full outer, natural, and `USING` joins with SQL NULL extension.
- Integer, boolean, text, enum, date, time, and exact numeric values, including nullable columns.
- Arithmetic, comparisons, SQL three-valued boolean logic, row comparisons, multi-column `IN`, `CASE`, casts, `COALESCE`/`IFNULL`, and `BETWEEN`.
- Exact encodings for common numeric, string, and day-based date functions, including `ABS`, `ROUND`, `TRUNCATE`, `POWER`, `CONCAT`, restricted `LIKE`, `DATEDIFF`, `DATE_ADD`/`DATE_SUB`, `TO_DAYS`, date parts, and literal `STR_TO_DATE`.
- `COUNT`, `SUM`, `AVG`, `MIN`, and `MAX`, with aggregate `DISTINCT`, `GROUP BY`, and `HAVING`.
- Derived tables, correlated and uncorrelated `EXISTS`/`IN` subqueries, statically single-row scalar subqueries, and non-recursive CTEs.
- Restricted `ROW_NUMBER`, `RANK`, `DENSE_RANK`, windowed aggregates, and `FIRST_VALUE`, including arithmetic over window results.
- `ORDER BY`, explicit NULL ordering, `LIMIT`, and `OFFSET`; ordered or sliced queries are compared as lists.
- Functional-dependency-aware strict grouping plus an explicit deterministic representative-row compatibility profile.
- Unquoted, case-insensitive table names, column names, aliases, wildcards, and positional grouping/ordering.
- NOT NULL, primary key, unique, foreign key, comparison/range/inclusion/implication checks, auto-increment, and consecutive-value constraints.
- SQL result-row equality in which NULL matches NULL, while predicate equality involving NULL is unknown.

An untyped standalone `NULL` projection is unsupported because its output type is ambiguous. NULL values from columns and typed predicate contexts are fully modeled.

## Explicitly unsupported

Unsupported constructs return a structured reason instead of being approximated. Important remaining gaps include:

- Recursive CTEs, `LATERAL`, semi/anti/ASOF/APPLY joins, and scalar subqueries not statically bounded to one row.
- General window frames, aggregate filters/ordering, grouping sets, `FETCH`, and unsupported dialect-specific query clauses.
- General `LIKE` patterns, regular expressions, arrays, JSON, non-day intervals, dynamic text/date parsing, and scalar functions without an exact encoding.
- Quoted identifiers, schema-qualified names, and dialect-specific name-resolution behavior.
- Runtime SQL errors and implementation-defined ordering. An ordered query cannot be compared with an unordered query.

Recursive nesting and symbolic intermediate sizes are guarded by complexity limits. Hitting one returns `Unsupported`, never an equivalence claim.

## VeriEQL LeetCode corpus

The exact 23,994-pair corpus is vendored at `tests/data/verieql/leetcode.jsonlines`. Its provenance and CC BY-NC-SA 4.0 notice are in `tests/data/verieql/README.md`, `tests/data/verieql/LICENSE.md`, and `THIRD_PARTY_NOTICES.md`. The corpus includes third-party submissions; commercial use or redistribution requires an independent rights review.

The corpus is a coverage workload, not a correctness oracle. It pairs a reference solution with an accepted submission but has no authoritative equivalence labels. Default tests validate the complete dataset and run a small set of manually reviewed bounded cases. Run an opt-in shard with:

```sh
QUERIFIER_LEETCODE_START=0 \
QUERIFIER_LEETCODE_LIMIT=100 \
QUERIFIER_LEETCODE_BOUND=1 \
QUERIFIER_LEETCODE_TIMEOUT_MS=2000 \
QUERIFIER_LEETCODE_RETRY_TIMEOUT_MS=10000 \
cargo test --test leetcode_corpus run_leetcode_corpus_shard -- --ignored --exact --nocapture
```

`QUERIFIER_LEETCODE_MAX_ROWS` controls the maximum symbolic intermediate relation size. The corpus runner defaults to its compatibility profile; set `QUERIFIER_LEETCODE_IGNORE_TOP_LEVEL_ORDER=false`, `QUERIFIER_LEETCODE_PERMISSIVE_GROUPING=false`, or `QUERIFIER_LEETCODE_MYSQL_COERCIONS=false` to measure strict behavior. `QUERIFIER_LEETCODE_SHOW_SQL=true` prints each unsupported pair. Current measured coverage, timing, and known gaps are recorded in `tests/data/verieql/COVERAGE.md`.

## Build and test

The Z3 dependency is vendored for reproducible builds. Building it requires a working Rust toolchain, CMake, and a C++ compiler.

```sh
cargo test
cargo clippy --all-targets --all-features -- -D warnings
cargo fmt --all -- --check
```
