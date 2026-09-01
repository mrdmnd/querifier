# querifier

`querifier` checks whether two SQL queries behave the same on every database up
to a chosen size. Give it a schema and two `SELECT` statements; it asks Z3 to
search all databases with at most *n* rows in each base table.

This is useful for checking a hand-written rewrite, reviewing generated SQL, or
turning a suspicious query difference into a small concrete example. It is a
library crate, not a database proxy or a SQL runner.

The important word is **bounded**. If no difference exists through the chosen
bound, `querifier` reports bounded equivalence—not a theorem about databases of
every size. If it does find a difference, the returned database is a real
counterexample and proves that the queries are not equivalent.

The implementation follows the central idea of
[VeriEQL](https://github.com/VeriEQL/VeriEQL) and the
[VeriEQL paper](https://arxiv.org/abs/2403.03193). It is a clean-room Rust
implementation, not a translation of the upstream project.

## A first check

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
        println!("no difference through {bound} rows per table");
    }
    VerificationResult::False { counterexample } => {
        println!("these queries differ on:\n{counterexample:#?}");
    }
    VerificationResult::Unsupported { reason } => {
        println!("querifier could not check this pair: {reason}");
    }
}
```

The default bound is 2. Here the queries are equivalent through that bound:
when `value` is `NULL`, both predicates evaluate to unknown and both queries
omit the row.

`verify` has three deliberately distinct outcomes:

- `True { bound }` means the typed outputs match on every valid database with
  at most `bound` rows in each base table.
- `False { counterexample }` contains the tables and both query outputs for a
  database where they differ. The witness is replayed by a concrete evaluator
  before it is returned.
- `Unsupported { reason }` means no claim was made. This covers unsupported
  SQL, invalid schemas, complexity limits, and solver failures.

Unordered results are compared as bags, so duplicate rows matter. Ordered or
sliced results are compared as lists. Output types matter; output aliases do
not.

## Finding a counterexample

```rust
let result = Verifier::default().verify(
    &schema,
    "SELECT id FROM items WHERE value > 10",
    "SELECT id FROM items WHERE value >= 10",
);

if let VerificationResult::False { counterexample } = result {
    // Includes a row with value = 10, plus the two different query results.
    println!("{counterexample:#?}");
}
```

Schema constraints are part of the search space. Declaring primary keys,
uniqueness, foreign keys, nullability, and checks prevents the solver from
returning witnesses that your real database would reject.

## The low-bound footguns

A small bound is excellent at finding small bugs. It is not evidence that a
larger database cannot expose one.

### n = 1 can hide duplicate behavior

With at most one row, these queries are equivalent:

```sql
SELECT value FROM items;
SELECT DISTINCT value FROM items;
```

At `n = 2`, they are not. A legal witness is:

```text
items
id | value
---+------
1  | 7
2  | 7
```

The first query returns two copies of `7`; the second returns one. A
`True { bound: 1 }` result only ruled out one-row counterexamples.

### n = 2 can hide three-row interactions

These queries both return an empty bag for every `items` table with at most two
rows:

```sql
SELECT a.id
FROM items a, items b, items c
WHERE a.id < b.id AND b.id < c.id;

SELECT id
FROM items
WHERE id <> id;
```

At `n = 3`, IDs `1`, `2`, and `3` make the first query return `1`, while the
second query remains empty. Aliasing a table three times does not give each
alias its own bound: the bound applies to the underlying base table.

You can check several bounds in one call:

```rust
use querifier::BoundSearchOrder;

let results = Verifier::default()
    .verify_bounds(
        &schema,
        "SELECT a.id FROM items a, items b, items c \
         WHERE a.id < b.id AND b.id < c.id",
        "SELECT id FROM items WHERE id <> id",
        &[1, 2, 3],
        BoundSearchOrder::LargestFirst,
    )
    .expect("bounds must be positive");
```

`verify_bounds` uses monotonicity: a proof at a larger bound also covers smaller
bounds, and a witness remains valid at every bound large enough to contain it.
In practice, choose bounds that can express the cardinality pattern you are
trying to check, and increase them when the query contains self-joins,
duplicate-sensitive operations, or thresholded aggregates.

## Configuration

```rust
use std::time::Duration;
use querifier::{Verifier, VerifyOptions};

let verifier = Verifier::new(VerifyOptions {
    max_rows_per_table: 3,
    timeout: Duration::from_secs(10),
    max_intermediate_rows: 20_000,
    ..VerifyOptions::default()
});
```

The strict defaults preserve top-level ordering, enforce standard grouping
rules (including known functional dependencies), and reject implicit
MySQL-style coercions. Compatibility policies are available explicitly for
corpus analysis.

## Supported SQL

The supported fragment is broad enough for joins, subqueries, aggregates, and
many analytical queries:

- bag-aware projection, filtering, `DISTINCT`, and set operations, including
  `ALL`;
- inner, cross, left/right/full outer, natural, and `USING` joins;
- nullable integer, boolean, text, enum, date, time, and exact numeric values
  with SQL three-valued logic;
- arithmetic, comparisons, row-valued `IN`, `CASE`, casts, `COALESCE`,
  `IFNULL`, `BETWEEN`, and a set of exactly encoded numeric, string, and date
  functions;
- `COUNT`, `SUM`, `AVG`, `MIN`, and `MAX`, including aggregate `DISTINCT`,
  `GROUP BY`, and `HAVING`;
- derived tables, correlated and uncorrelated `EXISTS`/`IN` subqueries,
  statically single-row scalar subqueries, and non-recursive CTEs;
- a restricted set of ranking, aggregate, and `FIRST_VALUE` window functions;
- `ORDER BY`, explicit NULL ordering, `LIMIT`, and `OFFSET`.

An untyped standalone `NULL` projection is unsupported because its output type
is ambiguous. NULLs originating from columns and typed expressions are modeled.

Unsupported constructs return `Unsupported` instead of being approximated.
Notable gaps include recursive CTEs, `LATERAL`, general window frames, grouping
sets, general `LIKE` patterns, regular expressions, arrays, JSON, non-day
intervals, quoted or schema-qualified identifiers, runtime SQL errors, and
implementation-defined ordering. Comparing an ordered result with an unordered
result is unsupported under the default policy.

Recursive expansion and symbolic intermediate relations have explicit
complexity limits. Reaching a limit never produces an equivalence claim.

## VeriEQL LeetCode corpus

The vendored 23,994-pair corpus lives at
`tests/data/verieql/leetcode.jsonlines`. It is a coverage workload, not a
correctness oracle: each record pairs a reference solution with an accepted
submission, but does not provide an authoritative equivalence label.

Provenance and the CC BY-NC-SA 4.0 notice are in
`tests/data/verieql/README.md`, `tests/data/verieql/LICENSE.md`, and
`THIRD_PARTY_NOTICES.md`. The corpus includes third-party submissions;
commercial use or redistribution requires an independent rights review.
Coverage, timing, opt-in runner settings, and known gaps are documented in
`tests/data/verieql/COVERAGE.md`.

For example, this runs a 100-record compatibility-profile shard at bound 1:

```sh
QUERIFIER_LEETCODE_START=0 \
QUERIFIER_LEETCODE_LIMIT=100 \
QUERIFIER_LEETCODE_BOUND=1 \
QUERIFIER_LEETCODE_TIMEOUT_MS=2000 \
QUERIFIER_LEETCODE_RETRY_TIMEOUT_MS=10000 \
cargo test --test leetcode_corpus run_leetcode_corpus_shard -- --ignored --exact --nocapture
```

Set `QUERIFIER_LEETCODE_IGNORE_TOP_LEVEL_ORDER=false`,
`QUERIFIER_LEETCODE_PERMISSIVE_GROUPING=false`, and
`QUERIFIER_LEETCODE_MYSQL_COERCIONS=false` to run with the library's strict
policies instead.

## Build and test

Z3 is vendored for reproducible builds, so building requires a Rust toolchain,
CMake, and a C++ compiler.

```sh
cargo test
cargo clippy --all-targets --all-features -- -D warnings
cargo fmt --all -- --check
```
