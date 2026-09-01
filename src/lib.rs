#![forbid(unsafe_code)]
#![deny(rust_2018_idioms)]
#![warn(missing_debug_implementations)]

//! Bounded SQL query equivalence checking.
//!
//! A [`VerificationResult::True`] result covers only databases containing at
//! most the configured number of rows in each base table. Results are compared
//! as bags unless ordering or slicing requires list comparison. A
//! [`VerificationResult::False`] result includes a concrete counterexample and
//! proves that the queries are not equivalent.

mod concrete;
mod counterexample;
mod ir;
mod metrics;
mod normalize;
mod outcome;
mod query;
mod schema;
mod symbolic;
mod verifier;

pub use counterexample::{
    Counterexample, CounterexampleTable, DateValue, ExactNumeric, QueryResult, Row,
    ScalarParseError, TimeValue, Value,
};
pub use metrics::{VerificationCounters, VerificationPhaseTimings, VerificationReport};
pub use outcome::{UnsupportedKind, UnsupportedReason, VerificationResult};
pub use schema::{
    Column, ColumnRef, ConstraintComparison, ConstraintOperand, ConstraintPredicate, DataType,
    IntegrityConstraint, Schema, Table,
};
pub use verifier::{
    BoundSearchOrder, BoundVerification, CoercionPolicy, GroupingPolicy, OrderingPolicy,
    PreparedVerifier, Verifier, VerifyOptions,
};

/// Checks two queries for bounded equivalence with [`VerifyOptions::default`].
#[must_use]
pub fn verify(schema: &Schema, left_sql: &str, right_sql: &str) -> VerificationResult {
    Verifier::default().verify(schema, left_sql, right_sql)
}
