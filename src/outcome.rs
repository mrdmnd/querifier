use std::fmt;

use crate::counterexample::Counterexample;

/// Broad reason that a verification attempt could not produce a proof or witness.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UnsupportedKind {
    InvalidSchema,
    ParseError,
    UnsupportedSql,
    NameResolution,
    TypeError,
    ComplexityLimit,
    Solver,
    Internal,
}

impl UnsupportedKind {
    /// Stable machine-readable category used by coverage and telemetry.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::InvalidSchema => "invalid_schema",
            Self::ParseError => "parse_error",
            Self::UnsupportedSql => "unsupported_sql",
            Self::NameResolution => "name_resolution",
            Self::TypeError => "type_error",
            Self::ComplexityLimit => "complexity_limit",
            Self::Solver => "solver",
            Self::Internal => "internal",
        }
    }

    /// Whether retrying with a larger resource budget can plausibly change the outcome.
    #[must_use]
    pub const fn is_resource_limit(self) -> bool {
        matches!(self, Self::ComplexityLimit | Self::Solver)
    }
}

/// Structured context for an [`VerificationResult::Unsupported`] result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnsupportedReason {
    pub kind: UnsupportedKind,
    pub message: String,
}

impl UnsupportedReason {
    #[must_use]
    pub fn new(kind: UnsupportedKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    #[must_use]
    pub const fn code(&self) -> &'static str {
        self.kind.code()
    }
}

impl fmt::Display for UnsupportedReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for UnsupportedReason {}

/// The three possible outcomes of bounded verification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VerificationResult {
    /// No counterexample exists within the configured per-table row bound.
    True { bound: usize },
    /// The queries differ on the included concrete database.
    False { counterexample: Counterexample },
    /// The input or solver fell outside the implementation's supported boundary.
    Unsupported { reason: UnsupportedReason },
}

impl VerificationResult {
    #[must_use]
    pub const fn is_true(&self) -> bool {
        matches!(self, Self::True { .. })
    }

    #[must_use]
    pub const fn is_false(&self) -> bool {
        matches!(self, Self::False { .. })
    }

    #[must_use]
    pub const fn is_unsupported(&self) -> bool {
        matches!(self, Self::Unsupported { .. })
    }
}

impl fmt::Display for VerificationResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::True { .. } => formatter.write_str("true"),
            Self::False { .. } => formatter.write_str("false"),
            Self::Unsupported { .. } => formatter.write_str("unsupported"),
        }
    }
}

impl From<UnsupportedReason> for VerificationResult {
    fn from(reason: UnsupportedReason) -> Self {
        Self::Unsupported { reason }
    }
}
