use std::fmt;
use std::num::ParseIntError;
use std::str::FromStr;

use crate::schema::DataType;

/// An exact rational value used for SQL `NUMERIC` columns and expressions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExactNumeric {
    numerator: i64,
    denominator: i64,
}

impl ExactNumeric {
    /// Constructs a normalized rational number.
    pub fn new(numerator: i64, denominator: i64) -> Result<Self, ScalarParseError> {
        if denominator == 0 {
            return Err(ScalarParseError::new(
                "a numeric denominator cannot be zero",
            ));
        }
        let mut numerator = i128::from(numerator);
        let mut denominator = i128::from(denominator);
        if denominator < 0 {
            numerator = -numerator;
            denominator = -denominator;
        }
        let divisor = gcd(numerator.unsigned_abs(), denominator.unsigned_abs()) as i128;
        let numerator = i64::try_from(numerator / divisor)
            .map_err(|_| ScalarParseError::new("numeric numerator is outside i64"))?;
        let denominator = i64::try_from(denominator / divisor)
            .map_err(|_| ScalarParseError::new("numeric denominator is outside i64"))?;
        Ok(Self {
            numerator,
            denominator,
        })
    }

    #[must_use]
    pub const fn from_integer(value: i64) -> Self {
        Self {
            numerator: value,
            denominator: 1,
        }
    }

    #[must_use]
    pub const fn numerator(self) -> i64 {
        self.numerator
    }

    #[must_use]
    pub const fn denominator(self) -> i64 {
        self.denominator
    }
}

impl FromStr for ExactNumeric {
    type Err = ScalarParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.trim();
        if value.is_empty() {
            return Err(ScalarParseError::new("numeric literal cannot be empty"));
        }
        let (negative, unsigned) = match value.as_bytes()[0] {
            b'-' => (true, &value[1..]),
            b'+' => (false, &value[1..]),
            _ => (false, value),
        };
        let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
        if whole.is_empty() && fraction.is_empty() {
            return Err(ScalarParseError::new("numeric literal has no digits"));
        }
        if !whole
            .bytes()
            .chain(fraction.bytes())
            .all(|byte| byte.is_ascii_digit())
        {
            return Err(ScalarParseError::new(format!(
                "`{value}` is not an exact decimal literal"
            )));
        }
        let scale = u32::try_from(fraction.len())
            .map_err(|_| ScalarParseError::new("numeric scale is too large"))?;
        let denominator = 10_i128
            .checked_pow(scale)
            .ok_or_else(|| ScalarParseError::new("numeric scale is outside i64"))?;
        let digits = format!("{whole}{fraction}");
        let mut numerator = digits.parse::<i128>().map_err(|_| {
            ScalarParseError::new(format!("numeric literal `{value}` is outside i64"))
        })?;
        if negative {
            numerator = -numerator;
        }
        Self::new(
            i64::try_from(numerator)
                .map_err(|_| ScalarParseError::new("numeric numerator is outside i64"))?,
            i64::try_from(denominator)
                .map_err(|_| ScalarParseError::new("numeric denominator is outside i64"))?,
        )
    }
}

impl fmt::Display for ExactNumeric {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == 1 {
            write!(formatter, "{}", self.numerator)
        } else {
            write!(formatter, "{}/{}", self.numerator, self.denominator)
        }
    }
}

/// A Gregorian calendar date represented as days since 1970-01-01.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DateValue {
    days_since_epoch: i32,
}

impl DateValue {
    #[must_use]
    pub const fn from_days_since_epoch(days: i32) -> Self {
        Self {
            days_since_epoch: days,
        }
    }

    #[must_use]
    pub const fn days_since_epoch(self) -> i32 {
        self.days_since_epoch
    }

    /// Returns the proleptic-Gregorian `(year, month, day)` components.
    #[must_use]
    pub fn components(self) -> (i64, i64, i64) {
        civil_from_days(i64::from(self.days_since_epoch))
    }
}

impl FromStr for DateValue {
    type Err = ScalarParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let mut parts = value.split('-');
        let year = parse_date_part(parts.next(), "year")?;
        let month = parse_date_part(parts.next(), "month")?;
        let day = parse_date_part(parts.next(), "day")?;
        if parts.next().is_some() {
            return Err(ScalarParseError::new(format!(
                "`{value}` is not an ISO date"
            )));
        }
        if !(1..=12).contains(&month) {
            return Err(ScalarParseError::new("date month is outside 1..=12"));
        }
        let max_day = days_in_month(year, month);
        if day < 1 || day > max_day {
            return Err(ScalarParseError::new(format!(
                "date day is outside 1..={max_day}"
            )));
        }
        let days = days_from_civil(year, month, day);
        Ok(Self::from_days_since_epoch(i32::try_from(days).map_err(
            |_| ScalarParseError::new("date is outside the supported range"),
        )?))
    }
}

impl fmt::Display for DateValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (year, month, day) = civil_from_days(i64::from(self.days_since_epoch));
        write!(formatter, "{year:04}-{month:02}-{day:02}")
    }
}

/// A SQL time-of-day represented as nanoseconds after midnight.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TimeValue {
    nanoseconds_since_midnight: i64,
}

impl TimeValue {
    pub const NANOS_PER_DAY: i64 = 86_400_000_000_000;

    pub fn from_nanoseconds_since_midnight(value: i64) -> Result<Self, ScalarParseError> {
        if !(0..Self::NANOS_PER_DAY).contains(&value) {
            return Err(ScalarParseError::new(
                "time is outside a single 24-hour day",
            ));
        }
        Ok(Self {
            nanoseconds_since_midnight: value,
        })
    }

    #[must_use]
    pub const fn nanoseconds_since_midnight(self) -> i64 {
        self.nanoseconds_since_midnight
    }
}

impl FromStr for TimeValue {
    type Err = ScalarParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let (clock, fractional) = value.split_once('.').unwrap_or((value, ""));
        let mut parts = clock.split(':');
        let hour = parse_time_part(parts.next(), "hour")?;
        let minute = parse_time_part(parts.next(), "minute")?;
        let second = parse_time_part(parts.next(), "second")?;
        if parts.next().is_some() || hour > 23 || minute > 59 || second > 59 {
            return Err(ScalarParseError::new(format!(
                "`{value}` is not a valid SQL time"
            )));
        }
        if fractional.len() > 9 || !fractional.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(ScalarParseError::new(
                "time fractional seconds must contain at most nine digits",
            ));
        }
        let fraction = if fractional.is_empty() {
            0
        } else {
            fractional
                .parse::<i64>()
                .map_err(|_| ScalarParseError::new("time fractional seconds are outside i64"))?
                * 10_i64.pow(9 - u32::try_from(fractional.len()).unwrap_or(9))
        };
        let seconds = i64::from(hour * 3_600 + minute * 60 + second);
        Self::from_nanoseconds_since_midnight(seconds * 1_000_000_000 + fraction)
    }
}

impl fmt::Display for TimeValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let total_seconds = self.nanoseconds_since_midnight / 1_000_000_000;
        let nanos = self.nanoseconds_since_midnight % 1_000_000_000;
        let hour = total_seconds / 3_600;
        let minute = total_seconds % 3_600 / 60;
        let second = total_seconds % 60;
        if nanos == 0 {
            write!(formatter, "{hour:02}:{minute:02}:{second:02}")
        } else {
            let fraction = format!("{nanos:09}");
            write!(
                formatter,
                "{hour:02}:{minute:02}:{second:02}.{}",
                fraction.trim_end_matches('0')
            )
        }
    }
}

/// A concrete SQL value in a counterexample.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Value {
    Integer(i64),
    Boolean(bool),
    Text(String),
    Enum(String),
    Date(DateValue),
    Time(TimeValue),
    Numeric(ExactNumeric),
    Null,
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(value) => write!(formatter, "{value}"),
            Self::Boolean(value) => write!(formatter, "{value}"),
            Self::Text(value) | Self::Enum(value) => write!(formatter, "'{value}'"),
            Self::Date(value) => write!(formatter, "DATE '{value}'"),
            Self::Time(value) => write!(formatter, "TIME '{value}'"),
            Self::Numeric(value) => write!(formatter, "{value}"),
            Self::Null => formatter.write_str("NULL"),
        }
    }
}

/// An ordered tuple of concrete values. Query result collections treat rows as a bag.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Row {
    pub values: Vec<Value>,
}

impl Row {
    #[must_use]
    pub fn new<I>(values: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            values: values.into_iter().collect(),
        }
    }
}

/// One base table from a counterexample database.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CounterexampleTable {
    pub name: String,
    pub columns: Vec<String>,
    pub rows: Vec<Row>,
}

/// The rows and typed columns produced by one query.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryResult {
    pub columns: Vec<String>,
    pub column_types: Vec<DataType>,
    pub rows: Vec<Row>,
}

/// A witness database for non-equivalence, together with both differing outputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Counterexample {
    pub tables: Vec<CounterexampleTable>,
    pub left_result: QueryResult,
    pub right_result: QueryResult,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScalarParseError {
    message: String,
}

impl ScalarParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for ScalarParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for ScalarParseError {}

fn gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left.max(1)
}

fn parse_date_part(value: Option<&str>, kind: &str) -> Result<i64, ScalarParseError> {
    parse_part(value, kind)
}

fn parse_time_part(value: Option<&str>, kind: &str) -> Result<u32, ScalarParseError> {
    parse_part(value, kind)
}

fn parse_part<T>(value: Option<&str>, kind: &str) -> Result<T, ScalarParseError>
where
    T: FromStr<Err = ParseIntError>,
{
    value
        .ok_or_else(|| ScalarParseError::new(format!("time/date is missing its {kind}")))?
        .parse()
        .map_err(|_| ScalarParseError::new(format!("invalid time/date {kind}")))
}

fn days_in_month(year: i64, month: i64) -> i64 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) => 29,
        2 => 28,
        _ => 0,
    }
}

fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let adjusted_year = year - i64::from(month <= 2);
    let era = adjusted_year.div_euclid(400);
    let year_of_era = adjusted_year - era * 400;
    let adjusted_month = month + if month > 2 { -3 } else { 9 };
    let day_of_year = (153 * adjusted_month + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

fn civil_from_days(days_since_epoch: i64) -> (i64, i64, i64) {
    let days = days_since_epoch + 719_468;
    let era = days.div_euclid(146_097);
    let day_of_era = days - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let mut year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_prime = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_prime + 2) / 5 + 1;
    let month = month_prime + if month_prime < 10 { 3 } else { -9 };
    year += i64::from(month <= 2);
    (year, month, day)
}
