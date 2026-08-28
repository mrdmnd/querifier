use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use indexmap::IndexMap;
use querifier::{
    Column, ColumnRef, ConstraintComparison, ConstraintOperand, ConstraintPredicate, DataType,
    DateValue, ExactNumeric, IntegrityConstraint, Schema, Table, TimeValue, Value,
};
use serde::Deserialize;
use serde_json::Value as JsonValue;

pub const EXPECTED_RECORDS: usize = 23_994;
pub const EXPECTED_GROUPS: usize = 56;

pub type CorpusSchema = IndexMap<String, IndexMap<String, String>>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorpusRecord {
    pub file: String,
    pub index: usize,
    pub schema: CorpusSchema,
    pub constraints: Vec<ConstraintExpr>,
    pub pair: [String; 2],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConstraintExpr {
    Primary(Vec<ConstraintTerm>),
    Foreign(ConstraintTerm, ConstraintTerm),
    Compare {
        op: ComparisonOp,
        left: ConstraintTerm,
        right: ConstraintTerm,
    },
    Between {
        value: ConstraintTerm,
        lower: ConstraintTerm,
        upper: ConstraintTerm,
    },
    In {
        value: ConstraintTerm,
        choices: Vec<ConstraintTerm>,
    },
    Implies(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Increment(ConstraintTerm),
    Consecutive(ConstraintTerm),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ComparisonOp {
    Equal,
    NotEqual,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConstraintTerm {
    Column(String),
    Integer(i64),
    Literal(String),
    Date(String),
}

#[derive(Debug)]
pub struct CorpusLoadError {
    line: Option<usize>,
    message: String,
}

impl CorpusLoadError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            line: None,
            message: message.into(),
        }
    }

    fn at_line(line: usize, message: impl Into<String>) -> Self {
        Self {
            line: Some(line),
            message: message.into(),
        }
    }
}

impl fmt::Display for CorpusLoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.line {
            Some(line) => write!(formatter, "corpus line {line}: {}", self.message),
            None => formatter.write_str(&self.message),
        }
    }
}

impl std::error::Error for CorpusLoadError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorpusAdaptError {
    pub message: String,
}

impl fmt::Display for CorpusAdaptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for CorpusAdaptError {}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawCorpusRecord {
    file: String,
    index: usize,
    schema: CorpusSchema,
    constraint: Option<Vec<JsonValue>>,
    pair: [String; 2],
}

pub fn corpus_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("data")
        .join("verieql")
        .join("leetcode.jsonlines")
}

pub fn load_corpus() -> Result<Vec<CorpusRecord>, CorpusLoadError> {
    load_corpus_from(&corpus_path())
}

pub fn load_corpus_from(path: &Path) -> Result<Vec<CorpusRecord>, CorpusLoadError> {
    let file = File::open(path).map_err(|error| {
        CorpusLoadError::new(format!("cannot open {}: {error}", path.display()))
    })?;
    let reader = BufReader::new(file);
    let mut records = Vec::with_capacity(EXPECTED_RECORDS);
    for (offset, line) in reader.lines().enumerate() {
        let line_number = offset + 1;
        let line = line.map_err(|error| {
            CorpusLoadError::at_line(line_number, format!("cannot read JSON: {error}"))
        })?;
        if line.is_empty() {
            return Err(CorpusLoadError::at_line(
                line_number,
                "blank records are not allowed",
            ));
        }
        let raw: RawCorpusRecord = serde_json::from_str(&line).map_err(|error| {
            CorpusLoadError::at_line(line_number, format!("invalid record: {error}"))
        })?;
        records.push(
            convert_record(raw)
                .map_err(|error| CorpusLoadError::at_line(line_number, error.message))?,
        );
    }
    Ok(records)
}

pub fn validate_corpus(records: &[CorpusRecord]) -> Result<(), CorpusLoadError> {
    if records.len() != EXPECTED_RECORDS {
        return Err(CorpusLoadError::new(format!(
            "expected {EXPECTED_RECORDS} records, found {}",
            records.len()
        )));
    }

    let mut groups: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    let mut keys = HashSet::with_capacity(records.len());
    let mut pairs = HashSet::with_capacity(records.len());
    for record in records {
        if record.schema.is_empty() {
            return Err(CorpusLoadError::new(format!(
                "{}:{} has an empty schema",
                record.file, record.index
            )));
        }
        if record.pair.iter().any(|query| query.trim().is_empty()) {
            return Err(CorpusLoadError::new(format!(
                "{}:{} has an empty query",
                record.file, record.index
            )));
        }
        if !keys.insert((record.file.as_str(), record.index)) {
            return Err(CorpusLoadError::new(format!(
                "duplicate record key {}:{}",
                record.file, record.index
            )));
        }
        if !pairs.insert((record.pair[0].as_str(), record.pair[1].as_str())) {
            return Err(CorpusLoadError::new(format!(
                "duplicate query pair at {}:{}",
                record.file, record.index
            )));
        }
        groups
            .entry(record.file.as_str())
            .or_default()
            .push(record.index);
    }
    if groups.len() != EXPECTED_GROUPS {
        return Err(CorpusLoadError::new(format!(
            "expected {EXPECTED_GROUPS} problem groups, found {}",
            groups.len()
        )));
    }
    for (file, indices) in &mut groups {
        indices.sort_unstable();
        for (expected, actual) in indices.iter().copied().enumerate() {
            if actual != expected {
                return Err(CorpusLoadError::new(format!(
                    "{file} has non-contiguous index {actual}; expected {expected}"
                )));
            }
        }
    }

    Ok(())
}

pub fn adapt_schema(record: &CorpusRecord) -> Result<Schema, CorpusAdaptError> {
    let tables = record
        .schema
        .iter()
        .map(|(table_name, columns)| {
            let columns = columns
                .iter()
                .map(|(column_name, data_type)| adapt_column(column_name, data_type))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Table::new(table_name, columns))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut schema = Schema::new(tables);
    for constraint in &record.constraints {
        schema.push_constraint(adapt_constraint(record, constraint)?);
    }
    Ok(schema)
}

fn convert_record(raw: RawCorpusRecord) -> Result<CorpusRecord, CorpusLoadError> {
    let constraints = raw
        .constraint
        .unwrap_or_default()
        .into_iter()
        .map(parse_constraint)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CorpusRecord {
        file: raw.file,
        index: raw.index,
        schema: raw.schema,
        constraints,
        pair: raw.pair,
    })
}

fn parse_constraint(value: JsonValue) -> Result<ConstraintExpr, CorpusLoadError> {
    let JsonValue::Object(object) = value else {
        return Err(CorpusLoadError::new(
            "constraint expressions must be objects",
        ));
    };
    if object.len() != 1 {
        return Err(CorpusLoadError::new(
            "constraint objects must contain exactly one operator",
        ));
    }
    let (operator, arguments) = object
        .into_iter()
        .next()
        .ok_or_else(|| CorpusLoadError::new("empty constraint object"))?;
    match operator.as_str() {
        "primary" => Ok(ConstraintExpr::Primary(parse_term_list(arguments)?)),
        "foreign" => {
            let [left, right] = parse_fixed_terms::<2>(arguments)?;
            Ok(ConstraintExpr::Foreign(left, right))
        }
        "eq" => parse_comparison(ComparisonOp::Equal, arguments),
        "neq" => parse_comparison(ComparisonOp::NotEqual, arguments),
        "lt" => parse_comparison(ComparisonOp::Less, arguments),
        "lte" => parse_comparison(ComparisonOp::LessOrEqual, arguments),
        "gt" => parse_comparison(ComparisonOp::Greater, arguments),
        "gte" => parse_comparison(ComparisonOp::GreaterOrEqual, arguments),
        "between" => {
            let [value, lower, upper] = parse_fixed_terms::<3>(arguments)?;
            Ok(ConstraintExpr::Between {
                value,
                lower,
                upper,
            })
        }
        "in" => {
            let JsonValue::Array(mut arguments) = arguments else {
                return Err(CorpusLoadError::new("in expects an argument array"));
            };
            if arguments.len() != 2 {
                return Err(CorpusLoadError::new("in expects two arguments"));
            }
            let choices = parse_term_list(
                arguments
                    .pop()
                    .ok_or_else(|| CorpusLoadError::new("in is missing choices"))?,
            )?;
            let value = parse_term(
                arguments
                    .pop()
                    .ok_or_else(|| CorpusLoadError::new("in is missing a value"))?,
            )?;
            Ok(ConstraintExpr::In { value, choices })
        }
        "imply" => {
            let JsonValue::Array(mut arguments) = arguments else {
                return Err(CorpusLoadError::new("imply expects an argument array"));
            };
            if arguments.len() != 2 {
                return Err(CorpusLoadError::new("imply expects two predicates"));
            }
            let right = parse_constraint(
                arguments
                    .pop()
                    .ok_or_else(|| CorpusLoadError::new("imply is missing its conclusion"))?,
            )?;
            let left = parse_constraint(
                arguments
                    .pop()
                    .ok_or_else(|| CorpusLoadError::new("imply is missing its premise"))?,
            )?;
            Ok(ConstraintExpr::Implies(Box::new(left), Box::new(right)))
        }
        "inc" => Ok(ConstraintExpr::Increment(parse_term(arguments)?)),
        "consec" => Ok(ConstraintExpr::Consecutive(parse_term(arguments)?)),
        _ => Err(CorpusLoadError::new(format!(
            "unknown constraint operator `{operator}`"
        ))),
    }
}

fn parse_comparison(
    op: ComparisonOp,
    arguments: JsonValue,
) -> Result<ConstraintExpr, CorpusLoadError> {
    let [left, right] = parse_fixed_terms::<2>(arguments)?;
    Ok(ConstraintExpr::Compare { op, left, right })
}

fn parse_fixed_terms<const N: usize>(
    arguments: JsonValue,
) -> Result<[ConstraintTerm; N], CorpusLoadError> {
    let terms = parse_term_list(arguments)?;
    terms.try_into().map_err(|terms: Vec<_>| {
        CorpusLoadError::new(format!("expected {N} arguments, found {}", terms.len()))
    })
}

fn parse_term_list(value: JsonValue) -> Result<Vec<ConstraintTerm>, CorpusLoadError> {
    let JsonValue::Array(values) = value else {
        return Err(CorpusLoadError::new("expected an argument array"));
    };
    values.into_iter().map(parse_term).collect()
}

fn parse_term(value: JsonValue) -> Result<ConstraintTerm, CorpusLoadError> {
    match value {
        JsonValue::Number(number) => number
            .as_i64()
            .map(ConstraintTerm::Integer)
            .ok_or_else(|| CorpusLoadError::new("constraint integer is outside i64")),
        JsonValue::String(value) => {
            if value.contains("__") {
                Ok(ConstraintTerm::Column(value))
            } else {
                Ok(ConstraintTerm::Literal(value))
            }
        }
        JsonValue::Object(object) if object.len() == 1 => {
            let (kind, value) = object
                .into_iter()
                .next()
                .ok_or_else(|| CorpusLoadError::new("empty constraint term"))?;
            let JsonValue::String(value) = value else {
                return Err(CorpusLoadError::new(format!(
                    "{kind} constraint terms must contain strings"
                )));
            };
            match kind.as_str() {
                "value" => Ok(ConstraintTerm::Column(value)),
                "literal" => Ok(ConstraintTerm::Literal(value)),
                "date" => Ok(ConstraintTerm::Date(value)),
                _ => Err(CorpusLoadError::new(format!(
                    "unknown constraint term `{kind}`"
                ))),
            }
        }
        _ => Err(CorpusLoadError::new("unsupported constraint term")),
    }
}

fn split_column_reference(reference: &str) -> Result<(&str, &str), CorpusAdaptError> {
    reference
        .split_once("__")
        .ok_or_else(|| adapt_error(format!("invalid corpus column reference `{reference}`")))
}

fn adapt_error(message: impl Into<String>) -> CorpusAdaptError {
    CorpusAdaptError {
        message: message.into(),
    }
}

fn adapt_column(name: &str, declaration: &str) -> Result<Column, CorpusAdaptError> {
    let declaration = declaration.to_ascii_uppercase();
    Ok(match declaration.as_str() {
        "INT" => Column::nullable(name, DataType::Integer),
        "BOOL" => Column::nullable(name, DataType::Boolean),
        "VARCHAR" => Column::nullable(name, DataType::Text),
        "DATE" => Column::nullable(name, DataType::Date),
        "TIME" => Column::nullable(name, DataType::Time),
        "NUMERIC" => Column::nullable(name, DataType::Numeric),
        _ if declaration.starts_with("ENUM,") => {
            let variants = declaration
                .split(',')
                .skip(1)
                .filter(|variant| *variant != "NULL")
                .map(str::to_owned)
                .collect::<Vec<_>>();
            Column::enumeration(name, variants, true)
        }
        _ => {
            return Err(adapt_error(format!("unknown corpus type `{declaration}`")));
        }
    })
}

fn adapt_constraint(
    record: &CorpusRecord,
    constraint: &ConstraintExpr,
) -> Result<IntegrityConstraint, CorpusAdaptError> {
    match constraint {
        ConstraintExpr::Primary(columns) => Ok(IntegrityConstraint::PrimaryKey {
            columns: columns
                .iter()
                .map(term_as_column)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ConstraintExpr::Foreign(column, referenced) => Ok(IntegrityConstraint::ForeignKey {
            columns: vec![term_as_column(column)?],
            referenced_columns: vec![term_as_column(referenced)?],
        }),
        ConstraintExpr::Compare { .. }
        | ConstraintExpr::Between { .. }
        | ConstraintExpr::In { .. }
        | ConstraintExpr::Implies(_, _) => Ok(IntegrityConstraint::Check {
            predicate: adapt_predicate(record, constraint)?,
        }),
        ConstraintExpr::Increment(column) => Ok(IntegrityConstraint::AutoIncrement {
            column: term_as_column(column)?,
        }),
        ConstraintExpr::Consecutive(column) => Ok(IntegrityConstraint::Consecutive {
            column: term_as_column(column)?,
        }),
    }
}

fn adapt_predicate(
    record: &CorpusRecord,
    expression: &ConstraintExpr,
) -> Result<ConstraintPredicate, CorpusAdaptError> {
    match expression {
        ConstraintExpr::Compare { op, left, right } => {
            let data_type = common_term_type(record, [left, right])?;
            Ok(ConstraintPredicate::Compare {
                op: match op {
                    ComparisonOp::Equal => ConstraintComparison::Equal,
                    ComparisonOp::NotEqual => ConstraintComparison::NotEqual,
                    ComparisonOp::Less => ConstraintComparison::Less,
                    ComparisonOp::LessOrEqual => ConstraintComparison::LessOrEqual,
                    ComparisonOp::Greater => ConstraintComparison::Greater,
                    ComparisonOp::GreaterOrEqual => ConstraintComparison::GreaterOrEqual,
                },
                left: adapt_operand(left, data_type)?,
                right: adapt_operand(right, data_type)?,
            })
        }
        ConstraintExpr::Between {
            value,
            lower,
            upper,
        } => {
            let data_type = common_term_type(record, [value, lower, upper])?;
            Ok(ConstraintPredicate::Between {
                value: adapt_operand(value, data_type)?,
                lower: adapt_operand(lower, data_type)?,
                upper: adapt_operand(upper, data_type)?,
            })
        }
        ConstraintExpr::In { value, choices } => {
            let data_type = common_term_type(record, std::iter::once(value).chain(choices.iter()))?;
            Ok(ConstraintPredicate::In {
                value: adapt_operand(value, data_type)?,
                choices: choices
                    .iter()
                    .map(|choice| adapt_operand(choice, data_type))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        ConstraintExpr::Implies(premise, conclusion) => Ok(ConstraintPredicate::Implies {
            premise: Box::new(adapt_predicate(record, premise)?),
            conclusion: Box::new(adapt_predicate(record, conclusion)?),
        }),
        ConstraintExpr::Primary(_)
        | ConstraintExpr::Foreign(_, _)
        | ConstraintExpr::Increment(_)
        | ConstraintExpr::Consecutive(_) => Err(adapt_error(
            "non-predicate constraint nested inside a predicate",
        )),
    }
}

fn common_term_type<'a>(
    record: &CorpusRecord,
    terms: impl IntoIterator<Item = &'a ConstraintTerm>,
) -> Result<DataType, CorpusAdaptError> {
    let mut data_type = None;
    for term in terms {
        let current = match term {
            ConstraintTerm::Column(column) => Some(column_data_type(record, column)?),
            ConstraintTerm::Integer(_) => Some(DataType::Integer),
            ConstraintTerm::Date(_) => Some(DataType::Date),
            ConstraintTerm::Literal(value) if value.eq_ignore_ascii_case("NULL") => None,
            ConstraintTerm::Literal(_) => None,
        };
        if let Some(current) = current {
            if data_type.is_some_and(|existing| existing != current)
                && !matches!(
                    (data_type, current),
                    (Some(DataType::Boolean), DataType::Integer)
                        | (Some(DataType::Numeric), DataType::Integer)
                        | (
                            Some(DataType::Integer),
                            DataType::Boolean | DataType::Numeric
                        )
                )
            {
                return Err(adapt_error("constraint terms have incompatible types"));
            }
            if data_type.is_none() || current != DataType::Integer {
                data_type = Some(current);
            }
        }
    }
    data_type.ok_or_else(|| adapt_error("cannot infer the constraint operand type"))
}

fn adapt_operand(
    term: &ConstraintTerm,
    expected: DataType,
) -> Result<ConstraintOperand, CorpusAdaptError> {
    Ok(match term {
        ConstraintTerm::Column(column) => ConstraintOperand::Column(column_ref(column)?),
        ConstraintTerm::Integer(value) => ConstraintOperand::Literal(match expected {
            DataType::Boolean if *value == 0 || *value == 1 => Value::Boolean(*value == 1),
            DataType::Numeric => Value::Numeric(ExactNumeric::from_integer(*value)),
            _ => Value::Integer(*value),
        }),
        ConstraintTerm::Literal(value) if value.eq_ignore_ascii_case("NULL") => {
            ConstraintOperand::Literal(Value::Null)
        }
        ConstraintTerm::Literal(value) => {
            ConstraintOperand::Literal(match expected {
                DataType::Text => Value::Text(value.clone()),
                DataType::Enum => Value::Enum(value.clone()),
                DataType::Date => Value::Date(DateValue::from_str(value).map_err(|error| {
                    adapt_error(format!("invalid corpus date `{value}`: {error}"))
                })?),
                DataType::Time => Value::Time(TimeValue::from_str(value).map_err(|error| {
                    adapt_error(format!("invalid corpus time `{value}`: {error}"))
                })?),
                DataType::Numeric => {
                    Value::Numeric(ExactNumeric::from_str(value).map_err(|error| {
                        adapt_error(format!("invalid corpus numeric `{value}`: {error}"))
                    })?)
                }
                _ => {
                    return Err(adapt_error(format!(
                        "string literal `{value}` cannot be used as {expected:?}"
                    )));
                }
            })
        }
        ConstraintTerm::Date(value) => ConstraintOperand::Literal(Value::Date(
            DateValue::from_str(value)
                .map_err(|error| adapt_error(format!("invalid corpus date `{value}`: {error}")))?,
        )),
    })
}

fn term_as_column(term: &ConstraintTerm) -> Result<ColumnRef, CorpusAdaptError> {
    let ConstraintTerm::Column(column) = term else {
        return Err(adapt_error("constraint requires a column reference"));
    };
    column_ref(column)
}

fn column_ref(reference: &str) -> Result<ColumnRef, CorpusAdaptError> {
    let (table, column) = split_column_reference(reference)?;
    Ok(ColumnRef::new(table, column))
}

fn column_data_type(record: &CorpusRecord, reference: &str) -> Result<DataType, CorpusAdaptError> {
    let (table_name, column_name) = split_column_reference(reference)?;
    let (_, columns) = record
        .schema
        .iter()
        .find(|(table, _)| table.eq_ignore_ascii_case(table_name))
        .ok_or_else(|| adapt_error(format!("unknown corpus table `{table_name}`")))?;
    let (_, declaration) = columns
        .iter()
        .find(|(column, _)| column.eq_ignore_ascii_case(column_name))
        .ok_or_else(|| {
            adapt_error(format!(
                "unknown corpus column `{table_name}.{column_name}`"
            ))
        })?;
    Ok(adapt_column(column_name, declaration)?.data_type)
}
