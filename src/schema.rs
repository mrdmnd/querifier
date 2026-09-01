use std::collections::HashSet;

use crate::counterexample::Value;
use crate::outcome::{UnsupportedKind, UnsupportedReason};

/// Scalar types supported by the bounded verifier.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DataType {
    Integer,
    Boolean,
    Text,
    Enum,
    Date,
    Time,
    Numeric,
}

/// A column in a base table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Column {
    pub name: String,
    pub data_type: DataType,
    pub nullable: bool,
    /// Legal values for an enum column. Empty for all non-enum columns.
    pub enum_values: Vec<String>,
}

impl Column {
    #[must_use]
    pub fn new(name: impl Into<String>, data_type: DataType, nullable: bool) -> Self {
        Self {
            name: name.into(),
            data_type,
            nullable,
            enum_values: Vec::new(),
        }
    }

    #[must_use]
    pub fn nullable(name: impl Into<String>, data_type: DataType) -> Self {
        Self::new(name, data_type, true)
    }

    #[must_use]
    pub fn not_null(name: impl Into<String>, data_type: DataType) -> Self {
        Self::new(name, data_type, false)
    }

    #[must_use]
    pub fn enumeration<I, S>(name: impl Into<String>, values: I, nullable: bool) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            name: name.into(),
            data_type: DataType::Enum,
            nullable,
            enum_values: values.into_iter().map(Into::into).collect(),
        }
    }
}

/// A base table and its local primary-key declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Table {
    pub name: String,
    pub columns: Vec<Column>,
    pub primary_key: Option<Vec<String>>,
}

impl Table {
    #[must_use]
    pub fn new<I>(name: impl Into<String>, columns: I) -> Self
    where
        I: IntoIterator<Item = Column>,
    {
        Self {
            name: name.into(),
            columns: columns.into_iter().collect(),
            primary_key: None,
        }
    }

    #[must_use]
    pub fn with_primary_key<I, S>(mut self, columns: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.primary_key = Some(columns.into_iter().map(Into::into).collect());
        self
    }
}

/// A fully qualified base-table column used by integrity constraints.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ColumnRef {
    pub table: String,
    pub column: String,
}

impl ColumnRef {
    #[must_use]
    pub fn new(table: impl Into<String>, column: impl Into<String>) -> Self {
        Self {
            table: table.into(),
            column: column.into(),
        }
    }
}

/// An operand in a schema check predicate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConstraintOperand {
    Column(ColumnRef),
    Literal(Value),
}

impl ConstraintOperand {
    #[must_use]
    pub fn column(table: impl Into<String>, column: impl Into<String>) -> Self {
        Self::Column(ColumnRef::new(table, column))
    }

    #[must_use]
    pub const fn literal(value: Value) -> Self {
        Self::Literal(value)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ConstraintComparison {
    Equal,
    NotEqual,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
}

/// A typed row predicate imposed on every live row combination it references.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConstraintPredicate {
    Compare {
        op: ConstraintComparison,
        left: ConstraintOperand,
        right: ConstraintOperand,
    },
    Between {
        value: ConstraintOperand,
        lower: ConstraintOperand,
        upper: ConstraintOperand,
    },
    In {
        value: ConstraintOperand,
        choices: Vec<ConstraintOperand>,
    },
    Implies {
        premise: Box<ConstraintPredicate>,
        conclusion: Box<ConstraintPredicate>,
    },
}

/// An integrity constraint over one or more base tables.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IntegrityConstraint {
    PrimaryKey {
        columns: Vec<ColumnRef>,
    },
    Unique {
        columns: Vec<ColumnRef>,
    },
    ForeignKey {
        columns: Vec<ColumnRef>,
        referenced_columns: Vec<ColumnRef>,
    },
    Check {
        predicate: ConstraintPredicate,
    },
    /// Adjacent live row slots contain increasing non-NULL integers; gaps are allowed.
    AutoIncrement {
        column: ColumnRef,
    },
    /// Adjacent live row slots contain non-NULL consecutive integer values.
    Consecutive {
        column: ColumnRef,
    },
}

/// A collection of base tables visible to both queries.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Schema {
    pub tables: Vec<Table>,
    pub constraints: Vec<IntegrityConstraint>,
}

impl Schema {
    #[must_use]
    pub fn new<I>(tables: I) -> Self
    where
        I: IntoIterator<Item = Table>,
    {
        Self {
            tables: tables.into_iter().collect(),
            constraints: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_constraint(mut self, constraint: IntegrityConstraint) -> Self {
        self.constraints.push(constraint);
        self
    }

    pub fn push_constraint(&mut self, constraint: IntegrityConstraint) {
        self.constraints.push(constraint);
    }

    pub(crate) fn validate(&self) -> Result<(), UnsupportedReason> {
        if self.tables.is_empty() {
            return Err(invalid_schema("the schema must contain at least one table"));
        }

        let mut table_names = HashSet::new();
        for table in &self.tables {
            validate_name(&table.name, "table")?;
            if !table_names.insert(canonical_name(&table.name)) {
                return Err(invalid_schema(format!(
                    "duplicate table name `{}`",
                    table.name
                )));
            }
            if table.columns.is_empty() {
                return Err(invalid_schema(format!(
                    "table `{}` must contain at least one column",
                    table.name
                )));
            }

            let mut column_names = HashSet::new();
            for column in &table.columns {
                validate_name(&column.name, "column")?;
                if !column_names.insert(canonical_name(&column.name)) {
                    return Err(invalid_schema(format!(
                        "duplicate column name `{}.{}`",
                        table.name, column.name
                    )));
                }
                validate_enum_domain(table, column)?;
            }
            if let Some(primary_key) = &table.primary_key {
                validate_local_key(table, primary_key, &column_names)?;
            }
        }
        for constraint in &self.constraints {
            self.validate_constraint(constraint)?;
        }
        Ok(())
    }

    pub(crate) fn table_index(&self, name: &str) -> Option<usize> {
        let name = canonical_name(name);
        self.tables
            .iter()
            .position(|table| canonical_name(&table.name) == name)
    }

    pub(crate) fn resolve_column(
        &self,
        reference: &ColumnRef,
    ) -> Result<(usize, usize, &Column), UnsupportedReason> {
        let table_index = self.table_index(&reference.table).ok_or_else(|| {
            invalid_schema(format!(
                "constraint references unknown table `{}`",
                reference.table
            ))
        })?;
        let table = &self.tables[table_index];
        let column_name = canonical_name(&reference.column);
        let column_index = table
            .columns
            .iter()
            .position(|column| canonical_name(&column.name) == column_name)
            .ok_or_else(|| {
                invalid_schema(format!(
                    "constraint references unknown column `{}.{}`",
                    reference.table, reference.column
                ))
            })?;
        Ok((table_index, column_index, &table.columns[column_index]))
    }

    fn validate_constraint(
        &self,
        constraint: &IntegrityConstraint,
    ) -> Result<(), UnsupportedReason> {
        match constraint {
            IntegrityConstraint::PrimaryKey { columns }
            | IntegrityConstraint::Unique { columns } => self.validate_qualified_key(columns),
            IntegrityConstraint::ForeignKey {
                columns,
                referenced_columns,
            } => {
                if columns.is_empty() || columns.len() != referenced_columns.len() {
                    return Err(invalid_schema(
                        "foreign keys must have matching non-empty column lists",
                    ));
                }
                require_one_table(columns, "foreign key")?;
                require_one_table(referenced_columns, "referenced key")?;
                for (column, referenced) in columns.iter().zip(referenced_columns) {
                    let (_, _, column) = self.resolve_column(column)?;
                    let (_, _, referenced) = self.resolve_column(referenced)?;
                    if column.data_type != referenced.data_type {
                        return Err(invalid_schema(
                            "foreign-key and referenced columns must have matching types",
                        ));
                    }
                }
                Ok(())
            }
            IntegrityConstraint::Check { predicate } => {
                self.validate_predicate(predicate).map(|_| ())
            }
            IntegrityConstraint::AutoIncrement { column }
            | IntegrityConstraint::Consecutive { column } => {
                let (_, _, column) = self.resolve_column(column)?;
                if column.data_type != DataType::Integer {
                    return Err(invalid_schema(
                        "auto-increment and consecutive constraints require integer columns",
                    ));
                }
                Ok(())
            }
        }
    }

    fn validate_qualified_key(&self, columns: &[ColumnRef]) -> Result<(), UnsupportedReason> {
        if columns.is_empty() {
            return Err(invalid_schema("key constraints cannot be empty"));
        }
        require_one_table(columns, "key")?;
        let mut names = HashSet::new();
        for reference in columns {
            self.resolve_column(reference)?;
            if !names.insert(canonical_name(&reference.column)) {
                return Err(invalid_schema(format!(
                    "key repeats column `{}.{}`",
                    reference.table, reference.column
                )));
            }
        }
        Ok(())
    }

    fn validate_predicate(
        &self,
        predicate: &ConstraintPredicate,
    ) -> Result<Option<DataType>, UnsupportedReason> {
        match predicate {
            ConstraintPredicate::Compare { op, left, right } => {
                let data_type = self.common_operand_type([left, right])?;
                if data_type == Some(DataType::Boolean)
                    && !matches!(
                        op,
                        ConstraintComparison::Equal | ConstraintComparison::NotEqual
                    )
                {
                    return Err(invalid_schema(
                        "boolean check operands only support equality",
                    ));
                }
                Ok(Some(DataType::Boolean))
            }
            ConstraintPredicate::Between {
                value,
                lower,
                upper,
            } => {
                let data_type = self.common_operand_type([value, lower, upper])?;
                if data_type == Some(DataType::Boolean) {
                    return Err(invalid_schema("BETWEEN cannot order boolean operands"));
                }
                Ok(Some(DataType::Boolean))
            }
            ConstraintPredicate::In { value, choices } => {
                if choices.is_empty() {
                    return Err(invalid_schema("IN constraints need at least one choice"));
                }
                self.common_operand_type(std::iter::once(value).chain(choices))?;
                Ok(Some(DataType::Boolean))
            }
            ConstraintPredicate::Implies {
                premise,
                conclusion,
            } => {
                self.validate_predicate(premise)?;
                self.validate_predicate(conclusion)?;
                Ok(Some(DataType::Boolean))
            }
        }
    }

    fn common_operand_type<'a>(
        &self,
        operands: impl IntoIterator<Item = &'a ConstraintOperand>,
    ) -> Result<Option<DataType>, UnsupportedReason> {
        let mut result = None;
        for operand in operands {
            let current = self.operand_type(operand)?;
            if let Some(current) = current {
                if result.is_some_and(|existing| existing != current) {
                    return Err(invalid_schema(
                        "constraint operands must have matching scalar types",
                    ));
                }
                result = Some(current);
            }
        }
        if result.is_none() {
            return Err(invalid_schema(
                "a constraint cannot contain only untyped NULL operands",
            ));
        }
        Ok(result)
    }

    fn operand_type(
        &self,
        operand: &ConstraintOperand,
    ) -> Result<Option<DataType>, UnsupportedReason> {
        Ok(match operand {
            ConstraintOperand::Column(reference) => {
                Some(self.resolve_column(reference)?.2.data_type)
            }
            ConstraintOperand::Literal(value) => value_data_type(value),
        })
    }
}

impl From<Vec<Table>> for Schema {
    fn from(tables: Vec<Table>) -> Self {
        Self::new(tables)
    }
}

pub(crate) fn canonical_name(name: &str) -> String {
    name.to_ascii_lowercase()
}

pub(crate) fn value_data_type(value: &Value) -> Option<DataType> {
    match value {
        Value::Integer(_) => Some(DataType::Integer),
        Value::Boolean(_) => Some(DataType::Boolean),
        Value::Text(_) => Some(DataType::Text),
        Value::Enum(_) => Some(DataType::Enum),
        Value::Date(_) => Some(DataType::Date),
        Value::Time(_) => Some(DataType::Time),
        Value::Numeric(_) => Some(DataType::Numeric),
        Value::Null => None,
    }
}

fn validate_enum_domain(table: &Table, column: &Column) -> Result<(), UnsupportedReason> {
    if column.data_type != DataType::Enum {
        if !column.enum_values.is_empty() {
            return Err(invalid_schema(format!(
                "non-enum column `{}.{}` has enum values",
                table.name, column.name
            )));
        }
        return Ok(());
    }
    if column.enum_values.is_empty() {
        return Err(invalid_schema(format!(
            "enum column `{}.{}` needs at least one value",
            table.name, column.name
        )));
    }
    let mut values = HashSet::new();
    for value in &column.enum_values {
        if value.is_empty() || !values.insert(value) {
            return Err(invalid_schema(format!(
                "enum column `{}.{}` has an empty or duplicate value",
                table.name, column.name
            )));
        }
    }
    Ok(())
}

fn validate_local_key(
    table: &Table,
    primary_key: &[String],
    column_names: &HashSet<String>,
) -> Result<(), UnsupportedReason> {
    if primary_key.is_empty() {
        return Err(invalid_schema(format!(
            "table `{}` has an empty primary key",
            table.name
        )));
    }
    let mut key_columns = HashSet::new();
    for key in primary_key {
        validate_name(key, "primary-key column")?;
        let canonical = canonical_name(key);
        if !key_columns.insert(canonical.clone()) {
            return Err(invalid_schema(format!(
                "primary key for `{}` repeats column `{key}`",
                table.name
            )));
        }
        if !column_names.contains(&canonical) {
            return Err(invalid_schema(format!(
                "primary key for `{}` references unknown column `{key}`",
                table.name
            )));
        }
    }
    Ok(())
}

fn require_one_table(columns: &[ColumnRef], kind: &str) -> Result<(), UnsupportedReason> {
    let Some(first) = columns.first() else {
        return Err(invalid_schema(format!("{kind} cannot be empty")));
    };
    let table = canonical_name(&first.table);
    if columns
        .iter()
        .any(|column| canonical_name(&column.table) != table)
    {
        return Err(invalid_schema(format!(
            "{kind} columns must belong to one table"
        )));
    }
    Ok(())
}

fn validate_name(name: &str, kind: &str) -> Result<(), UnsupportedReason> {
    if name.trim().is_empty() {
        return Err(invalid_schema(format!("{kind} names cannot be empty")));
    }
    Ok(())
}

fn invalid_schema(message: impl Into<String>) -> UnsupportedReason {
    UnsupportedReason::new(UnsupportedKind::InvalidSchema, message)
}
