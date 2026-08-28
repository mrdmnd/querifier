use crate::counterexample::Value;
use crate::schema::DataType;

#[derive(Clone, Debug)]
pub(crate) struct TypedQuery {
    pub root: Relation,
    pub semantics: QuerySemantics,
}

impl TypedQuery {
    pub fn output_types(&self) -> impl Iterator<Item = DataType> + '_ {
        self.root.columns.iter().map(|column| column.data_type)
    }

    pub fn output_names(&self) -> Vec<String> {
        self.root
            .columns
            .iter()
            .map(|column| column.name.clone())
            .collect()
    }

    pub const fn requires_list_comparison(&self) -> bool {
        self.semantics.ordered || self.semantics.sliced
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct QuerySemantics {
    pub ordered: bool,
    pub sliced: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Relation {
    pub node: RelationNode,
    pub columns: Vec<ColumnMeta>,
    pub max_rows: usize,
    /// Sound functional dependencies over output column indexes.
    pub functional_dependencies: Vec<FunctionalDependency>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FunctionalDependency {
    pub determinants: Vec<usize>,
    pub dependents: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum RelationNode {
    Unit,
    Scan {
        table_index: usize,
    },
    Product {
        left: Box<Relation>,
        right: Box<Relation>,
    },
    Join {
        kind: JoinKind,
        left: Box<Relation>,
        right: Box<Relation>,
        on: TypedExpr,
    },
    Filter {
        input: Box<Relation>,
        predicate: TypedExpr,
    },
    Project {
        input: Box<Relation>,
        expressions: Vec<TypedExpr>,
    },
    Distinct {
        input: Box<Relation>,
    },
    SetOperation {
        op: SetOp,
        all: bool,
        left: Box<Relation>,
        right: Box<Relation>,
    },
    Aggregate {
        input: Box<Relation>,
        group_by: Vec<TypedExpr>,
        expressions: Vec<TypedExpr>,
        having: Option<TypedExpr>,
    },
    Sort {
        input: Box<Relation>,
        keys: Vec<SortKey>,
    },
    Slice {
        input: Box<Relation>,
        offset: usize,
        limit: Option<usize>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum JoinKind {
    Inner,
    Left,
    Right,
    Full,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SetOp {
    Union,
    Intersect,
    Except,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ColumnMeta {
    pub qualifier: Option<String>,
    pub name: String,
    pub canonical_name: String,
    /// Qualified source name retained for clause resolution after projection.
    pub source_qualifier: Option<String>,
    pub source_name: Option<String>,
    pub data_type: DataType,
    pub nullable: bool,
    pub unqualified_visible: bool,
    pub wildcard_visible: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct SortKey {
    pub expression: TypedExpr,
    pub ascending: bool,
    pub nulls_first: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct TypedExpr {
    pub data_type: DataType,
    pub nullable: bool,
    pub kind: ExprKind,
}

impl TypedExpr {
    pub fn column(index: usize, column: &ColumnMeta) -> Self {
        Self {
            data_type: column.data_type,
            nullable: column.nullable,
            kind: ExprKind::Column(index),
        }
    }

    pub fn literal(value: Value, data_type: DataType, nullable: bool) -> Self {
        Self {
            data_type,
            nullable,
            kind: ExprKind::Literal(value),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ExprKind {
    Column(usize),
    OuterColumn {
        depth: usize,
        index: usize,
    },
    Literal(Value),
    Compare {
        op: CompareOp,
        left: Box<TypedExpr>,
        right: Box<TypedExpr>,
    },
    And(Box<TypedExpr>, Box<TypedExpr>),
    Or(Box<TypedExpr>, Box<TypedExpr>),
    Not(Box<TypedExpr>),
    IsNull(Box<TypedExpr>),
    IsNotNull(Box<TypedExpr>),
    Coalesce(Vec<TypedExpr>),
    Arithmetic {
        op: ArithmeticOp,
        left: Box<TypedExpr>,
        right: Box<TypedExpr>,
    },
    Negate(Box<TypedExpr>),
    Case {
        branches: Vec<(TypedExpr, TypedExpr)>,
        else_result: Box<TypedExpr>,
    },
    Cast {
        expression: Box<TypedExpr>,
        to: DataType,
    },
    ScalarFunction {
        function: ScalarFunction,
        arguments: Vec<TypedExpr>,
    },
    Aggregate {
        function: AggregateFunction,
        expression: Option<Box<TypedExpr>>,
        distinct: bool,
    },
    CountDistinctRow {
        expressions: Vec<TypedExpr>,
    },
    Exists {
        query: Box<Relation>,
        negated: bool,
    },
    InSubquery {
        expressions: Vec<TypedExpr>,
        query: Box<Relation>,
        negated: bool,
    },
    ScalarSubquery {
        query: Box<Relation>,
    },
    WindowRank {
        function: WindowRankFunction,
        partition_by: Vec<TypedExpr>,
        order_by: Vec<SortKey>,
    },
    WindowAggregate {
        function: AggregateFunction,
        expression: Option<Box<TypedExpr>>,
        distinct: bool,
        partition_by: Vec<TypedExpr>,
        order_by: Vec<SortKey>,
    },
    FirstValue {
        expression: Box<TypedExpr>,
        partition_by: Vec<TypedExpr>,
        order_by: Vec<SortKey>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum WindowRankFunction {
    RowNumber,
    Rank,
    DenseRank,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum CompareOp {
    Equal,
    NotEqual,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ArithmeticOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ScalarFunction {
    Abs,
    Round,
    Truncate,
    Concat,
    Length,
    DateDiff,
    Year,
    Month,
    Day,
    ToDays,
    LastDay,
    Weekday,
    DayOfWeek,
    Quarter,
    Sign,
    Power(u32),
    Floor,
    Ceil,
    StartsWith,
    EndsWith,
    Contains,
    Substring { start: usize, length: Option<usize> },
    Left(usize),
    Right(usize),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum AggregateFunction {
    Count,
    Sum,
    Min,
    Max,
    Avg,
}
