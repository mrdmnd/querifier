use std::time::Duration;

use querifier::{
    CoercionPolicy, Column, ColumnRef, ConstraintComparison, ConstraintOperand,
    ConstraintPredicate, Counterexample, DataType, GroupingPolicy, IntegrityConstraint,
    OrderingPolicy, Schema, Table, UnsupportedKind, VerificationResult, Verifier, VerifyOptions,
};

fn basic_schema(nullable_value: bool) -> Schema {
    Schema::new([Table::new(
        "items",
        [
            Column::not_null("id", DataType::Integer),
            Column::new("value", DataType::Integer, nullable_value),
            Column::nullable("flag", DataType::Boolean),
        ],
    )])
}

fn primary_key_schema() -> Schema {
    Schema::new([Table::new(
        "items",
        [
            Column::nullable("id", DataType::Integer),
            Column::nullable("value", DataType::Integer),
        ],
    )
    .with_primary_key(["id"])])
}

fn assert_true(result: VerificationResult, expected_bound: usize) {
    assert_eq!(
        result,
        VerificationResult::True {
            bound: expected_bound
        }
    );
}

fn expect_false(result: VerificationResult) -> Counterexample {
    match result {
        VerificationResult::False { counterexample } => counterexample,
        other => panic!("expected false, got {other:?}"),
    }
}

fn expect_unsupported(result: VerificationResult, expected_kind: UnsupportedKind) {
    match result {
        VerificationResult::Unsupported { reason } => {
            assert_eq!(reason.kind, expected_kind, "{}", reason.message);
        }
        other => panic!("expected unsupported, got {other:?}"),
    }
}

#[test]
fn proves_simple_predicate_rewrite_with_nulls() {
    let result = Verifier::default().verify(
        &basic_schema(true),
        "SELECT id FROM items WHERE NOT (value > 25)",
        "SELECT id FROM items WHERE value <= 25",
    );

    assert_true(result, 2);
}

#[test]
fn returns_reproducible_threshold_counterexample() {
    let counterexample = expect_false(Verifier::default().verify(
        &basic_schema(true),
        "SELECT id FROM items WHERE value > 1",
        "SELECT id FROM items WHERE value > 2",
    ));

    assert_ne!(
        counterexample.left_result.rows,
        counterexample.right_result.rows
    );
    assert!(!counterexample.tables[0].rows.is_empty());
}

#[test]
fn models_three_valued_boolean_logic() {
    let counterexample = expect_false(Verifier::default().verify(
        &basic_schema(true),
        "SELECT id FROM items WHERE flag OR NOT flag",
        "SELECT id FROM items",
    ));

    assert!(
        counterexample.tables[0]
            .rows
            .iter()
            .any(|row| row.values[2] == querifier::Value::Null)
    );
}

#[test]
fn treats_outputs_as_bags_not_sets() {
    let schema = Schema::new([Table::new(
        "items",
        [Column::not_null("id", DataType::Integer)],
    )]);
    let counterexample = expect_false(Verifier::default().verify(
        &schema,
        "SELECT a.id FROM items a JOIN items b ON a.id = b.id",
        "SELECT id FROM items",
    ));

    assert_eq!(counterexample.tables[0].rows.len(), 2);
    assert_eq!(counterexample.left_result.rows.len(), 4);
    assert_eq!(counterexample.right_result.rows.len(), 2);
}

#[test]
fn inner_join_matches_cross_product_filter() {
    let schema = Schema::new([
        Table::new(
            "employees",
            [
                Column::not_null("id", DataType::Integer),
                Column::nullable("department_id", DataType::Integer),
                Column::nullable("active", DataType::Boolean),
            ],
        ),
        Table::new("departments", [Column::not_null("id", DataType::Integer)]),
    ]);
    let result = Verifier::default().verify(
        &schema,
        "SELECT e.id FROM employees e INNER JOIN departments d ON e.department_id = d.id WHERE e.active",
        "SELECT e.id FROM employees e, departments d WHERE e.department_id = d.id AND e.active",
    );

    assert_true(result, 2);
}

#[test]
fn verifies_complex_three_table_agent_queries() {
    let schema = Schema::new([
        Table::new(
            "customers",
            [
                Column::nullable("id", DataType::Integer),
                Column::nullable("active", DataType::Boolean),
            ],
        )
        .with_primary_key(["id"]),
        Table::new(
            "orders",
            [
                Column::nullable("id", DataType::Integer),
                Column::nullable("customer_id", DataType::Integer),
                Column::nullable("total", DataType::Integer),
            ],
        )
        .with_primary_key(["id"]),
        Table::new(
            "payments",
            [
                Column::nullable("order_id", DataType::Integer),
                Column::nullable("sequence", DataType::Integer),
                Column::nullable("amount", DataType::Integer),
                Column::nullable("settled", DataType::Boolean),
            ],
        )
        .with_primary_key(["order_id", "sequence"]),
    ]);
    let reference = "
        SELECT c.id, o.id, p.amount
        FROM customers c
        INNER JOIN orders o ON c.id = o.customer_id
        INNER JOIN payments p ON o.id = p.order_id
        WHERE c.active
          AND o.total >= 100
          AND p.settled
          AND p.amount IS NOT NULL
    ";
    let equivalent_rewrite = "
        SELECT c.id, o.id, p.amount
        FROM payments p, orders o, customers c
        WHERE p.order_id = o.id
          AND o.customer_id = c.id
          AND NOT (c.active = FALSE)
          AND NOT (o.total < 100)
          AND NOT (p.settled = FALSE)
          AND NOT (p.amount IS NULL)
    ";

    assert_true(
        Verifier::default().verify(&schema, reference, equivalent_rewrite),
        2,
    );

    // This plausible agent output accidentally omits the settled-payment filter.
    let buggy_candidate = "
        SELECT c.id, o.id, p.amount
        FROM customers c
        JOIN orders o ON c.id = o.customer_id
        JOIN payments p ON o.id = p.order_id
        WHERE c.active
          AND o.total >= 100
          AND p.amount IS NOT NULL
    ";
    let counterexample =
        expect_false(Verifier::default().verify(&schema, reference, buggy_candidate));

    assert_eq!(counterexample.tables.len(), 3);
    assert!(
        counterexample
            .tables
            .iter()
            .all(|table| !table.rows.is_empty())
    );
    assert_ne!(
        counterexample.left_result.rows,
        counterexample.right_result.rows
    );
}

#[test]
fn supports_text_enum_date_time_and_exact_numeric_domains() {
    let verifier = Verifier::default();
    let cases = [
        (Column::nullable("value", DataType::Text), "value = 'ALPHA'"),
        (
            Column::nullable("value", DataType::Date),
            "value > DATE '2020-01-01'",
        ),
        (
            Column::nullable("value", DataType::Time),
            "value >= TIME '08:30:00'",
        ),
        (Column::nullable("value", DataType::Numeric), "value < 1.50"),
    ];
    for (column, predicate) in cases {
        let schema = Schema::new([Table::new(
            "domain_values",
            [Column::not_null("id", DataType::Integer), column],
        )]);
        assert_true(
            verifier.verify(
                &schema,
                &format!("SELECT id FROM domain_values WHERE {predicate}"),
                &format!("SELECT id FROM domain_values WHERE NOT NOT ({predicate})"),
            ),
            2,
        );
    }

    let enum_schema = Schema::new([Table::new(
        "states",
        [
            Column::not_null("id", DataType::Integer),
            Column::enumeration("state", ["OPEN", "CLOSED"], true),
        ],
    )]);
    assert_true(
        verifier.verify(
            &enum_schema,
            "SELECT id FROM states WHERE state = 'OPEN' OR state = 'CLOSED'",
            "SELECT id FROM states WHERE state IS NOT NULL",
        ),
        2,
    );
}

#[test]
fn enforces_generic_checks_and_foreign_keys() {
    let ranged = Schema::new([Table::new(
        "items",
        [
            Column::not_null("id", DataType::Integer),
            Column::nullable("value", DataType::Integer),
        ],
    )])
    .with_constraint(IntegrityConstraint::Check {
        predicate: ConstraintPredicate::Between {
            value: ConstraintOperand::column("items", "value"),
            lower: ConstraintOperand::literal(querifier::Value::Integer(1)),
            upper: ConstraintOperand::literal(querifier::Value::Integer(3)),
        },
    });
    assert_true(
        Verifier::default().verify(
            &ranged,
            "SELECT id FROM items WHERE value IS NULL OR (value >= 1 AND value <= 3)",
            "SELECT id FROM items",
        ),
        2,
    );

    let relational = Schema::new([
        Table::new("parents", [Column::nullable("id", DataType::Integer)]),
        Table::new(
            "children",
            [Column::nullable("parent_id", DataType::Integer)],
        ),
    ])
    .with_constraint(IntegrityConstraint::PrimaryKey {
        columns: vec![ColumnRef::new("parents", "id")],
    })
    .with_constraint(IntegrityConstraint::ForeignKey {
        columns: vec![ColumnRef::new("children", "parent_id")],
        referenced_columns: vec![ColumnRef::new("parents", "id")],
    });
    assert_true(
        Verifier::default().verify(
            &relational,
            "SELECT parent_id FROM children WHERE parent_id IS NOT NULL",
            "SELECT c.parent_id FROM children c INNER JOIN parents p ON c.parent_id = p.id",
        ),
        2,
    );
}

#[test]
fn rejects_inconsistent_generic_constraints() {
    let schema = Schema::new([Table::new(
        "items",
        [Column::not_null("id", DataType::Integer)],
    )])
    .with_constraint(IntegrityConstraint::Check {
        predicate: ConstraintPredicate::Compare {
            op: ConstraintComparison::Greater,
            left: ConstraintOperand::literal(querifier::Value::Integer(1)),
            right: ConstraintOperand::literal(querifier::Value::Integer(2)),
        },
    });
    expect_unsupported(
        Verifier::default().verify(&schema, "SELECT id FROM items", "SELECT id FROM items"),
        UnsupportedKind::InvalidSchema,
    );
}

#[test]
fn replays_witnesses_under_consecutive_constraints() {
    let schema = Schema::new([Table::new(
        "sequence_values",
        [Column::nullable("id", DataType::Integer)],
    )])
    .with_constraint(IntegrityConstraint::Consecutive {
        column: ColumnRef::new("sequence_values", "id"),
    });
    let counterexample = expect_false(Verifier::default().verify(
        &schema,
        "SELECT a.id FROM sequence_values a, sequence_values b WHERE a.id < b.id",
        "SELECT b.id FROM sequence_values a, sequence_values b WHERE a.id < b.id",
    ));
    let rows = &counterexample.tables[0].rows;
    assert_eq!(rows.len(), 2);
    let [
        querifier::Value::Integer(left),
        querifier::Value::Integer(right),
    ] = [&rows[0].values[0], &rows[1].values[0]]
    else {
        panic!("expected integer sequence values");
    };
    assert_eq!(left.checked_add(1), Some(*right));
}

#[test]
fn models_distinct_and_set_multiplicities() {
    let schema = Schema::new([Table::new(
        "items",
        [Column::nullable("value", DataType::Integer)],
    )]);
    let verifier = Verifier::default();

    assert_true(
        verifier.verify(
            &schema,
            "SELECT value FROM items UNION SELECT value FROM items",
            "SELECT DISTINCT value FROM items",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT value FROM items INTERSECT ALL SELECT value FROM items",
            "SELECT value FROM items",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT value FROM items EXCEPT ALL SELECT value FROM items",
            "SELECT value FROM items WHERE FALSE",
        ),
        2,
    );
    expect_false(verifier.verify(
        &schema,
        "SELECT value FROM items UNION ALL SELECT value FROM items",
        "SELECT value FROM items UNION SELECT value FROM items",
    ));
}

#[test]
fn bag_comparison_can_use_the_smaller_relation_as_representatives() {
    let schema = Schema::new([Table::new(
        "items",
        [Column::nullable("value", DataType::Integer)],
    )]);
    let verifier = Verifier::default();
    let short = "SELECT value FROM items";
    let long_equivalent = "SELECT value FROM items UNION ALL SELECT value FROM items WHERE FALSE";
    let long_with_duplicates = "SELECT value FROM items UNION ALL SELECT value FROM items";

    assert_true(verifier.verify(&schema, short, long_equivalent), 2);
    assert_true(verifier.verify(&schema, long_equivalent, short), 2);
    expect_false(verifier.verify(&schema, short, long_with_duplicates));
    expect_false(verifier.verify(&schema, long_with_duplicates, short));
}

#[test]
fn supports_outer_join_symmetry_and_null_extension() {
    let schema = Schema::new([
        Table::new(
            "left_items",
            [
                Column::nullable("id", DataType::Integer),
                Column::nullable("left_value", DataType::Text),
            ],
        ),
        Table::new(
            "right_items",
            [
                Column::nullable("id", DataType::Integer),
                Column::nullable("right_value", DataType::Text),
            ],
        ),
    ]);
    let verifier = Verifier::default();

    assert_true(
        verifier.verify(
            &schema,
            "SELECT l.id, l.left_value, r.right_value FROM left_items l LEFT JOIN right_items r ON l.id = r.id",
            "SELECT l.id, l.left_value, r.right_value FROM right_items r RIGHT JOIN left_items l ON l.id = r.id",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT l.id, r.id, l.left_value, r.right_value FROM left_items l FULL JOIN right_items r ON l.id = r.id",
            "SELECT l.id, r.id, l.left_value, r.right_value FROM right_items r FULL JOIN left_items l ON l.id = r.id",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id AS id FROM left_items AS i ORDER BY i.id",
            "SELECT id FROM left_items ORDER BY id",
        ),
        2,
    );
}

#[test]
fn using_and_natural_joins_match_explicit_composite_conditions() {
    let schema = Schema::new([
        Table::new(
            "left_items",
            [
                Column::nullable("first_id", DataType::Integer),
                Column::nullable("second_id", DataType::Integer),
                Column::nullable("left_value", DataType::Text),
            ],
        ),
        Table::new(
            "right_items",
            [
                Column::nullable("first_id", DataType::Integer),
                Column::nullable("second_id", DataType::Integer),
                Column::nullable("right_value", DataType::Text),
            ],
        ),
    ]);
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(
            &schema,
            "SELECT first_id, left_value, right_value FROM left_items JOIN right_items USING (first_id, second_id)",
            "SELECT l.first_id, l.left_value, r.right_value FROM left_items l JOIN right_items r ON l.first_id = r.first_id AND l.second_id = r.second_id",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT first_id, second_id, left_value, right_value FROM left_items NATURAL LEFT JOIN right_items",
            "SELECT first_id, second_id, left_value, right_value FROM left_items LEFT JOIN right_items USING (first_id, second_id)",
        ),
        2,
    );
}

#[test]
fn supports_arithmetic_case_coalesce_and_membership_expressions() {
    let schema = basic_schema(true);
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id, value + 1, CASE WHEN flag THEN value ELSE 0 END, COALESCE(value, 7) FROM items WHERE value BETWEEN 1 AND 3",
            "SELECT id, 1 + value, IF(flag, value, 0), IFNULL(value, 7) FROM items WHERE value >= 1 AND value <= 3",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id FROM items WHERE value IN (1, 2, NULL)",
            "SELECT id FROM items WHERE value = 1 OR value = 2 OR value = NULL",
        ),
        2,
    );
}

#[test]
fn models_aggregate_empty_null_and_distinct_semantics() {
    let schema = basic_schema(true);
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(
            &schema,
            "SELECT COUNT(value) FROM items",
            "SELECT COALESCE(SUM(CASE WHEN value IS NULL THEN 0 ELSE 1 END), 0) FROM items",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT AVG(value) FROM items",
            "SELECT SUM(value) / COUNT(value) FROM items",
        ),
        2,
    );
    let witness = expect_false(verifier.verify(
        &schema,
        "SELECT COUNT(*) FROM items",
        "SELECT COUNT(value) FROM items",
    ));
    assert!(
        witness.tables[0]
            .rows
            .iter()
            .any(|row| row.values[1] == querifier::Value::Null)
    );
}

#[test]
fn groups_and_filters_with_having_under_bag_semantics() {
    let schema = basic_schema(true);
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT flag, COUNT(*) AS item_count FROM items GROUP BY flag HAVING item_count > 1",
            "SELECT flag, COUNT(*) AS item_count FROM items GROUP BY flag HAVING COUNT(*) > 1",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT flag, COUNT(*), SUM(value), MIN(value), MAX(value), AVG(value), COUNT(DISTINCT value) FROM items GROUP BY flag HAVING COUNT(*) > 1",
            "SELECT flag, COUNT(1), SUM(value), MIN(value), MAX(value), AVG(value), COUNT(DISTINCT value) FROM items GROUP BY 1 HAVING COUNT(1) >= 2",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &primary_key_schema(),
            "SELECT id, MIN(value) AS first_value FROM items GROUP BY id",
            "SELECT MIN(id) AS id, MIN(value) AS first_value FROM items GROUP BY id",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &primary_key_schema(),
            "SELECT id, value, COUNT(*) FROM items GROUP BY id",
            "SELECT id, value, COUNT(*) FROM items GROUP BY id, value",
        ),
        2,
    );
    expect_unsupported(
        Verifier::default().verify(
            &basic_schema(true),
            "SELECT id, value, COUNT(*) FROM items GROUP BY id",
            "SELECT id, value, COUNT(*) FROM items GROUP BY id, value",
        ),
        UnsupportedKind::TypeError,
    );
    assert_true(
        Verifier::new(VerifyOptions {
            grouping_policy: GroupingPolicy::PermissiveFirstRow,
            ..VerifyOptions::default()
        })
        .verify(
            &basic_schema(true),
            "SELECT id, value, COUNT(*) FROM items GROUP BY id",
            "SELECT id, value, COUNT(*) FROM items GROUP BY id",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &basic_schema(true),
            "WITH counts AS (SELECT flag, COUNT(*) AS n FROM items GROUP BY flag) SELECT items.flag, counts.n, COUNT(*) FROM items JOIN counts ON items.flag = counts.flag GROUP BY items.flag",
            "WITH counts AS (SELECT flag, COUNT(*) AS n FROM items GROUP BY flag) SELECT items.flag, counts.n, COUNT(*) FROM items JOIN counts ON items.flag = counts.flag GROUP BY items.flag, counts.n",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &primary_key_schema(),
            "SELECT id FROM items GROUP BY id HAVING MAX(value > 0) AND MAX(value > 1) = 0",
            "SELECT id FROM items WHERE value > 0 AND NOT (value > 1)",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT value FROM items GROUP BY value",
            "SELECT value FROM (SELECT value, DENSE_RANK() OVER (ORDER BY value) AS value_rank FROM items) ranked GROUP BY value_rank",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT COUNT(DISTINCT id, value) FROM items",
            "SELECT COUNT(*) FROM (SELECT DISTINCT id, value FROM items WHERE id IS NOT NULL AND value IS NOT NULL) AS distinct_pairs",
        ),
        2,
    );
}

#[test]
fn permissive_grouping_uses_the_first_live_symbolic_row() {
    let schema = Schema::new([
        Table::new(
            "users",
            [
                Column::nullable("account", DataType::Integer),
                Column::nullable("name", DataType::Text),
            ],
        )
        .with_primary_key(["account"]),
        Table::new(
            "transactions",
            [
                Column::nullable("trans_id", DataType::Integer),
                Column::nullable("account", DataType::Integer),
                Column::nullable("amount", DataType::Integer),
            ],
        )
        .with_primary_key(["trans_id"]),
    ])
    .with_constraint(IntegrityConstraint::ForeignKey {
        columns: vec![ColumnRef::new("transactions", "account")],
        referenced_columns: vec![ColumnRef::new("users", "account")],
    });
    let verifier = Verifier::new(VerifyOptions {
        max_rows_per_table: 1,
        grouping_policy: GroupingPolicy::PermissiveFirstRow,
        ..VerifyOptions::default()
    });
    assert_true(
        verifier.verify(
            &schema,
            "SELECT u.name, SUM(t.amount) AS balance FROM users u JOIN transactions t ON u.account = t.account GROUP BY t.account HAVING SUM(t.amount) > 10000",
            "WITH balances AS (SELECT account, SUM(amount) AS balance FROM transactions GROUP BY account) SELECT u.name, b.balance FROM users u JOIN balances b ON u.account = b.account HAVING b.balance > 10000",
        ),
        1,
    );
}

#[test]
fn supports_exact_scalar_functions_and_casts() {
    let schema = Schema::new([Table::new(
        "values_table",
        [
            Column::not_null("id", DataType::Integer),
            Column::nullable("name", DataType::Text),
            Column::nullable("amount", DataType::Numeric),
            Column::nullable("flag", DataType::Boolean),
        ],
    )]);
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT id, CONCAT(name, '!'), LENGTH(name), ROUND(amount), ABS(amount), CAST(flag AS INT), POWER(amount, 2), SIGN(amount), FLOOR(1.5), CEIL(-1.5), MOD(id, 2), SUBSTRING(name, 1, 2) FROM values_table",
            "SELECT id, name || '!', CHAR_LENGTH(name), ROUND(amount, 0), CASE WHEN amount < 0 THEN -amount ELSE amount END, CASE WHEN flag IS NULL THEN NULL WHEN flag THEN 1 ELSE 0 END, amount * amount, CASE WHEN amount IS NULL THEN NULL WHEN amount > 0 THEN 1 WHEN amount < 0 THEN -1 ELSE 0 END, 1, -1, id % 2, LEFT(name, 2) FROM values_table",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT id FROM values_table WHERE name LIKE 'A' OR name LIKE '%'",
            "SELECT id FROM values_table WHERE name = 'A' OR name IS NOT NULL",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT TRUNCATE(1.239, 2), TRUNCATE(-1.239, 2), TRUNCATE(123, -1)",
            "SELECT 1.23, -1.23, 120",
        ),
        2,
    );
    expect_false(Verifier::default().verify(
        &schema,
        "SELECT id FROM values_table WHERE name LIKE 'A%'",
        "SELECT id FROM values_table WHERE FALSE",
    ));
}

#[test]
fn supports_explicit_mysql_scalar_coercions() {
    let schema = basic_schema(true);
    let verifier = Verifier::new(VerifyOptions {
        coercion_policy: CoercionPolicy::MySqlCompatible,
        ..VerifyOptions::default()
    });
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id FROM items WHERE value",
            "SELECT id FROM items WHERE value <> 0",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT SUBSTRING('abc', '1', 2), ROUND(1.234, 2.0)",
            "SELECT 'ab', 1.23",
        ),
        2,
    );
}

#[test]
fn supports_day_date_arithmetic_and_truth_tests() {
    let schema = Schema::new([Table::new(
        "events",
        [
            Column::not_null("id", DataType::Integer),
            Column::nullable("event_date", DataType::Date),
            Column::nullable("flag", DataType::Boolean),
        ],
    )]);
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(
            &schema,
            "SELECT DATE_ADD(DATE '2020-02-28', INTERVAL '1' DAY), DATE_SUB(DATE '2020-03-01', INTERVAL 1 DAY), TIMESTAMPDIFF(DAY, DATE '2020-02-28', DATE '2020-03-01'), YEAR(DATE '2020-02-29'), MONTH(DATE '2020-02-29'), DAYOFMONTH(DATE '2020-02-29'), EXTRACT(YEAR FROM DATE '2020-02-29'), TO_DAYS(DATE '1970-01-01'), DATE_ADD(' 2020-02-28 ', INTERVAL 1 DAY), LAST_DAY(DATE '2020-02-10'), WEEKDAY(DATE '1970-01-01'), DAYOFWEEK(DATE '1970-01-01'), QUARTER(DATE '2020-05-01'), CAST('2020-02-29' AS DATE), STR_TO_DATE('2020-02-29', '%Y-%m-%d')",
            "SELECT DATE '2020-02-29', DATE '2020-02-29', 2, 2020, 2, 29, 2020, 719528, DATE '2020-02-29', DATE '2020-02-29', 3, 5, 2, DATE '2020-02-29', DATE '2020-02-29'",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id, NULLIF(flag, true), flag <=> true, flag IS DISTINCT FROM false FROM events WHERE flag IS NOT TRUE",
            "SELECT id, CASE WHEN flag = true THEN NULL ELSE flag END, flag IS TRUE, flag IS NOT FALSE FROM events WHERE flag = false OR flag IS NULL",
        ),
        2,
    );
}

#[test]
fn supports_from_first_queries_and_reports_width_mismatches() {
    let schema = basic_schema(true);
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(&schema, "FROM items", "SELECT id, value, flag FROM items"),
        2,
    );
    expect_false(verifier.verify(
        &schema,
        "FROM (SELECT id, value FROM items) AS projected",
        "SELECT id FROM items",
    ));
}

#[test]
fn compares_ordered_sliced_results_as_lists() {
    let schema = basic_schema(true);
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id, value FROM items ORDER BY value ASC NULLS FIRST, id LIMIT 1 OFFSET 1",
            "SELECT id, value FROM items ORDER BY 2, 1 LIMIT 1 OFFSET 1",
        ),
        2,
    );
    expect_false(verifier.verify(
        &schema,
        "SELECT id, value FROM items ORDER BY value ASC, id ASC",
        "SELECT id, value FROM items ORDER BY value DESC, id DESC",
    ));
    assert_true(
        verifier.verify(
            &schema,
            "SELECT flag, COUNT(*) AS count_items FROM items GROUP BY flag ORDER BY count_items, flag",
            "SELECT flag, COUNT(*) AS count_items FROM items GROUP BY flag ORDER BY 2, 1",
        ),
        2,
    );
}

#[test]
fn primary_key_changes_self_join_equivalence() {
    let result = Verifier::default().verify(
        &primary_key_schema(),
        "SELECT a.id FROM items a JOIN items b ON a.id = b.id",
        "SELECT id FROM items",
    );

    assert_true(result, 2);
}

#[test]
fn not_null_constraint_changes_filter_equivalence() {
    let not_null_schema = Schema::new([Table::new(
        "items",
        [
            Column::not_null("id", DataType::Integer),
            Column::not_null("value", DataType::Integer),
        ],
    )]);
    assert_true(
        Verifier::default().verify(
            &not_null_schema,
            "SELECT id FROM items WHERE value IS NOT NULL",
            "SELECT id FROM items",
        ),
        2,
    );

    let nullable_schema = Schema::new([Table::new(
        "items",
        [
            Column::not_null("id", DataType::Integer),
            Column::nullable("value", DataType::Integer),
        ],
    )]);
    expect_false(Verifier::default().verify(
        &nullable_schema,
        "SELECT id FROM items WHERE value IS NOT NULL",
        "SELECT id FROM items",
    ));
}

#[test]
fn result_can_depend_on_the_row_bound() {
    let schema = Schema::new([Table::new(
        "items",
        [Column::not_null("id", DataType::Integer)],
    )]);
    let options = |bound| VerifyOptions {
        max_rows_per_table: bound,
        timeout: Duration::from_secs(5),
        max_intermediate_rows: 100,
        ..VerifyOptions::default()
    };
    let left = "SELECT a.id FROM items a JOIN items b ON a.id <> b.id";
    let right = "SELECT id FROM items WHERE FALSE";

    assert_true(Verifier::new(options(1)).verify(&schema, left, right), 1);
    expect_false(Verifier::new(options(2)).verify(&schema, left, right));
}

#[test]
fn symbolic_tables_can_have_different_cardinalities() {
    let schema = Schema::new([
        Table::new("a", [Column::not_null("id", DataType::Integer)]),
        Table::new("b", [Column::not_null("id", DataType::Integer)]),
    ]);
    let counterexample = expect_false(
        Verifier::new(VerifyOptions {
            max_rows_per_table: 1,
            ..VerifyOptions::default()
        })
        .verify(
            &schema,
            "SELECT a.id FROM a CROSS JOIN b",
            "SELECT a.id FROM a",
        ),
    );

    assert_eq!(counterexample.tables[0].rows.len(), 1);
    assert!(counterexample.tables[1].rows.is_empty());
}

#[test]
fn wildcard_and_alias_projection_are_supported() {
    let result = Verifier::default().verify(
        &basic_schema(true),
        "SELECT i.* FROM items AS i",
        "SELECT id, value, flag FROM items",
    );

    assert_true(result, 2);
}

#[test]
fn supports_derived_tables_and_non_recursive_ctes() {
    let schema = basic_schema(true);
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT d.item_id FROM (SELECT id AS item_id, value FROM items) d WHERE d.value > 0",
            "SELECT id FROM items WHERE value > 0",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "WITH selected(item_id) AS (SELECT id FROM items WHERE value > 0) SELECT item_id FROM selected",
            "SELECT id FROM items WHERE value > 0",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT i.id FROM (items i INNER JOIN items j ON i.id = j.id)",
            "SELECT i.id FROM items i INNER JOIN items j ON i.id = j.id",
        ),
        2,
    );
}

#[test]
fn supports_correlated_exists_in_and_scalar_subqueries() {
    let schema = primary_key_schema();
    let verifier = Verifier::default();
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id FROM items i WHERE EXISTS (SELECT j.id FROM items j WHERE j.id = i.id AND j.value > 0)",
            "SELECT id FROM items WHERE value > 0",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id FROM items i WHERE i.id IN (SELECT j.id FROM items j WHERE j.value > 0)",
            "SELECT id FROM items WHERE value > 0",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id FROM items i WHERE i.value IN (SELECT j.value FROM items j)",
            "SELECT id FROM items WHERE value IS NOT NULL",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id FROM items i WHERE (i.id, i.value) IN (SELECT j.id, j.value FROM items j)",
            "SELECT id FROM items WHERE value IS NOT NULL",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id FROM items i WHERE (i.id, i.value) NOT IN (SELECT j.id, j.value FROM items j)",
            "SELECT id FROM items WHERE FALSE",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id FROM items WHERE (id, value) = (id, value)",
            "SELECT id FROM items WHERE value IS NOT NULL",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT id FROM items WHERE (id, value) IN ((id, value))",
            "SELECT id FROM items WHERE value IS NOT NULL",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id, (SELECT j.value FROM items j WHERE j.id = i.id LIMIT 1) FROM items i",
            "SELECT id, value FROM items",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id, (SELECT j.value FROM items j WHERE j.id = i.id AND j.value > 0 LIMIT 1) FROM items i",
            "SELECT id, CASE WHEN value > 0 THEN value ELSE NULL END FROM items",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id FROM items i WHERE EXISTS (SELECT j.id FROM items j WHERE EXISTS (SELECT k.id FROM items k WHERE k.id = i.id))",
            "SELECT id FROM items",
        ),
        2,
    );
    assert_true(
        verifier.verify(
            &schema,
            "SELECT i.id, (SELECT 1) FROM items i WHERE EXISTS (SELECT 1)",
            "SELECT id, CAST(true AS INT) FROM items",
        ),
        2,
    );
}

#[test]
fn supports_restricted_row_number_windows() {
    let schema = basic_schema(true);
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT value FROM items GROUP BY value HAVING COUNT(*) > 1",
            "SELECT DISTINCT value FROM (SELECT value, ROW_NUMBER() OVER (PARTITION BY value ORDER BY id) AS row_num FROM items) ranked WHERE row_num > 1",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT DISTINCT value FROM items",
            "SELECT value FROM (SELECT value, ROW_NUMBER() OVER (PARTITION BY value ORDER BY id DESC) AS row_num FROM items) ranked WHERE row_num = 1",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT value, COUNT(*) FROM items GROUP BY value",
            "SELECT value, item_count FROM (SELECT value, COUNT(*) OVER (PARTITION BY value) AS item_count, ROW_NUMBER() OVER (PARTITION BY value ORDER BY id) AS row_num FROM items) ranked WHERE row_num = 1",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT flag, MIN(id) FROM items GROUP BY flag",
            "SELECT DISTINCT flag, FIRST_VALUE(id) OVER (PARTITION BY flag ORDER BY id) FROM items",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT flag, MIN(id) FROM items GROUP BY flag",
            "SELECT DISTINCT flag, MIN(id) OVER (PARTITION BY flag ORDER BY id) FROM items",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT id, ROW_NUMBER() OVER (ORDER BY id) + 1 FROM items",
            "SELECT id, row_num + 1 FROM (SELECT id, ROW_NUMBER() OVER (ORDER BY id) AS row_num FROM items) AS ranked",
        ),
        2,
    );
    assert_true(
        Verifier::default().verify(
            &schema,
            "SELECT id, SUM(id) OVER () / COUNT(id) OVER () FROM items",
            "SELECT id, window_sum / window_count FROM (SELECT id, SUM(id) OVER () AS window_sum, COUNT(id) OVER () AS window_count FROM items) AS windowed",
        ),
        2,
    );
}

#[test]
fn rejects_pathologically_deep_nested_queries() {
    let schema = basic_schema(true);
    let mut predicate = "value > 0".to_owned();
    for depth in 0..9 {
        predicate = format!(
            "EXISTS (SELECT nested_{depth}.id FROM items nested_{depth} WHERE {predicate})"
        );
    }
    let query = format!("SELECT id FROM items WHERE {predicate}");
    expect_unsupported(
        Verifier::default().verify(&schema, &query, "SELECT id FROM items"),
        UnsupportedKind::ComplexityLimit,
    );
}

#[test]
fn rejects_features_outside_the_mvp() {
    let schema = basic_schema(true);
    expect_unsupported(
        Verifier::default().verify(
            &schema,
            "SELECT id FROM items WHERE 'abc' LIKE 'a_c'",
            "SELECT id FROM items",
        ),
        UnsupportedKind::UnsupportedSql,
    );
    assert_true(
        Verifier::new(VerifyOptions {
            ordering_policy: OrderingPolicy::IgnoreTopLevelOrder,
            ..VerifyOptions::default()
        })
        .verify(
            &schema,
            "SELECT id FROM items ORDER BY id",
            "SELECT id FROM items",
        ),
        2,
    );
    expect_unsupported(
        Verifier::default().verify(
            &schema,
            "SELECT id FROM items ORDER BY id",
            "SELECT id FROM items",
        ),
        UnsupportedKind::UnsupportedSql,
    );
    expect_unsupported(
        Verifier::default().verify(
            &schema,
            "SELECT id FROM items GROUP BY id ORDER BY COUNT(id)",
            "SELECT id FROM items GROUP BY id ORDER BY COUNT(id)",
        ),
        UnsupportedKind::UnsupportedSql,
    );
}

#[test]
fn reports_parse_name_type_and_schema_failures() {
    let schema = basic_schema(true);
    expect_unsupported(
        Verifier::default().verify(&schema, "not sql", "SELECT id FROM items"),
        UnsupportedKind::ParseError,
    );
    expect_unsupported(
        Verifier::default().verify(&schema, "SELECT missing FROM items", "SELECT id FROM items"),
        UnsupportedKind::NameResolution,
    );
    let type_witness = expect_false(Verifier::default().verify(
        &schema,
        "SELECT id FROM items",
        "SELECT flag FROM items",
    ));
    assert_ne!(
        type_witness.left_result.column_types,
        type_witness.right_result.column_types
    );

    let invalid_schema = Schema::new([
        Table::new("items", [Column::not_null("id", DataType::Integer)]),
        Table::new("ITEMS", [Column::not_null("id", DataType::Integer)]),
    ]);
    expect_unsupported(
        Verifier::default().verify(
            &invalid_schema,
            "SELECT id FROM items",
            "SELECT id FROM items",
        ),
        UnsupportedKind::InvalidSchema,
    );
}

#[test]
fn enforces_symbolic_complexity_limit() {
    let schema = Schema::new([Table::new(
        "items",
        [Column::not_null("id", DataType::Integer)],
    )]);
    let verifier = Verifier::new(VerifyOptions {
        max_rows_per_table: 3,
        timeout: Duration::from_secs(5),
        max_intermediate_rows: 10,
        ..VerifyOptions::default()
    });

    expect_unsupported(
        verifier.verify(
            &schema,
            "SELECT a.id FROM items a, items b, items c",
            "SELECT a.id FROM items a, items b, items c",
        ),
        UnsupportedKind::ComplexityLimit,
    );
}
