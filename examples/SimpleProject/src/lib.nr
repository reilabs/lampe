fn return_one() -> Field {
    1
}

#[test]
fn test_equal_one() {
    assert(1 == return_one());
}
