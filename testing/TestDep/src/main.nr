use local_dependency::Point;

fn make_point(x: Field, y: Field) -> Point {
    Point { x, y }
}

fn main(x: Field, y: pub Field) {
    assert(x != y);
}

#[test]
fn test_main() {
    main(1, 2);

    // Uncomment to make test fail
    // main(1, 1);
}
