pub struct Point {
    pub x: Field,
    pub y: Field,
}

fn not_equal(x: Field, y: Field) -> bool {
    x != y
}

#[allow(dead_code)]
global hello: str<15> = "hello-local-dep";
#[allow(dead_code)]
global hello_local_dep: str<15> = "hello-local-dep";

#[test]
fn test_not_equal() {
    assert(not_equal(1, 2));

    // Uncomment to make test fail
    // assert(not_equal(1, 1));
}
