fn not_equal(x: Field, y: Field) -> bool {
    x != y
}

global hello: str<15> = "hello-local-dep";
global hello_local_dep: str<15> = "hello-local-dep";

#[test]
fn test_not_equal() {
    assert(not_equal(1, 2));

    // Uncomment to make test fail
    // assert(not_equal(1, 1));
}
