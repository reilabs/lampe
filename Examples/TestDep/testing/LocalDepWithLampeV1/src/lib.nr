fn not_equal(x: Field, y: Field) -> bool {
    x != y
}

global hello: str<29> = "hello-local-dep-with-lampe-v1";
global hello_local_dep_with_lampe_v1: str<29> = "hello-local-dep-with-lampe-v1";

#[test]
fn test_not_equal() {
    assert(not_equal(1, 2));

    // Uncomment to make test fail
    // assert(not_equal(1, 1));
}
