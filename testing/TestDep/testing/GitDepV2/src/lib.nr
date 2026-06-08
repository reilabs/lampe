fn not_equal(x: Field, y: Field) -> bool {
    x != y
}

#[allow(dead_code)]
global hello: str<16> = "hello-git-dep-v2";
#[allow(dead_code)]
global hello_git_dep_v2: str<16> = "hello-git-dep-v2";

#[test]
fn test_not_equal() {
    assert(not_equal(1, 2));

    // Uncomment to make test fail
    // assert(not_equal(1, 1));
}
