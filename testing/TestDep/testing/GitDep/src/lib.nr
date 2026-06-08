fn not_equal(x: Field, y: Field) -> bool {
    x != y
}

#[allow(dead_code)]
global hello: str<13> = "hello-git-dep";
#[allow(dead_code)]
global hello_git_dep: str<13> = "hello-git-dep";

#[test]
fn test_not_equal() {
    assert(not_equal(1, 2));

    // Uncomment to make test fail
    // assert(not_equal(1, 1));
}
