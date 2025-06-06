fn not_equal(x: Field, y: Field) -> bool {
    x != y
}

global hello: str<24> = "hello-git-dep-with-lampe";
global hello_git_dep_with_lampe: str<24> = "hello-git-dep-with-lampe";

#[test]
fn test_not_equal() {
    assert(not_equal(1, 2));

    // Uncomment to make test fail
    // assert(not_equal(1, 1));
}
