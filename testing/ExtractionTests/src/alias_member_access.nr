// Regression test for GitHub issue #268:
// Panic: "Attempted to access member on non-struct or non-tuple type" on alias.
//
// The extractor should resolve through type aliases when generating member access.

pub type Foo<A, B> = (A, B);

pub fn alias_member_first(foo: Foo<u8, u32>) -> u8 {
    foo.0
}

pub fn alias_member_second(foo: Foo<u8, u32>) -> u32 {
    foo.1
}

pub fn alias_member_assert() {
    let foo: Foo<u8, u32> = (1, 2);
    assert(foo.0 == 1);
    assert(foo.1 == 2);
}
