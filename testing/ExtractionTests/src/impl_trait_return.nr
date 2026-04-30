trait Foo {
    fn foo(self) -> Field;
    // fn as_impl(self) -> impl Foo; // TODO: requires Tp.any support in trait declarations
}

struct Bar {}

impl Foo for Bar {
    fn foo(self) -> Field {
        42
    }
}

pub fn some_foo() -> impl Foo {
    Bar {}
}

pub fn wrap_foo() -> impl Foo {
    some_foo()
}

pub fn use_foo() -> Field {
    wrap_foo().foo()
}
