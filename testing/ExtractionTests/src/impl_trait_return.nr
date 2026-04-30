trait Foo {
    fn foo(self) -> Field;
    fn as_impl(self) -> impl Foo;
}

struct Bar {}

impl Foo for Bar {
    fn foo(self) -> Field {
        42
    }
    fn as_impl(self) -> impl Foo {
        self
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
