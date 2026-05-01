trait Foo {
    fn foo(self) -> Field;
    fn as_impl(self) -> impl Foo;
}

struct Bar {}
struct Baz { x: Field }

impl Foo for Bar {
    fn foo(self) -> Field {
        42
    }
    fn as_impl(self) -> impl Foo {
        self
    }
}

impl Foo for Baz {
    fn foo(self) -> Field {
        self.x
    }
    fn as_impl(self) -> impl Foo {
        self
    }
}

fn call_foo<T>(x: T) -> Field where T: Foo {
    x.foo()
}

fn get_impl_bar() -> impl Foo {
    Bar {}
}

fn get_impl_baz() -> impl Foo {
    Baz { x: 99 }
}

pub fn use_bar() -> Field {
    call_foo(get_impl_bar())
}

pub fn use_baz() -> Field {
    call_foo(get_impl_baz())
}
