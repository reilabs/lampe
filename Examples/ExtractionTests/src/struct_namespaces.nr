mod test {
    pub struct Foo {
        i: Field,
    }

    impl Foo {
        pub fn bar(self) -> Field {
            self.i
        }

        pub fn bar2() -> Field {
            3
        }
    }
}

use test::Foo;

pub fn baz(a: Foo) -> Field {
    let x = Foo::bar2();
    let y = a.bar();
    x + y
}
