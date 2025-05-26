trait Foo {
    type Out;
    fn foo(self) -> Self::Out
}

struct Pair {
    a : Field,
    b : Field
}

type Bar = Pair;

impl Foo for Pair {
    type Out = Field;

    fn foo(self) -> Self::Out {
        self.a
    }
}
