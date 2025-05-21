trait Foo<I> {
    fn foo(self) -> I
}

struct Pair<I> {
    a : I,
    b : I,
}

impl<I> Foo<I> for Pair<I> {
    fn foo(self) -> I {
        self.a
    }
}
