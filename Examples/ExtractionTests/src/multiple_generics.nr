pub trait Foo<I> {
    fn foo(self) -> I;
}

pub struct Pair<I> {
    a : I,
    b : I,
}

impl<I> Foo<I> for Pair<I> {
    fn foo(self) -> I {
        self.a
    }
}
