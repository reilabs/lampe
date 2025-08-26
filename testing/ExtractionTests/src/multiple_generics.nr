pub trait Foo<I> {
    fn foo3(self) -> I;
}

pub struct Pair<I> {
    a : I,
    b : I,
}

impl<I> Foo<I> for Pair<I> {
    fn foo3(self) -> I {
        self.a
    }
}
