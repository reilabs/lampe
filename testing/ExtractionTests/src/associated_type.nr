pub trait Foo {
    type Out;
    fn foo_meth(self) -> Self::Out;
}

pub struct Pair {
    a : Field,
    b : Field
}

pub type Bar = Pair;

impl Foo for Pair {
    type Out = Field;

    fn foo_meth(self) -> Self::Out {
        self.a
    }
}
