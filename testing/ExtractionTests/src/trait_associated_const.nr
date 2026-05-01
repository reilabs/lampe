// Trait associated constants. Declared on the trait as kind-annotated
// "additional params" (alongside associated types); at a `Self::CONST` use
// site lampe resolves to the impl's chosen value.

pub trait HasConst {
    let N: u32;

    fn double_n() -> u32;
}

pub struct Foo {}
pub struct Bar {}

impl HasConst for Foo {
    let N: u32 = 5;

    fn double_n() -> u32 {
        Self::N * 2
    }
}

impl HasConst for Bar {
    let N: u32 = 10;

    fn double_n() -> u32 {
        Self::N * 2
    }
}

pub fn double_foo() -> u32 {
    <Foo as HasConst>::double_n()
}

pub fn double_bar() -> u32 {
    <Bar as HasConst>::double_n()
}
