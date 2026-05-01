// Trait associated constants - handled the same way as associated types: the
// trait declares them in the `[...]` slot, and use sites reference them by
// name into that scope.

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

// Polymorphic use at type level. Static resolution is impossible here because
// `T` is a generic parameter - Noir surfaces `<T as HasConst>::N` as an
// extra const-generic on the function, which is exactly what we need for a
// trait-abstracted associated constant.
pub fn poly_array<T>() -> [u32; <T as HasConst>::N]
where
    T: HasConst,
{
    [0; <T as HasConst>::N]
}

pub fn use_foo_array() -> [u32; 5] {
    poly_array::<Foo>()
}

pub fn use_bar_array() -> [u32; 10] {
    poly_array::<Bar>()
}
