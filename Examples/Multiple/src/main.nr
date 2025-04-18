use bar::Asdf2;

pub mod foo;
pub mod bar;
pub mod baz;

pub type Asdf3 = Asdf2;

fn main(x: Field) -> pub Field {
    let mut x = x;
    x = foo::foo(x);
    x = bar::bar(x);
    x = baz::bang::bang(x);

    x
}
