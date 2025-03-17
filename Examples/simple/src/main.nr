use other::{bar, foo};

mod other;

fn main(x: Field, y: pub Field) -> pub Field {
    bar(x) + foo(y)
}

#[test]
fn asdf() {
    assert_eq(main(1,2), 5);
}
