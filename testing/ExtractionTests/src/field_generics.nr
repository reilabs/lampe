global A: Field = 4294967297;

fn foo1<let A: Field>() -> Field { A }

#[allow(dead_code)]
fn main() {
    let _ = foo1::<A>();
}
