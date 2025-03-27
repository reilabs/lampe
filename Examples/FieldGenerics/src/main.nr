global A: Field = 4294967297;

fn foo<let A: Field>() -> Field { A }

fn main() {
    let _ = foo::<A>();
}
