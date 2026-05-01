// Issue #269: Noir allows signed integer kinds for numeric generics. Lampe
// must accept `let N: i32` etc. and emit Kind::I.

pub fn use_signed() -> i32 {
    foo::<7_i32>()
}

fn foo<let N: i32>() -> i32 {
    N
}
