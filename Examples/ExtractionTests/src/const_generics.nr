pub fn nat_generic_test<let N: u32>() -> [Field; N] {
    for i in 0..N {
        let _ = i;
    }
    [1; N]
}

pub fn nat_generic_test_2<let N: u8>(x: Field) -> Field {
    let mut res = x;
    for _ in 0..N {
        res = res * 2;
    }
    res
}
