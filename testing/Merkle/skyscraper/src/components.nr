use crate::globals;

pub fn rl(u: u8) -> u8 {
    let top_bit = u >> 7;
    (u << 1) | top_bit
}

pub fn rotate_left(u: u8, N: u8) -> u8 {
    let mut result = u;
    for _ in 0..N {
        result = rl(result);
    }
    result
}

pub fn sbox(v: u8) -> u8 {
    let x1 = !v;
    let x2 = rotate_left(x1, 1);
    let x3 = rotate_left(v, 2);
    let x4 = rotate_left(v, 3);
    let x5 = x2 & x3 & x4;
    let x6 = rotate_left(x5, 1);
    v ^ x6
}

pub fn square(a: Field) -> Field {
    a * a * globals::SIGMA
}
