use std::hint::black_box;

pub fn black_box_mut(b: u32) -> u32 {
    let mut d = b;
    let mut c = 0;
    set_ref(&mut c, &mut black_box(d));
    c
}

fn set_ref(c: &mut u32, b: &mut u32) {
    *c = *b;
}
