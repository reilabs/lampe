// Regression test for https://github.com/reilabs/lampe/issues/263
// A mutable variable shadowed by an immutable binding of the same name
// must not cause an "Application type mismatch" on the new binding.

pub fn shadow_mut() -> [u32; 2] {
    let mut v = &[1, 2, 3];
    let (_, v) = v.pop_front();
    v.as_array()
}
