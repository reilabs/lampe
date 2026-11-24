// Issue #319: a call whose generic arguments repeat a value (here `N = M = 2`)
// must pass all of them, not drop the repeated one.
pub fn total_len<let N: u32, let M: u32>(_a: [Field; N], _b: [Field; M]) -> u32 {
    N + M
}

pub fn same_lengths() -> u32 {
    total_len([1, 2], [3, 4])
}
