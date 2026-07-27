// Inclusive ranges (`start..=end`) must extract to a loop that includes the
// final iteration (regression test for the extractor dropping it).
pub fn sum_inclusive(n: u32) -> u32 {
    let mut sum = 0;
    for i in 0..=n {
        sum = sum + i;
    }
    sum
}
