use crate::bar::bar;
use crate::globals::RC;
use crate::utils::square;

pub fn permute(s: [Field; 2]) -> [Field; 2] {
    let (l, r) = (s[0], s[1]);
    let (l, r) = (r + square(l), l);
    let (l, r) = (r + square(l) + RC[0], l);
    let (l, r) = (r + bar(l) + RC[1], l);
    let (l, r) = (r + bar(l) + RC[2], l);
    let (l, r) = (r + square(l) + RC[3], l);
    let (l, r) = (r + square(l) + RC[4], l);
    let (l, r) = (r + bar(l) + RC[5], l);
    let (l, r) = (r + bar(l) + RC[6], l);
    let (l, r) = (r + square(l) + RC[7], l);
    let (l, r) = (r + square(l), l);
    [l, r]
}
