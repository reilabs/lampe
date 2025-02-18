pub trait MHash<F> {
    fn hash_two(self, l: F, r: F) -> F;
}

/// Recovers the root hash of a Merkle tree `t` from the proof `p`.
/// `idx` is the index of the leaf in little endian.
/// `p` is the sibling roots starting from the leaf.
pub fn mtree_recover<F>(h: impl MHash<F>, idx: [bool], p: [F], item: F) -> F {
    assert(idx.len() == p.len());
    let mut curr_h = item;
    for i in 0..idx.len() {
        let dir = idx[i];
        let sibling_root = p[i];
        if dir {
            curr_h = h.hash_two(sibling_root, curr_h);
        } else {
            curr_h = h.hash_two(curr_h, sibling_root);
        }
    }
    curr_h
}

struct BabyHash;

impl MHash<Field> for BabyHash {
    fn hash_two(self, l: Field, r: Field) -> Field {
        (l + 2 * r) * 3
    }
}

#[test]
fn test_mtree_recover() {
    let h = BabyHash {};
    let _leaves = &[1, 2, 3, 4, 5, 6, 7, 8];
    // Index of `5` (i.e., `4`) in little endian.
    let idx = &[false, false, true];
    // Sibling roots starting from the leaf.
    let p = &[6, 69, 243];
    assert(mtree_recover(h, idx, p, 5) == 4131);
}
