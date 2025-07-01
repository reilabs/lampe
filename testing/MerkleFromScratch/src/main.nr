pub mod bar;
pub mod globals;
pub mod hasher;
pub mod permute;
pub mod skyscraper;
pub mod utils;
pub mod witness;

pub fn mtree_recover<H, let N: u32>(idx: [bool; N], p: [Field; N], item: Field) -> Field
where
    H: hasher::BinaryHasher<Field>,
{
    let mut curr_h = item;
    for i in 0..N {
        let dir = idx[i];
        let sibling_root = p[i];
        if dir {
            curr_h = H::hash(sibling_root, curr_h);
        } else {
            curr_h = H::hash(curr_h, sibling_root);
        }
    }
    curr_h
}

fn main(root: pub Field, proof: pub [Field; 32], item: pub Field, idx: [bool; 32]) {
    let calculated_root = mtree_recover::<skyscraper::Skyscraper, _>(idx, proof, item);
    witness::weird_assert_eq(root, calculated_root);
}