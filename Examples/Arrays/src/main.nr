pub fn mtree_recover<let N : u32>(idx: [bool; N], p: [Field; N], item: Field) -> Field
{
    item
}

fn main(root: pub Field, proof : pub [Field; 32], idx : pub [bool; 32], item : pub Field) {
    assert(root == mtree_recover(idx, proof, item));
}
