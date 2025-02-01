pub trait MHash<F> {
    fn hash_two(self, l: F, r: F) -> F;
}

/// Returns the numerical index from a boolean index.
/// If `idx` is empty, this returns 0.
///
/// [TODO] This should be a `from_bits` call.
fn abs_idx(idx: [bool]) -> u32 {
    let mut abs_idx = 0 as u32;
    for dir in idx {
        abs_idx = abs_idx * 2 + (dir as u32);
    }
    abs_idx
}

/// Represents a Merkle tree with hash digests of `F`.
pub struct MTree<F> {
    leaves: [F],
    depth: u32,
}

impl<F> MTree<F> {
    /// Builds a Merkle tree of depth `d` from a list of leaves of length `2^d`.
    /// If `d = 0`, then the tree is a leaf with a single leaf node.
    fn build(leaves: [F], d: u32) -> Self {
        Self { leaves, depth: d }
    }

    /// Builds a Merkle tree from two subtrees/leaves.
    fn build_from(l: MTree<F>, r: MTree<F>) -> Self {
        assert(l.depth == r.depth);
        let leaves = l.leaves.append(r.leaves);
        Self::build(leaves, l.depth + 1)
    }

    /// Returns `true` iff this Merkle tree is a leaf.
    pub fn is_leaf(self) -> bool {
        self.depth == 0
    }

    /// Returns the left subtree of a non-leaf Merkle tree.
    fn left(self) -> MTree<F> {
        assert(self.depth > 0);
        let mut l_leaves = &[];
        for i in 0..self.leaves.len() / 2 {
            l_leaves = l_leaves.push_back(self.leaves[i]);
        }
        Self::build(l_leaves, self.depth - 1)
    }

    /// Returns the right subtree of a non-leaf Merkle tree.
    fn right(self) -> MTree<F> {
        assert(self.depth > 0);
        let mut r_leaves = &[];
        for i in (self.leaves.len() / 2)..self.leaves.len() {
            r_leaves = r_leaves.push_back(self.leaves[i]);
        }
        Self::build(r_leaves, self.depth - 1)
    }

    /// Returns the child subtree in the direction of the given direction `dir`
    /// where `0` denotes the left direction and `1` denotes the right direction.
    pub fn child(self, dir: bool) -> MTree<F> {
        if dir {
            self.right()
        } else {
            self.left()
        }
    }

    /// Returns the leaf at the given index denoted by `idx`.
    /// If `self` is a leaf, then `idx` must be empty, and this returns the value of the leaf.
    pub fn get_leaf(self, idx: [bool]) -> F {
        let mut tree = self;
        for dir in idx {
            tree = tree.child(dir);
        }
        tree.leaves[0]
    }

    /// Sets the leaf at the given index denoted by `idx` to `new_leaf` and returns the new tree.
    /// If `self` is a leaf, then this updates the value of the leaf.
    pub fn set_leaf(self, idx: [bool], new_leaf: F) -> MTree<F> {
        let mut new_leaves = self.leaves;
        let mut abs_idx = abs_idx(idx);
        new_leaves[abs_idx] = new_leaf;
        MTree::build(new_leaves, self.depth)
    }

    /// Reduces the Merkle tree once by using `h`.
    /// Reducing means that the tree is reduced by one level by hashing adjacent leaves.
    fn reduce_leaves(self, h: impl MHash<F>) -> MTree<F> {
        assert(self.depth > 0);
        let mut leaves = &[];
        for j in 1..self.leaves.len() {
            if (j + 1) % 2 == 0 {
                let l = self.leaves[j - 1];
                let r = self.leaves[j];
                let h = h.hash_two(l, r);
                leaves = leaves.push_back(h);
            }
        }
        MTree::build(leaves, self.depth - 1)
    }

    /// Returns the root hash of this Merkle tree/leaf.
    /// If `self` is a leaf, then this returns the value of the leaf.
    pub fn root(self, h: impl MHash<F>) -> F {
        let mut t = self;
        for _ in 0..self.depth {
            t = t.reduce_leaves(h);
        }
        t.leaves[0]
    }

    /// Returns the Merkle proof for the leaf at `idx`.
    /// If `self` is a leaf, then this returns an empty list.
    ///
    /// The proof represents the minimal information that can be used to reconstruct `self.root(h)` from the leaf at `idx`.
    pub fn proof(self, h: impl MHash<F>, idx: [bool]) -> [F] {
        if self.is_leaf() {
            &[]
        } else {
            let mut proof = &[];
            let mut t = self;
            for dir in idx {
                let sibling_root = t.child(!dir).root(h);
                proof = proof.push_back(sibling_root);
                t = t.child(dir);
            }
            proof
        }
    }

    /// Recovers the root hash of a Merkle tree `t` from the proof `p` such that `p = t.proof(h, idx)` and `idx` is the supposed index of `item` in `t`.
    /// Accordingly, we must have `t.root(h) == recover(h, idx, p, item)`.
    pub fn recover(h: impl MHash<F>, idx: [bool], p: [F], item: F) -> F {
        assert(idx.len() == p.len());
        if idx.len() == 0 {
            item
        } else {
            let (dir, rem_idx) = idx.pop_front();
            let (sibling_root, rem_proof) = p.pop_front();
            let rec = Self::recover(h, rem_idx, rem_proof, item);
            if dir {
                h.hash_two(sibling_root, rec)
            } else {
                h.hash_two(rec, sibling_root)
            }
        }
    }
}

struct AddFields;

impl MHash<Field> for AddFields {
    fn hash_two(self, l: Field, r: Field) -> Field {
        (l + r)
    }
}

#[test]
fn test_mtree_basic() {
    let leaves = &[1, 2, 3, 4];
    let tree = MTree::build(leaves, 2);
    assert(tree.leaves == leaves);
    assert(!tree.is_leaf());
    assert(tree.left().leaves == &[1, 2]);
    assert(!tree.left().is_leaf());
    assert(tree.left().left().is_leaf());
    assert(tree.left().left().leaves == &[1]);
    assert(tree.left().right().leaves == &[2]);
    assert(tree.left().right().is_leaf());
    // get_leaf
    assert(tree.get_leaf(&[true, false]) == 3);
    assert(tree.get_leaf(&[true, true]) == tree.right().right().get_leaf(&[]));
    // set_leaf
    let new_tree = tree.set_leaf(&[true, false], 5);
    assert(tree.get_leaf(&[true, false]) == 3);
    assert(new_tree.get_leaf(&[true, false]) == 5);
}

#[test]
fn test_mtree_root() {
    let h = AddFields {};
    let leaves = &[1, 2, 3, 4];
    let tree = MTree::build(leaves, 2);
    assert(tree.root(h) == 10);
    let leaves = &[1, 2, 3, 4, 5, 6, 7, 8];
    let tree = MTree::build(leaves, 3);
    assert(tree.root(h) == 36);
}

#[test]
fn test_mtree_proof() {
    let h = AddFields {};
    let leaves = &[1, 2, 3, 4, 5, 6, 7, 8];
    let tree = MTree::build(leaves, 3);
    assert(tree.proof(h, &[true, false, false]) == &[10, 15, 6]);
}

#[test]
fn test_mtree_recover() {
    let h = AddFields {};
    let leaves = &[1, 2, 3, 4, 5, 6, 7, 8];
    let tree = MTree::build(leaves, 3);
    let idx = &[true, false, false];
    let p = tree.proof(h, idx);
    assert(MTree::recover(h, idx, p, 5) == tree.root(h));
}
