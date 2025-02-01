trait MHash<F> {
    fn hash_two(self, l: F, r: F) -> F;
}

/// Represents a Merkle tree with hash digests of `F`.
struct MTree<F> {
    leafs: [F],
    is_leaf: bool,
}

impl<F> MTree<F> {
    /// Builds a Merkle tree of depth `d` from a list of leafs of length `2^d`.
    /// If the length of `leafs` is 1, then this builds a leaf (`d = 0`) instead.
    fn build(leafs: [F]) -> Self {
        assert(leafs.len() > 0);
        let is_leaf = leafs.len() == 1;
        assert((leafs.len() % 2 == 0) | is_leaf);
        Self { leafs, is_leaf }
    }

    /// Builds a Merkle tree from two subtrees/leafs.
    fn build_from(l: MTree<F>, r: MTree<F>) -> Self {
        let leafs = l.leafs.append(r.leafs);
        Self::build(leafs)
    }

    /// Returns the left subtree of a non-leaf Merkle tree.
    fn left(self) -> MTree<F> {
        assert(!self.is_leaf);
        let mut l_leafs = &[];
        for i in 0..self.leafs.len() / 2 {
            l_leafs = l_leafs.push_back(self.leafs[i]);
        }
        Self::build(l_leafs)
    }

    /// Returns the right subtree of a non-leaf Merkle tree.
    fn right(self) -> MTree<F> {
        assert(!self.is_leaf);
        let mut r_leafs = &[];
        for i in (self.leafs.len() / 2)..self.leafs.len() {
            r_leafs = r_leafs.push_back(self.leafs[i]);
        }
        Self::build(r_leafs)
    }

    /// Returns the subtree in the direction of the given direction `dir`
    /// where `false` denotes the left direction and `true` denotes the right direction.
    fn treeFor(self, dir: bool) -> MTree<F> {
        assert(!self.is_leaf);
        if dir {
            self.right()
        } else {
            self.left()
        }
    }

    /// Returns the leaf at the given index denoted by `idx`.
    /// If `self` is a leaf, then `idx` must be empty, and this returns the value of the leaf.
    fn getLeaf(self, idx: [bool]) -> F {
        if self.is_leaf {
            assert(idx.len() == 0);
            self.leafs[0]
        } else {
            assert(idx.len() > 0);
            let (dir, rem) = idx.pop_front();
            if dir {
                self.right().getLeaf(rem)
            } else {
                self.left().getLeaf(rem)
            }
        }
    }

    /// Sets the leaf at the given index denoted by `idx` to `new_leaf` and returns the new tree.
    /// If `self` is a leaf, then `idx` must be empty, and this updates the value of the leaf.
    fn setLeaf(self, idx: [bool], new_leaf: F) -> MTree<F> {
        if self.is_leaf {
            assert(idx.len() == 0);
            MTree::build([new_leaf])
        } else {
            assert(idx.len() > 0);
            let (dir, rem) = idx.pop_front();
            if dir {
                let l = self.left();
                let r = self.right().setLeaf(rem, new_leaf);
                MTree::build_from(l, r)
            } else {
                let l = self.left().setLeaf(rem, new_leaf);
                let r = self.right();
                MTree::build_from(l, r)
            }
        }
    }

    /// Returns the root hash of this Merkle tree/leaf.
    /// If `self` is a leaf, then this returns the value of the leaf.
    fn root(self, h: impl MHash<F>) -> F {
        if self.is_leaf {
            self.leafs[0]
        } else {
            let l = self.left();
            let r = self.right();
            h.hash_two(l.root(h), r.root(h))
        }
    }

    /// Returns the Merkle proof for the leaf at `idx`.
    /// If `self` is a leaf, then `idx` must be empty, and this returns an empty list.
    ///
    /// The proof represents the minimal information that can be used to reconstruct `self.root(h)` from the leaf at `idx`.
    fn proof(self, h: impl MHash<F>, idx: [bool]) -> [F] {
        if self.is_leaf {
            assert(idx.len() == 0);
            &[]
        } else {
            assert(idx.len() > 0);
            let (dir, rem) = idx.pop_front();
            // Get the root hash of the sibling subtree.
            let root_proof = self.treeFor(!dir).root(h);
            // Get the subproofs for the remaining path.
            let rem_proofs = self.treeFor(dir).proof(h, rem);
            &[root_proof].append(rem_proofs)
        }
    }

    /// Recovers the root hash of a Merkle tree `t` from the proof `p` such that `p = t.proof(h, idx)` and `idx` is the supposed index of `item` in `t`.
    /// Accordingly, we must have `t.root(h) == recover(h, idx, p, item)`.
    fn recover(h: impl MHash<F>, idx: [bool], p: [F], item: F) -> F {
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
