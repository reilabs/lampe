struct MTree<H> {
    digest: H,
    children: Vec<MTree<H>>,
}

impl <H> MTree<H> where H: Hash {
    fn new_leaf(digest: H) -> MTree<H> {
        MTree { digest, children: Vec::new() }
    }

    fn new_parent(children: Vec<MTree<H>>) -> MTree<H> {
        let mut hasher = H::new();
        for child in &children {
            hasher.update(&child.digest);
        }
        let digest = hasher.finalize();
        MTree { digest, children }
    }
}
