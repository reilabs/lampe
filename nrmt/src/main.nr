trait BinaryHasher<F> {
    fn hash(a: F, b: F) -> F;
}

struct DummyHasher {}

impl BinaryHasher<Field> for DummyHasher {
    fn hash(a: Field, b: Field) -> Field {
        a + b
    }
}

pub fn mtree_recover<H, let N : u32>(idx: [bool; N], p: [Field; N], item: Field) -> Field
    where H: BinaryHasher<Field>
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

fn main(x: Field, y: pub Field) {
    assert(x != y);
}

#[test]
fn test_main() {
    main(1, 2);

    // Uncomment to make test fail
    // main(1, 1);
}
