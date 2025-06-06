// mod test;

trait BinaryHasher<F> {
    fn hash(a: F, b: F) -> F;
}

global RC: [Field; 8] = [
    17829420340877239108687448009732280677191990375576158938221412342251481978692,
    5852100059362614845584985098022261541909346143980691326489891671321030921585,
    17048088173265532689680903955395019356591870902241717143279822196003888806966,
    71577923540621522166602308362662170286605786204339342029375621502658138039,
    1630526119629192105940988602003704216811347521589219909349181656165466494167,
    7807402158218786806372091124904574238561123446618083586948014838053032654983,
    13329560971460034925899588938593812685746818331549554971040309989641523590611,
    16971509144034029782226530622087626979814683266929655790026304723118124142299,
];

global SIGMA: Field = 9915499612839321149637521777990102151350674507940716049588462388200839649614;

fn rl(u: u8) -> u8 {
    let top_bit = u >> 7;
    (u << 1) | top_bit
}

fn rotate_left(u: u8, N: u8) -> u8 {
    let mut result = u;
    for _ in 0..N {
        result = rl(result);
    }
    result
}

fn sbox(v: u8) -> u8 {
    let x1 = !v;
    let x2 = rotate_left(x1, 1);
    let x3 = rotate_left(v, 2);
    let x4 = rotate_left(v, 3);
    let x5 = x2 & x3 & x4;
    let x6 = rotate_left(x5, 1);
    v ^ x6
}

// NOTE: adapted from stdlib
fn from_le_bytes(bytes: [u8; 32]) -> Field {
    let mut v = 1;
    let mut result = 0;

    for i in 0..32 {
        result += (bytes[i] as Field) * v;
        v = v * 256;
    }
    result
}

// NOTE: adapted from stdlib
pub fn sgn0(self: Field) -> u1 {
    self as u1
}

// NOTE: hacky workaround
fn to_le_bits(self: Field) -> [u1; 256] {
    let mut val = self;
    let mut bits: [u1; 256] = [0; 256];

    for i in 0..256 {
        bits[i] = sgn0(val);
        if bits[i] == 0 {
            val = val / 2;
        } else {
            val = (val - 1) / 2;
        }
    }

    bits
}

// NOTE: hacky workaround
fn to_le_bytes(self: Field) -> [u8; 32] {
    let bits = to_le_bits(self);
    let mut bytes: [u8; 32] = [0; 32];

    for i in 0..32 {
        bytes[i] = (bits[8 * i] as u8)
            + 2 * (bits[8 * i + 1] as u8)
            + 4 * (bits[8 * i + 2] as u8)
            + 8 * (bits[8 * i + 3] as u8)
            + 16 * (bits[8 * i + 4] as u8)
            + 32 * (bits[8 * i + 5] as u8)
            + 64 * (bits[8 * i + 6] as u8)
            + 128 * (bits[8 * i + 7] as u8);
    }

    bytes
}

// NOTE: adapted from stdlib
fn as_array(self: [u8]) -> [u8; 32] {
    let mut array = [0; 32];
    for i in 0..32 {
        array[i] = self[i];
    }
    array
}

fn bar(a: Field) -> Field {
    let bytes: [u8; 32] = to_le_bytes(a);
    let mut new_left: [u8; 16] = [0; 16];
    let mut new_right: [u8; 16] = [0; 16];

    for i in 0..16 {
        new_left[i] = sbox(bytes[i]);
    }
    for i in 0..16 {
        new_right[i] = sbox(bytes[16 + i]);
    }

    let mut new_bytes = new_right.as_slice();

    for elem in new_left {
        new_bytes = new_bytes.push_back(elem);
    }

    let new_bytes_array: [u8; 32] = as_array(new_bytes);

    from_le_bytes(new_bytes_array)
}

fn square(a: Field) -> Field {
    a * a * SIGMA
}

fn permute(s: [Field; 2]) -> [Field; 2] {
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

pub struct Skyscraper {}

impl BinaryHasher<Field> for Skyscraper {
    fn hash(a: Field, b: Field) -> Field {
        let x = permute([a, b]);
        x[0] + a
    }
}

pub fn mtree_recover<H, let N: u32>(idx: [bool; N], p: [Field; N], item: Field) -> Field
where
    H: BinaryHasher<Field>,
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

unconstrained fn weird_eq_witness(a : Field, _b : Field) -> Field {
    a
}

// This is pointless, but demonstrated how we can use unconstrained functions
fn weird_assert_eq(a : Field, b : Field) {
    // Safety: Purely for test purposes
    let wit = unsafe { weird_eq_witness(a, b) };
    assert(wit == a);
    assert(wit == b);
}

fn main(root: pub Field, proof: pub [Field; 32], item: pub Field, idx: [bool; 32]) {
    let calculated_root = mtree_recover::<Skyscraper, _>(idx, proof, item);
    weird_assert_eq(root, calculated_root);
}
