use std::hash::poseidon2_permutation;
use std::println;

global RATE: u32 = 3;

struct P2 {
    cache: [Field; 3],
    state: [Field; 4],
    cache_size: u32,
    squeeze_mode: bool,
}

fn p2_new(iv: Field) -> P2 {
    let mut result = P2 {
        cache: [0; 3],
        state: [0; 4],
        cache_size: 0,
        squeeze_mode: false,
    };
    result.state[RATE] = iv;
    result
}

fn p2_perform_duplex(self: &mut P2) {
    for i in 0..RATE {
        if i < self.cache_size {
            self.state[i] += self.cache[i];
        }
    }
    self.state = poseidon2_permutation(self.state, 4);
}

fn p2_absorb(self: &mut P2, input: Field) {
    assert(!self.squeeze_mode);
    if self.cache_size == RATE {
        p2_perform_duplex(self);
        self.cache[0] = input;
        self.cache_size = 1;
    } else {
        self.cache[self.cache_size] = input;
        self.cache_size += 1;
    }
}

fn p2_squeeze(self: &mut P2) -> Field {
    assert(!self.squeeze_mode);
    p2_perform_duplex(self);
    self.squeeze_mode = true;
    self.state[0]
}

fn p2_hash<let N: u32>(input: [Field; N], in_len: u32, variable_length: bool) -> Field {
    let two_pow_64 = 18446744073709551616;
    let iv: Field = (in_len as Field) * two_pow_64;
    let mut sponge = p2_new(iv);

    for i in 0..N {
        if i < in_len {
            p2_absorb(&mut sponge, input[i]);
        }
    }

    if variable_length {
        p2_absorb(&mut sponge, 1);
    }

    p2_squeeze(&mut sponge)
}

#[test]
fn print_poseidon_vectors() {
    // The printed values come from Noir itself, so they are convenient fixtures but not
    // independent evidence of correctness.
    println(poseidon2_permutation([0, 1, 2, 3], 4));
    println(poseidon2_permutation([1, 2, 3, 4], 4));
    println(p2_hash([1, 2, 3], 3, false));
    println(p2_hash([1, 2, 0], 2, true));
}

fn main() {}
