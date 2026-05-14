use std::hash::poseidon2_permutation;

fn poseidon2_hash(input: [Field; 3], in_len: u32, is_variable_length: bool) -> Field {
    let iv = in_len as Field * 18446744073709551616;
    let mut state = [0, 0, 0, iv];
    let mut absorbed = 0;

    for i in 0..input.len() {
        if i < in_len {
            if absorbed == 3 {
                state = poseidon2_permutation(state, 4);
                absorbed = 0;
            }

            state[absorbed] += input[i];
            absorbed += 1;
        }
    }

    if is_variable_length {
        if absorbed == 3 {
            state = poseidon2_permutation(state, 4);
            absorbed = 0;
        }

        state[absorbed] += 1;
    }

    state = poseidon2_permutation(state, 4);
    state[0]
}

#[test]
fn poseidon2_permutation_matches_reference_vectors() {
    // These expected outputs are circular as evidence: they were generated from Noir's own
    // implementation and are only useful as a regression tripwire for accidental changes.
    // A stronger future check would compare against an independently formalized or parameterized
    // Poseidon2 implementation and prove the instantiated permutation matches Noir's semantics.
    let expected_0 = [
        0x01bd538c2ee014ed5141b29e9ae240bf8db3fe5b9a38629a9647cf8d76c01737,
        0x239b62e7db98aa3a2a8f6a0d2fa1709e7a35959aa6c7034814d9daa90cbac662,
        0x04cbb44c61d928ed06808456bf758cbf0c18d1e15a7b6dbc8245fa7515d5e3cb,
        0x2e11c5cff2a22c64d01304b778d78f6998eff1ab73163a35603f54794c30847a,
    ];
    let expected_1 = [
        0x224785a48a72c75e2cbb698143e71d5d41bd89a2b9a7185871e39a54ce5785b1,
        0x225bb800db22c4f4b09ace45cb484d42b0dd7dfe8708ee26aacde6f2c1fb2cb8,
        0x1180f4260e60b4264c987b503075ea8374b53ed06c5145f8c21c2aadb5087d21,
        0x16c877b5b9c04d873218804ccbf65d0eeb12db447f66c9ca26fec380055df7e9,
    ];

    assert(poseidon2_permutation([0, 1, 2, 3], 4) == expected_0);
    assert(poseidon2_permutation([1, 2, 3, 4], 4) == expected_1);
}

#[test]
fn poseidon2_hash_matches_reference_vectors() {
    // This duplicates Noir stdlib's cached sponge logic and compares against hard-coded outputs
    // derived from Noir itself, so it is also circular. Keeping the test is still useful for
    // catching unintended changes in the current Noir-facing semantics until we have a genuinely
    // independent implementation or a parameterized proof that another formalization instantiates
    // to the same function.
    let fixed_length = 0x23864adb160dddf590f1d3303683ebcb914f828e2635f6e85a32f0a1aecd3dd8;
    let variable_length = 0x05183cc69f95f56ec1bbd9eedd6f337448abba8ed4bc19799ae2c684fea26dfe;

    assert(poseidon2_hash([1, 2, 3], 3, false) == fixed_length);
    assert(poseidon2_hash([1, 2, 0], 2, true) == variable_length);
}
