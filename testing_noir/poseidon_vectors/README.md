# Poseidon Vector Validation

Scratch Noir project for validating the BN254 Poseidon2 vectors used by Lampe.

Validation boundary:
- The harness only uses the public `std::hash::poseidon2_permutation` entrypoint.
- The sponge logic in `src/lib.nr` is a local replica of Noir stdlib's cached Poseidon2 sponge.
- The checked outputs are currently hard-coded from Noir itself, so this harness is circular as
  evidence for correctness. Its value today is regression detection, not independent validation.
- A stronger future story would compare against an independent implementation or prove that another
  parameterized Poseidon formalization instantiates to the same semantics.

Checked vectors:
- `poseidon2_permutation([0, 1, 2, 3], 4)`
- `poseidon2_permutation([1, 2, 3, 4], 4)`
- `Poseidon2::hash([1, 2, 3], 3, false)` as the fixed-length case
- `Poseidon2::hash([1, 2, 0], 2, true)` as the variable-length case

Run with:

```bash
nargo test --show-output
```

