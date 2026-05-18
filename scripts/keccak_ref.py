#!/usr/bin/env python3
"""Reference Keccak-f[1600] implementation for test vector generation.

Direct port of FIPS 202 Section 3.2. ~30 lines for the permutation
itself. Validates against the canonical all-zeros vector before
emitting more test cases.
"""

RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
      0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
      0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
      0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
      0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
      0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
      0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
      0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

R = [ 0,  1, 62, 28, 27,
     36, 44,  6, 55, 20,
      3, 10, 43, 25, 39,
     41, 45, 15, 21,  8,
     18,  2, 61, 56, 14]

MASK = (1 << 64) - 1

def rotl(x, n): return ((x << n) | (x >> (64 - n))) & MASK

def keccak_f1600(s):
    s = list(s)
    for rnd in range(24):
        # theta
        C = [s[x] ^ s[x+5] ^ s[x+10] ^ s[x+15] ^ s[x+20] for x in range(5)]
        D = [C[(x+4) % 5] ^ rotl(C[(x+1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                s[x + 5*y] ^= D[x]
        # rho + pi
        new_s = [0] * 25
        for x in range(5):
            for y in range(5):
                src = (x + 3*y) % 5 + 5*x
                new_s[x + 5*y] = rotl(s[src], R[src])
        s = new_s
        # chi
        new_s = [0] * 25
        for x in range(5):
            for y in range(5):
                new_s[x + 5*y] = s[x + 5*y] ^ ((~s[(x+1) % 5 + 5*y]) & s[(x+2) % 5 + 5*y] & MASK)
        s = new_s
        # iota
        s[0] ^= RC[rnd]
    return s

# Sanity: all-zeros vector
expected_zero_lane0 = 0xf1258f7940e1dde7
assert keccak_f1600([0]*25)[0] == expected_zero_lane0, "zeros test vector mismatch"

def fmt_lane(x):
    return f"0x{x:016x}#64"

def emit(name, inp, comment=""):
    out = keccak_f1600(inp)
    lanes_in = "[" + ", ".join(fmt_lane(v) for v in inp) + "]"
    lanes_out = "[" + ", ".join(fmt_lane(v) for v in out) + "]"
    print(f"-- {comment}" if comment else f"-- vector: {name}")
    print(f"private def {name}In : List.Vector (BitVec 64) 25 := ⟨{lanes_in}, by decide⟩")
    print(f"private def {name}Out : List.Vector (BitVec 64) 25 := ⟨{lanes_out}, by decide⟩")
    print(f"theorem keccakF1600_{name}_correct :")
    print(f"    keccakF1600State {name}In = {name}Out := by native_decide")
    print()

# Vector 1: all zeros (already have, regenerate for completeness)
emit("zeros", [0]*25, "All-zeros input. Canonical Keccak team reference.")

# Vector 2: one bit set in lane 0
emit("oneBit", [1] + [0]*24, "Lane 0 = 0x1, rest zero.")

# Vector 3: ascending lane values 0..24
emit("ascending", list(range(25)), "Lanes 0,1,2,...,24.")

# Vector 4: SHA3-256 IV-ish (alternating high/low)
emit("alternating", [0xAAAAAAAAAAAAAAAA, 0x5555555555555555] * 12 + [0xFFFFFFFFFFFFFFFF],
     "Alternating 0xAA / 0x55 with trailing 0xFF.")

# Vector 5: maximum value (all ones)
emit("allOnes", [MASK]*25, "All lanes = 2^64 - 1.")
