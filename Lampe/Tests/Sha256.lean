import Lampe
import Lampe.Crypto.Sha256

/-!
# Sha256 compression — driver-level test vectors

These re-run the FIPS 180-2 Appendix B SHA-256 worked examples through
the public `Crypto.Sha256.compressOne` entry point. The same vectors are
also covered (as `private` theorems) inside `Lampe/Crypto/Sha256.lean`;
duplicating them at the Tests layer makes them visible to `lake test`
and protects the public surface from accidental regressions.

Reference: FIPS 180-2 "Secure Hash Standard" Appendix B (single-block
"abc" example in §B.1; two-block "abcdbcdec..." example in §B.2, from
which we take the final hash).

  https://csrc.nist.gov/csrc/media/publications/fips/180/2/archive/
  2002-08-01/documents/fips180-2.pdf
-/

namespace Tests.Sha256

open Lampe.Crypto.Sha256

/-- FIPS 180-2 §B.1: padded "abc" against the IV gives the final
SHA-256 hash of "abc". -/
example :
    compressOne
        ⟨[ 0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
           0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32 ],
         by rfl⟩
        ⟨[ 0x61626380#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
           0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
           0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
           0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000018#32 ],
         by rfl⟩
      =
    ⟨[ 0xba7816bf#32, 0x8f01cfea#32, 0x414140de#32, 0x5dae2223#32,
       0xb00361a3#32, 0x96177a9c#32, 0xb410ff61#32, 0xf20015ad#32 ],
     by rfl⟩ := by native_decide

/-- FIPS 180-2 §B.2: second-block compression of the two-block example
takes the intermediate H^(1) (also printed in the standard) to the
final published hash H^(2). -/
example :
    compressOne
        ⟨[ 0x85e655d6#32, 0x417a1795#32, 0x3363376a#32, 0x624cde5c#32,
           0x76e09589#32, 0xcac5f811#32, 0xcc4b32c1#32, 0xf20e533a#32 ],
         by rfl⟩
        ⟨[ 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
           0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
           0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
           0x00000000#32, 0x00000000#32, 0x00000000#32, 0x000001c0#32 ],
         by rfl⟩
      =
    ⟨[ 0x248d6a61#32, 0xd20638b8#32, 0xe5c02693#32, 0x0c3e6039#32,
       0xa33ce459#32, 0x64ff2167#32, 0xf6ecedd4#32, 0x19db06c1#32 ],
     by rfl⟩ := by native_decide

end Tests.Sha256
