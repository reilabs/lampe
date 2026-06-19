import Lampe
import Lampe.Crypto.Keccak

/-!
# Keccak-f[1600] reference test vectors

End-to-end checks against the concrete `keccakF1600State` permutation.

Both vectors are anchored to the official XKCP Known-Answer-Tests file
`tests/TestVectors/KeccakF-1600-IntermediateValues.txt`:
  https://github.com/XKCP/XKCP/blob/master/tests/TestVectors/KeccakF-1600-IntermediateValues.txt

That file documents two consecutive applications of the permutation:
  - Vector 1: input = all-zeros state, output = "state after permutation".
  - Vector 2: input = Vector 1's output, output = "state after permutation"
    of the second application.

This is Keccak-f[1600], the underlying permutation. It is identical
between FIPS 202 SHA-3 and Ethereum's keccak256 — the two differ only
in the sponge-layer padding byte (`0x06` vs `0x01`), which lives above
this function.
-/

namespace Tests.Keccak

open Lampe.Crypto.Keccak

/-! ### Vector 1: all-zeros input
XKCP `KeccakF-1600-IntermediateValues.txt`, "state after permutation"
of the first application. -/

private def zerosIn : List.Vector (BitVec 64) 25 :=
  ⟨List.replicate 25 0, by decide⟩

private def zerosOut : List.Vector (BitVec 64) 25 :=
  ⟨[0xf1258f7940e1dde7#64, 0x84d5ccf933c0478a#64, 0xd598261ea65aa9ee#64,
    0xbd1547306f80494d#64, 0x8b284e056253d057#64, 0xff97a42d7f8e6fd4#64,
    0x90fee5a0a44647c4#64, 0x8c5bda0cd6192e76#64, 0xad30a6f71b19059c#64,
    0x30935ab7d08ffc64#64, 0xeb5aa93f2317d635#64, 0xa9a6e6260d712103#64,
    0x81a57c16dbcf555f#64, 0x43b831cd0347c826#64, 0x01f22f1a11a5569f#64,
    0x05e5635a21d9ae61#64, 0x64befef28cc970f2#64, 0x613670957bc46611#64,
    0xb87c5a554fd00ecb#64, 0x8c3ee88a1ccf32c8#64, 0x940c7922ae3a2614#64,
    0x1841f924a2c509e4#64, 0x16f53526e70465c2#64, 0x75f644e97f30a13b#64,
    0xeaf1ff7b5ceca249#64], by decide⟩

theorem keccakF1600_zeros_correct :
    (keccakF1600State zerosIn).toList = zerosOut.toList := by native_decide

/-! ### Vector 2: second application
XKCP `KeccakF-1600-IntermediateValues.txt`, "state after permutation"
of the second application (input = Vector 1's output). -/

private def secondOut : List.Vector (BitVec 64) 25 :=
  ⟨[0x2d5c954df96ecb3c#64, 0x6a332cd07057b56d#64, 0x093d8d1270d76b6c#64,
    0x8a20d9b25569d094#64, 0x4f9c4f99e5e7f156#64, 0xf957b9a2da65fb38#64,
    0x85773dae1275af0d#64, 0xfaf4f247c3d810f7#64, 0x1f1b9ee6f79a8759#64,
    0xe4fecc0fee98b425#64, 0x68ce61b6b9ce68a1#64, 0xdeea66c4ba8f974f#64,
    0x33c43d836eafb1f5#64, 0xe00654042719dbd9#64, 0x7cf8a9f009831265#64,
    0xfd5449a6bf174743#64, 0x97ddad33d8994b40#64, 0x48ead5fc5d0be774#64,
    0xe3b8c8ee55b7b03c#64, 0x91a0226e649e42e9#64, 0x900e3129e7badd7b#64,
    0x202a9ec5faa3cce8#64, 0x5b3402464e1c3db6#64, 0x609f4e62a44c1059#64,
    0x20d06cd26a8fbf5c#64], by decide⟩

theorem keccakF1600_second_correct :
    (keccakF1600State zerosOut).toList = secondOut.toList := by native_decide

end Tests.Keccak
