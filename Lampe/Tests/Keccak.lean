import Lampe
import Lampe.Crypto.Keccak

/-!
# Keccak-f[1600] reference test vectors

Five independent full-state inputs validated end-to-end against the
concrete `keccakF1600State` permutation via `native_decide`.

The first vector (all-zeros) is anchored against the Keccak team's
published intermediate-values reference
(https://keccak.team/files/Keccak-f-1600-IntermediateValues.txt);
matching it certifies the other four (generated via the Python
reference `scripts/keccak_ref.py` which is itself anchored against the
same canonical zeros vector).

This is Keccak-f[1600], the underlying permutation. It is identical
between FIPS 202 SHA-3 and Ethereum's keccak256 — the two differ only
in the sponge-layer padding byte (`0x06` vs `0x01`), which lives above
this function.
-/

namespace Tests.Keccak

open Lampe.Crypto.Keccak

/-! ### Vector 1: all-zeros (canonical anchor) -/

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

/-! ### Vector 2: lane 0 = 1, rest zero -/

private def oneBitIn : List.Vector (BitVec 64) 25 :=
  ⟨1 :: List.replicate 24 0, by decide⟩

private def oneBitOut : List.Vector (BitVec 64) 25 :=
  ⟨[0xe2a944396f0b13c6#64, 0x70fec06ceb0b06c4#64, 0x721dfc5018f27a42#64,
    0x64a2af57149f7096#64, 0xd3bc0b3f2712e2e6#64, 0x25b8444d0aea8b74#64,
    0x9396ef8130f1be5c#64, 0x87a98f12b6ad542c#64, 0x727078041f4f63f7#64,
    0x92cbec3174d6f74a#64, 0x23fbed32ed720767#64, 0xac2329d693b10d76#64,
    0x493d4a7a941b2026#64, 0x700069b797e2f86c#64, 0x95d8e3aee6fc4b8c#64,
    0x0bca1b8d9d0d82fc#64, 0xe2ad33926d474c63#64, 0x6a5415a4ebed8dfe#64,
    0xed6a86e4fecbac62#64, 0xd86e73c1b945a137#64, 0x333256c252840104#64,
    0x9f111faa6a08d2e5#64, 0x6d1f6a874f916feb#64, 0xf716ae69d3a57f06#64,
    0xf5a843755d5374af#64], by decide⟩

theorem keccakF1600_oneBit_correct :
    (keccakF1600State oneBitIn).toList = oneBitOut.toList := by native_decide

/-! ### Vector 3: ascending lane values 0..24 -/

private def ascendingIn : List.Vector (BitVec 64) 25 :=
  ⟨(List.range 25).map (fun i => BitVec.ofNat 64 i), by decide⟩

private def ascendingOut : List.Vector (BitVec 64) 25 :=
  ⟨[0x8374b05252ed8115#64, 0x1df7a676b6569400#64, 0xf765194b8a51797d#64,
    0x20477b43d1760545#64, 0xd15f8ba4f3f6606a#64, 0xa1d7144f7c8dd493#64,
    0x30d193965138fd3f#64, 0x487e9472951be3be#64, 0x0cf3a858cbda7a5a#64,
    0x2fe54e389bb17f88#64, 0x0b7338de0d9f268f#64, 0x55efdff58b256d7f#64,
    0xc8353e94eb2c3e6a#64, 0x2e2af6948c901f11#64, 0xe873de0cca309da6#64,
    0xf7afc26c944d31e2#64, 0xa0f5ea808cc415d7#64, 0x53f531437e3ed8cf#64,
    0x777f1f3b43a4d221#64, 0xfd0ca63cb499e985#64, 0xd4c055c0c5d12330#64,
    0xa72fe58aa6e0a7df#64, 0x421af5937c9948a3#64, 0x5e16103071340888#64,
    0xd153f43a297e4a33#64], by decide⟩

theorem keccakF1600_ascending_correct :
    (keccakF1600State ascendingIn).toList = ascendingOut.toList := by native_decide

/-! ### Vector 4: alternating 0xAA/0x55 with trailing 0xFF -/

private def alternatingIn : List.Vector (BitVec 64) 25 :=
  ⟨[0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64,
    0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64,
    0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64,
    0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64,
    0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64,
    0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64,
    0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64,
    0x5555555555555555#64, 0xaaaaaaaaaaaaaaaa#64, 0x5555555555555555#64,
    0xffffffffffffffff#64], by decide⟩

private def alternatingOut : List.Vector (BitVec 64) 25 :=
  ⟨[0xaedc706385f5d0e5#64, 0xbec2d885d5297e29#64, 0xf381522750633acb#64,
    0x74cb7df0ab89c91d#64, 0x571cb28d0d21c109#64, 0x97bbbf9e318584c5#64,
    0x894a1d9cb0c65e51#64, 0xb74b6c8bd1be49f1#64, 0x7f43b94191825889#64,
    0xa7e36af2debe5a35#64, 0xe9b5a26f3c1c2e7a#64, 0x72424e75c3cf9a53#64,
    0x64575b3483a50cf8#64, 0x3e2a4e932c74b593#64, 0xa9ba50d1a385278b#64,
    0xe15593bde24ad4b9#64, 0xf93cc9ee6e788181#64, 0x11ec6ea7ea5c27b6#64,
    0x5297886390f670db#64, 0xf086b6882dbbdbd3#64, 0x3c33c4e30c5ea45f#64,
    0x2ff579a6d63aabb3#64, 0xf5bdaa838c29f9af#64, 0x90e2b8e669e0c93f#64,
    0xdb4f44223bf98121#64], by decide⟩

theorem keccakF1600_alternating_correct :
    (keccakF1600State alternatingIn).toList = alternatingOut.toList := by native_decide

/-! ### Vector 5: all-ones (lanes = 2^64 - 1) -/

private def allOnesIn : List.Vector (BitVec 64) 25 :=
  ⟨List.replicate 25 0xffffffffffffffff#64, by decide⟩

private def allOnesOut : List.Vector (BitVec 64) 25 :=
  ⟨[0x9f00f21bba6817c4#64, 0xcdf5aa0d21af5e78#64, 0xd6539abf24095b97#64,
    0x8bb6f30a010f8228#64, 0xf0f711ba0547331d#64, 0x4f44330558eb182f#64,
    0x2213b79d9055207c#64, 0xeb5e5b55ca4fb490#64, 0x0bfaeb81a299b5d4#64,
    0x9e5d924f1a65ed48#64, 0x004650c533b7bfb3#64, 0xddad454b84d7ab05#64,
    0xf03ce56503e82921#64, 0xce442e92c6728660#64, 0x1a9ce5e4b37ddcd3#64,
    0xf63b60e27cea6f0e#64, 0xcc4cc7fca665bfad#64, 0x40cf4eba54a2285d#64,
    0x2725f1f142304213#64, 0x554d327de6fbad9b#64, 0x19866a26cbc8bdc2#64,
    0xe8c3c28faf02c7f5#64, 0xc6bc1f3512a665ae#64, 0xcaa831f1a5dc86ce#64,
    0x3f82afe91ca4b9b0#64], by decide⟩

theorem keccakF1600_allOnes_correct :
    (keccakF1600State allOnesIn).toList = allOnesOut.toList := by native_decide

end Tests.Keccak
