import Lampe
import Lampe.Crypto.Blake2s

/-!
# BLAKE2s reference vector check

Validates `Lampe.Crypto.Blake2s.blake2sHashBytes` against canonical
RFC 7693 vectors (`empty`, `"abc"`) plus block-boundary edge cases.
Output bytes are anchored to Python's `hashlib.blake2s`, which wraps
the BLAKE2 reference implementation (`libb2`).

Inputs follow the canonical convention `input[i] = i % 251` for the
length-parametric cases. Lengths cover empty, the RFC `"abc"` vector,
exactly one full BLAKE2s block (64 bytes), and one byte past the
block boundary (65 bytes).

Regenerate with `scripts/gen/blake2s_ref.py`.
-/

namespace Tests.Blake2s

open Lampe.Crypto.Blake2s

-- BEGIN generated blake2s test vectors --
-- empty: RFC 7693 reference, input length = 0
private def emptyIn : Array (BitVec 8) :=
  #[]
private def emptyOut : Array (BitVec 8) :=
  #[0x69#8, 0x21#8, 0x7a#8, 0x30#8, 0x79#8, 0x90#8, 0x80#8, 0x94#8, 0xe1#8, 0x11#8, 0x21#8, 0xd0#8, 0x42#8, 0x35#8, 0x4a#8, 0x7c#8, 0x1f#8, 0x55#8, 0xb6#8, 0x48#8, 0x2c#8, 0xa1#8, 0xa5#8, 0x1e#8, 0x1b#8, 0x25#8, 0x0d#8, 0xfd#8, 0x1e#8, 0xd0#8, 0xee#8, 0xf9#8]
example : blake2sHashBytes emptyIn = emptyOut := by native_decide

-- abc: RFC 7693 reference, input length = 3
private def abcIn : Array (BitVec 8) :=
  #[0x61#8, 0x62#8, 0x63#8]
private def abcOut : Array (BitVec 8) :=
  #[0x50#8, 0x8c#8, 0x5e#8, 0x8c#8, 0x32#8, 0x7c#8, 0x14#8, 0xe2#8, 0xe1#8, 0xa7#8, 0x2b#8, 0xa3#8, 0x4e#8, 0xeb#8, 0x45#8, 0x2f#8, 0x37#8, 0x45#8, 0x8b#8, 0x20#8, 0x9e#8, 0xd6#8, 0x3a#8, 0x29#8, 0x4d#8, 0x99#8, 0x9b#8, 0x4c#8, 0x86#8, 0x67#8, 0x59#8, 0x82#8]
example : blake2sHashBytes abcIn = abcOut := by native_decide

-- oneBlock: exactly one full BLAKE2s message block, input length = 64
private def oneBlockIn : Array (BitVec 8) :=
  ((List.range 64).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def oneBlockOut : Array (BitVec 8) :=
  #[0x56#8, 0xf3#8, 0x4e#8, 0x8b#8, 0x96#8, 0x55#8, 0x7e#8, 0x90#8, 0xc1#8, 0xf2#8, 0x4b#8, 0x52#8, 0xd0#8, 0xc8#8, 0x9d#8, 0x51#8, 0x08#8, 0x6a#8, 0xcf#8, 0x1b#8, 0x00#8, 0xf6#8, 0x34#8, 0xcf#8, 0x1d#8, 0xde#8, 0x92#8, 0x33#8, 0xb8#8, 0xea#8, 0xaa#8, 0x3e#8]
example : blake2sHashBytes oneBlockIn = oneBlockOut := by native_decide

-- overBlock: one byte past block boundary (two compressions), input length = 65
private def overBlockIn : Array (BitVec 8) :=
  ((List.range 65).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def overBlockOut : Array (BitVec 8) :=
  #[0x1b#8, 0x53#8, 0xee#8, 0x94#8, 0xaa#8, 0xf3#8, 0x4e#8, 0x4b#8, 0x15#8, 0x9d#8, 0x48#8, 0xde#8, 0x35#8, 0x2c#8, 0x7f#8, 0x06#8, 0x61#8, 0xd0#8, 0xa4#8, 0x0e#8, 0xdf#8, 0xf9#8, 0x5a#8, 0x0b#8, 0x16#8, 0x39#8, 0xb4#8, 0x09#8, 0x0e#8, 0x97#8, 0x44#8, 0x72#8]
example : blake2sHashBytes overBlockIn = overBlockOut := by native_decide
-- END generated blake2s test vectors --

end Tests.Blake2s
