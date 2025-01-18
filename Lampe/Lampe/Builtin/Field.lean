import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
For a prime `p`, a field element `a : Fp p`, and a bit size `w : U 32`,
this builtin evaluates to `()` if and only if `a < 2^w`, i.e., it can be represented by `w` bits.
Otherwise, an exception is thrown.

In Noir, this builtin corresponds to `fn __assert_max_bit_size(self, bit_size: u32)` implemented for `Field`.
-/
def fApplyRangeConstraint := newPureBuiltin
  ⟨[CTp.field, (CTp.u 32)], CTp.unit⟩
  (fun h![a, w] => ⟨a.val < 2^w.toNat,
    fun _ => ()⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the number of bits of `p`.
We asdecomposeWithRadix `log p + 1 < 2^64`, i.e., `p`'s size can be represented by a uint of bit-size `64`.
Otherwise, this builtin throws an exception.

In Noir, this builtin corresponds to `fn modulus_num_bits() -> u64` implemented for `Field`.
-/
def fModNumBits := newPureBuiltin
  ⟨[CTp.field], (CTp.u 64)⟩
  (@fun p h![_] => ⟨numBits p.val < 2^64,
    fun _ => numBits p.val⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bits() -> [u1]` implemented for `Field`.
-/
def fModLeBits := newPureBuiltin
  ⟨[CTp.field], (CTp.slice (CTp.u 1))⟩
  (@fun p h![_] => ⟨True,
    fun _ => decomposeToRadix 2 p.val (by tauto)⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bits() -> [u1]` implemented for `Field`.
-/
def fModBeBits := newPureBuiltin
  ⟨[CTp.field], (CTp.slice (CTp.u 1))⟩
  (@fun p h![_] => ⟨True,
    fun _ => .reverse (decomposeToRadix 2 p.val (by tauto))⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the byte representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bytes() -> [u8]` implemented for `Field`.
-/
def fModLeBytes := newPureBuiltin
  ⟨[CTp.field], (CTp.slice (CTp.u 8))⟩
  (@fun p h![_] => ⟨True,
    fun _ => decomposeToRadix 256 p.val (by linarith)⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bytes() -> [u8]` implemented for `Field`.
-/
def fModBeBytes := newPureBuiltin
  ⟨[CTp.field], (CTp.slice (CTp.u 8))⟩
  (@fun p h![_] => ⟨True,
    fun _ => .reverse (decomposeToRadix 256 p.val (by linarith))⟩)

/--
Represents the builtin that converts a field element to an unsigned integer.
We assume that this conversion is done by truncating the field element when necessary.

In Noir, this builtin corresponds to `fn from_field(a: Field) -> T` implemented for uints of bit size `s`.
 -/
def uFromField := newGenericPureBuiltin
  (fun s => ⟨[CTp.field], (CTp.u s)⟩)
  (fun s h![f] => ⟨True,
    fun _ => BitVec.ofNat s f.val⟩)

example : (BitVec.ofNat 8 200).toInt = -56 := by rfl

/--
Represents the builtin that converts a field element to an integer.
We assume that this conversion is done by truncating the field element when necessary.

In Noir, this builtin corresponds to `fn from_field(a: Field) -> T` implemented for ints of bit size `s`.
-/
def iFromField := newGenericPureBuiltin
  (fun s => ⟨[CTp.field], (CTp.i s)⟩)
  (fun s h![f] => ⟨True,
    fun _ => BitVec.ofNat s f.val⟩)

/--
Specs are not clear.
- What happens when P < 2^s for u-s while converting (Fp p) to (U s)?

In Noir, this builtin corresponds to `fn as_field(self) -> Field` implemented for uints of bit size `s`.
-/
def uAsField := newGenericPureBuiltin
  (fun s => ⟨[CTp.u s], (CTp.field)⟩)
  (fun s h![a] => sorry)

/--
Specs are not clear.
- What happens when P < 2^s for i-s while (Fp p) to (I s)?

In Noir, this builtin corresponds to `fn as_field(self) -> Field` implemented for ints of bit size `s`.
-/
def iAsField := newGenericPureBuiltin
  (fun s => ⟨[CTp.i s], (CTp.field)⟩)
  (fun s h![a] => sorry)

end Lampe.Builtin
