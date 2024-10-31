import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
For a prime `p`, a field element `a : Fp p`, and a bit size `w : U 32`,
this builtin evaluates to `()` if and only if `a < 2^w`, i.e., it can be represented by `w` bits.
Otherwise, an exception is thrown.

In Noir, this builtin corresponds to `fn __assert_max_bit_size(self, bit_size: u32)` implemented for `Field`.
-/
def fApplyRangeConstraint : Builtin := newBuiltin
  [.field, (.u 32)] .unit
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun _ _ => ())

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the number of bits of `p`.
We assume that `log p + 1 < 2^64`, i.e., `p`'s size can be represented by a uint of bit-size `64`.
Otherwise, this builtin throws an exception.

In Noir, this builtin corresponds to `fn modulus_num_bits() -> u64` implemented for `Field`.
-/
def fModNumBits : Builtin := newBuiltin
  [.field] (.u 64)
  (@fun p _ => numBits p.val < 2^64)
  (@fun p h![_] _ => numBits p.val)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bits() -> [u1]` implemented for `Field`.
-/
def fModLeBits : Builtin := newBuiltin
  [.field] (.slice (.u 1))
  (@fun p _ => True)
  (@fun p h![_] _ => withRadix 2 p.val (by tauto))

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bits() -> [u1]` implemented for `Field`.
-/
def fModBeBits : Builtin := newBuiltin
  [.field] (.slice (.u 1))
  (@fun p _ => True)
  (@fun p h![_] _ => .reverse (withRadix 2 p.val (by tauto)))

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the byte representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bytes() -> [u8]` implemented for `Field`.
-/
def fModLeBytes : Builtin := newBuiltin
  [.field] (.slice (.u 8))
  (@fun p _ => True)
  (@fun p h![_] _ => withRadix 256 p.val (by linarith))

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bytes() -> [u8]` implemented for `Field`.
-/
def fModBeBytes : Builtin := newBuiltin
  [.field] (.slice (.u 8))
  (@fun p _ => True)
  (@fun p h![_] _ => .reverse (withRadix 256 p.val (by linarith)))

/--
Represents the builtin that converts a field element to an unsigned integer.
We assume that this conversion is done by truncating the field element when necessary.

In Noir, this builtin corresponds to `fn from_field(a: Field) -> u32` implemented for uints of bit size `s`.
 -/
def uFromField {s : Nat} : Builtin := newBuiltin
  [.field] (.u s)
  (fun _ => True)
  (fun h![f] _ => BitVec.ofNat s f.val)

#eval (BitVec.ofNat 8 200).toInt -- ((200 as i8) as Field) == -56

/--
Represents the builtin that converts a field element to an integer.
We assume that this conversion is done by truncating the field element when necessary.

In Noir, this builtin corresponds to `fn from_field(a: Field) -> u32` implemented for ints of bit size `s`.
-/
def iFromField {s : Nat} : Builtin := newBuiltin
  [.field] (.i s)
  (fun _ => True)
  (fun h![f] _ => BitVec.ofNat s f.val)

/--
Specs are not clear.
- What happens when P < 2^s for while converting (Fp p) to (U s)?

In Noir, this builtin corresponds to `fn as_field(self) -> Field` implemented for uints of bit size `s`.
-/
def uAsField {s : Nat} : Builtin := newBuiltin
  [.u s] (.field)
  (fun _ => True)
  (fun h![a] _ => sorry)

/--
Specs are not clear.
- What happens when P < 2^s for while converting (Fp p) to (U s)?

In Noir, this builtin corresponds to `fn as_field(self) -> Field` implemented for uints of bit size `s`.
-/
def iAsField {s : Nat} : Builtin := newBuiltin
  [.i s] (.field)
  (fun _ => True)
  (fun h![a] _ => sorry)

end Lampe.Builtin
