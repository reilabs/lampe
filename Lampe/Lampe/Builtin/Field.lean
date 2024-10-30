import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/--
For a field element `a : Fp p` ∈ `Fp p`, and a bit size `w : U 32`,
we assume the following:
- If `a < 2^w`, then this builtin evaluates to a list of 1-bit uints `l`, which is the little-endian bit representation of `a`.
Note that `l` is padded up to `w` elements with `0`.
- Otherwise, an exception is thrown.

In Noir, this builtin corresponds to ` fn __to_le_bits(self, bit_size: u32) -> [u1]` implemented for `Field`.
-/
def fToLeBits : Builtin := newBuiltin
  [(.field), (.u 32)] (.slice (.u 1))
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun h![a, w] _ => extList
    (withRadix 2 a.val (by tauto)) (w.toNat) 0)

/--
For a prime `p`, a field element `a : Fp p`, and a bit size `w : U 32`,
we assume the following:
- If `a < 2^w`, then this builtin evaluates to a list of 1-bit uints `l`, which is the big-endian bit representation of `a`.
Note that `l` is padded down to `w` elements with `0`.
- Otherwise, an exception is thrown.

In Noir, this builtin corresponds to ` fn __to_be_bits(self, bit_size: u32) -> [u1]` implemented for `Field`.
-/
def fToBeBits : Builtin := newBuiltin
  [(.field), (.u 32)] (.slice (.u 1))
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun h![a, w] _ => .reverse (extList
    (withRadix 2 a.val (by tauto)) (w.toNat) 0))

/--
For a prime `p`, a field element `a : Fp p`, a radix `rad : U 32`, and an output length `w : U 32`,
this builtin evaluates to a list of `w` little-endian radix `rad` digits representing `a`.
We assume the following:
- `a < rad^w` is not enforced, so the output may be truncated.
- `1 < rad < 256` must hold, or this builtin throws an exception.
In Noir, this builtin corresponds to `fn __to_le_radix(self, radix: u32, result_len: u32) -> [u8]` implemented for `Field`.
-/
def fToLeRadix : Builtin := newBuiltin
  [(.field), (.u 32), (.u 32)] (.slice (.u 8))
  (fun h![_, rad, _] => 1 < rad ∧ rad < 256)
  (fun h![a, rad, w] _ => extList
    (withRadix rad.toNat a.val (by tauto)) w.toNat 0)

/--
For a prime `p`, a field element `a : Fp p`, a radix `rad : U 32`, and an output length `w : U 32`,
this builtin evaluates to a list of `w` big-endian radix `rad` digits representing `a`.
We assume the following:
- `a < rad^w` is not enforced, so the output may be truncated.
- `1 < rad < 256` must hold, or this builtin throws an exception.
In Noir, this builtin corresponds to `fn __to_be_radix(self, radix: u32, result_len: u32) -> [u8]` implemented for `Field`.
-/
def fToBeRadix : Builtin :=  newBuiltin
  [(.field), (.u 32), (.u 32)] (.slice (.u 8))
  (fun h![_, rad, _] => 1 < rad ∧ rad < 256)
  (fun h![a, rad, w] _ => .reverse (extList
    (withRadix rad.toNat a.val (by tauto)) w.toNat 0))

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
Specs are not clear.

In Noir, this builtin corresponds to `fn from_field(a: Field) -> u32` implemented for uints of bit size `s`.
 -/
def uFromField {s : Nat} : Builtin := newBuiltin
  [.field] (.u s)
  (fun _ => True)
  (fun h![f] _ => sorry)

/--
Specs are not clear.

In Noir, this builtin corresponds to `fn from_field(a: Field) -> u32` implemented for ints of bit size `s`.
-/
def iFromField {s : Nat} : Builtin := newBuiltin
  [.field] (.i s)
  (fun _ => True)
  (fun h![f] _ => sorry)

/--
Specs are not clear.

In Noir, this builtin corresponds to `fn as_field(self) -> Field` implemented for uints of bit size `s`.
-/
def uAsField {s : Nat} : Builtin := newBuiltin
  [.u s] (.field)
  (fun _ => True)
  (fun h![a] _ => sorry)

/--
Specs are not clear.

In Noir, this builtin corresponds to `fn as_field(self) -> Field` implemented for uints of bit size `s`.
-/
def iAsField {s : Nat} : Builtin := newBuiltin
  [.i s] (.field)
  (fun _ => True)
  (fun h![a] _ => sorry)

end Lampe.Builtin
