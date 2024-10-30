import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/--
For a field element `a : Tp.denote p Tp.field` in `Fp p`, and a bit size `w : Tp.denote p (Tp.u 32)`,
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
For a field element `a : Tp.denote p Tp.field` in `Fp p`, and a bit size `w : Tp.denote p (Tp.u 32)`,
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
Assumption: a < rad^l is not enforced
Assumption: 1 < rad < 256
In Noir, this builtin corresponds to `fn __to_le_radix(self, radix: u32, result_len: u32) -> [u8]` implemented for `Field`.
-/
def fToLeRadix : Builtin := newBuiltin
  [(.field), (.u 32), (.u 32)] (.slice (.u 8))
  (fun h![_, rad, _] => 1 < rad ∧ rad < 256)
  (fun h![a, rad, l] _ => extList
    (withRadix rad.toNat a.val (by tauto)) l.toNat 0)

/--
Assumption: a < rad^l is not enforced
Assumption: 1 < rad < 256
In Noir, this builtin corresponds to `fn __to_be_radix(self, radix: u32, result_len: u32) -> [u8]` implemented for `Field`.
-/
def fToBeRadix : Builtin :=  newBuiltin
  [(.field), (.u 32), (.u 32)] (.slice (.u 8))
  (fun h![_, rad, _] => 1 < rad ∧ rad < 256)
  (fun h![a, rad, l] _ => .reverse (extList
    (withRadix rad.toNat a.val (by tauto)) l.toNat 0))

/--
Assumption: a < 2^w
In Noir, this builtin corresponds to `fn __assert_max_bit_size(self, bit_size: u32)` implemented for `Field`.
-/
def fApplyRangeConstraint : Builtin := newBuiltin
  [.field, (.u 32)] .unit
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun _ _ => ())

/--
Assumption: p < 2^64
In Noir, this builtin corresponds to `fn modulus_num_bits() -> u64` implemented for `Field`.
-/
def fModNumBits : Builtin := newBuiltin
  [.field] (.u 64)
  (@fun P _ => P.val < 2^64)
  (@fun P h![_] _ => numBits P.val)

/--

In Noir, this builtin corresponds to `fn modulus_le_bits() -> [u1]` implemented for `Field`.
-/
def fModLeBits : Builtin := newBuiltin
  [.field] (.slice (.u 1))
  (@fun p _ => True)
  (@fun p h![_] _ => withRadix 2 p.val (by tauto))

/--

In Noir, this builtin corresponds to `fn modulus_be_bits() -> [u1]` implemented for `Field`.
-/
def fModBeBits : Builtin := newBuiltin
  [.field] (.slice (.u 1))
  (@fun p _ => True)
  (@fun p h![_] _ => .reverse (withRadix 2 p.val (by tauto)))

/--

In Noir, this builtin corresponds to `fn modulus_le_bytes() -> [u8]` implemented for `Field`.
-/
def fModLeBytes : Builtin := newBuiltin
  [.field] (.slice (.u 8))
  (@fun p _ => True)
  (@fun p h![_] _ => withRadix 256 p.val (by linarith))

/--

In Noir, this builtin corresponds to `fn modulus_be_bytes() -> [u8]` implemented for `Field`.
-/
def fModBeBytes : Builtin := newBuiltin
  [.field] (.slice (.u 8))
  (@fun p _ => True)
  (@fun p h![_] _ => .reverse (withRadix 256 p.val (by linarith)))

/-- Specs are not clear. -/
def uFromField {s : Nat} : Builtin := newBuiltin
  [.field] (.u s)
  (fun _ => True)
  (fun h![f] _ => f.val)

/-- Specs are not clear. -/
def iFromField {s : Nat} : Builtin := newBuiltin
  [.field] (.i s)
  (fun _ => True)
  (fun h![f] _ => f.val)

/-- Specs are not clear. -/
def uAsField {s : Nat} : Builtin := newBuiltin
  [.u s] (.field)
  (fun _ => True)
  (fun h![a] _ => a.toNat)

/-- Specs are not clear. -/
def iAsField {s : Nat} : Builtin := newBuiltin
  [.i s] (.field)
  (fun _ => True)
  (fun h![a] _ => a.toInt)

end Lampe.Builtin
