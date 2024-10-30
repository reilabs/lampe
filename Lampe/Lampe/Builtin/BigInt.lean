import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the addition of two bigints `(a b : Int)`.
The builtin is assumed to return `a + b`.

In Noir, this builtin corresponds to `a + b` for bigints `a`, `b`.
-/
def bigIntAdd : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a + b)

/--
Defines the subtraction of two bigints `(a b : Int)`.
The builtin is assumed to return `a - b`.

In Noir, this builtin corresponds to `a - b` for bigints `a`, `b`.
-/
def bigIntSub : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a - b)

/--
Defines the multiplication of two bigints `(a b : Int)`.
The builtin is assumed to return `a * b`.

In Noir, this builtin corresponds to `a * b` for bigints `a`, `b`.
-/
def bigIntMul : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a * b)

/--
Defines the division of two bigints `(a b : Int)`.
The builtin is assumed to return `a / b`.

In Noir, this builtin corresponds to `a / b` for bigints `a`, `b`.
-/
def bigIntDiv : Builtin := newBuiltin
  [.bi, .bi] .bi
  (fun _ => True)
  (fun h![a, b] _  => a / b)

/-- Not implemented yet.

In Noir, this builtin corresponds to `fn from_le_bytes(bytes: [u8], modulus: [u8])` implemented for `BigInt`.
 -/
def bigIntFromLeBytes : Builtin := newBuiltin
  [.slice (.u 8), .slice (.u 8)] .bi
  (fun _ => True)
  (fun h![bs, m] _ => sorry)

/--
Defines the conversion of `a : Int` to its byte slice representation `l : Array 32 (U 8)` in little-endian encoding.
For integers that can be represented by less than 32 bytes, the higher bytes of `l` are set to zero.

We make the following assumptions:
- If `a` cannot be represented by 32 bytes, an exception is thrown
- Else, the builtin returns `l`.

In Noir, this builtin corresponds to `fn to_le_bytes(self) -> [u8; 32]` implemented for `BigInt`.
-/
def bigIntToLeBytes : Builtin := newBuiltin
  [.bi] (.array (.u 8) 32)
  (fun h![a] => canContain 256 a)
  (fun h![a] _ => Array.mk (extList (withRadix 256 a.toNat (by linarith)) 32 0))

end Lampe.Builtin
