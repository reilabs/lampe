import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the addition of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a + b`.

In Noir, this builtin corresponds to `a + b` for bigints `a`, `b`.
-/
def bigIntAdd : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a + b)

/--
Defines the subtraction of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a - b`.

In Noir, this builtin corresponds to `a - b` for bigints `a`, `b`.
-/
def bigIntSub : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a - b)

/--
Defines the multiplication of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a * b`.

In Noir, this builtin corresponds to `a * b` for bigints `a`, `b`.
-/
def bigIntMul : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a * b)

/--
Defines the division of two bigints `(a b : Tp.denote Tp.bi)`.
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
Defines the conversion of `a : Tp.denote .bi` to its byte slice representation `l : Tp.denote _ (.slice (.u 8))` in little-endian encoding.
Note that `l` always contains 32 elements. Hence, for integers that can be represented by less than 32 bytes, the higher bytes are set to zero.

We make the following assumptions:
- If `a` cannot be represented by 32 bytes, an exception is thrown
- Else, the builtin returns `l`.

In Noir, this builtin corresponds to `fn to_le_bytes(self) -> [u8; 32]` implemented for `BigInt`.
-/
def bigIntToLeBytes : Builtin := newBuiltin
  [.bi] (.slice (.u 8))
  (fun h![a] => canContain 256 a)
  (fun h![a] _ => chunksOf (BitVec.ofInt 256 a) 8 (by linarith))

end Lampe.Builtin
