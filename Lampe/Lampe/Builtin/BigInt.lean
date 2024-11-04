import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the addition of two bigints `(a b : Int)`.
The builtin is assumed to return `a + b`.

In Noir, this builtin corresponds to `a + b` for bigints `a`, `b`.
-/
def bigIntAdd := newPureBuiltin
  ⟨[.bi, .bi], (.bi)⟩
  (fun h![a, b]  => ⟨True,
    fun _ => a + b⟩)

/--
Defines the subtraction of two bigints `(a b : Int)`.
The builtin is assumed to return `a - b`.

In Noir, this builtin corresponds to `a - b` for bigints `a`, `b`.
-/
def bigIntSub := newPureBuiltin
  ⟨[.bi, .bi], (.bi)⟩
  (fun h![a, b]  => ⟨True,
    fun _ => a - b⟩)

/--
Defines the multiplication of two bigints `(a b : Int)`.
The builtin is assumed to return `a * b`.

In Noir, this builtin corresponds to `a * b` for bigints `a`, `b`.
-/
def bigIntMul := newPureBuiltin
  ⟨[.bi, .bi], (.bi)⟩
  (fun h![a, b]  => ⟨True,
    fun _ => a * b⟩)

/--
Defines the division of two bigints `(a b : Int)`. We make the following assumptions:
- If `b = 0`, an exception is thrown.
- Otherwise, the builtin is assumed to return `a / b`.

In Noir, this builtin corresponds to `a / b` for bigints `a`, `b`.
-/
def bigIntDiv := newPureBuiltin
  ⟨[.bi, .bi], (.bi)⟩
  (fun h![a, b]  => ⟨b ≠ 0,
    fun _ => a / b⟩)

/--
Defines the conversion of a byte slice `bytes : List (U 8)` in little-endian encoding to a `BigInt`.
Modulus parameter is ignored.

In Noir, this builtin corresponds to `fn from_le_bytes(bytes: [u8], modulus: [u8])` implemented for `BigInt`.
 -/
def bigIntFromLeBytes : Builtin := newPureBuiltin
  ⟨[.slice (.u 8), .slice (.u 8)], .bi⟩
  (fun h![bs, _] => ⟨True,
    fun _ => composeFromRadix 256 (bs.map (fun u => u.toNat))⟩)

/--
Defines the conversion of `a : Int` to its byte slice representation `l : Array 32 (U 8)` in little-endian encoding.
For integers that can be represented by less than 32 bytes, the higher bytes of `l` are set to zero.

We make the following assumptions:
- If `a` cannot be represented by 32 bytes, an exception is thrown.
- Else, the builtin returns `l`.

In Noir, this builtin corresponds to `fn to_le_bytes(self) -> [u8; 32]` implemented for `BigInt`.
-/
def bigIntToLeBytes : Builtin := newPureBuiltin
  ⟨[.bi], (.array (.u 8) 32)⟩
  (fun h![a] => ⟨bitsCanRepresent 256 a, fun _ =>
    let l := (decomposeToRadix 256 a.toNat (by linarith))
    Mathlib.Vector.ofFn (fun i =>
      if h: i.val < l.length then
        l.get (Fin.mk i.val h)
      else 0 -- higher bytes are set to zero
    )⟩)

end Lampe.Builtin