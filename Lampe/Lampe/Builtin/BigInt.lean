import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the conversion of a byte slice `bytes : List (U 8)` in little-endian encoding to a `BigInt`.
Modulus parameter is ignored.

In Noir, this builtin corresponds to `fn from_le_bytes(bytes: [u8], modulus: [u8])` implemented for `BigInt`.
 -/
def bigIntFromLeBytes := newPureBuiltin
  ⟨[.slice (.u 8), .slice (.u 8)], .bi⟩
  (fun h![bs, _] => ⟨True,
    fun _ => composeFromRadix 256 (bs.map (fun u => u.toNat))⟩)

/--
Converts a list `l` to a vector of size `n`s.
- If `n < l.length`, then the output is truncated from the end.
- If `n > l.length`, then the higher indices are populated with `zero`.
-/
def listToVec (l : List α) (zero : α) : Mathlib.Vector α n :=
  Mathlib.Vector.ofFn (fun (i : Fin n) =>
    if h: i.val < l.length then
      (l.get (Fin.mk i.val h))
    else zero)

/--
Defines the conversion of `a : Int` to its byte slice representation `l : Array 32 (U 8)` in little-endian encoding.
For integers that can be represented by less than 32 bytes, the higher bytes of `l` are set to zero.

We make the following assumptions:
- If `a` cannot be represented by 32 bytes, an exception is thrown.
- Else, the builtin returns `l`.

In Noir, this builtin corresponds to `fn to_le_bytes(self) -> [u8; 32]` implemented for `BigInt`.
-/
def bigIntToLeBytes := newPureBuiltin
  ⟨[.bi], (.array (.u 8) 32)⟩
  (fun h![a] => ⟨bitsCanRepresent 256 a, fun _ =>
    Builtin.listToVec (decomposeToRadix 256 a.toNat (by linarith)) 0
      |>.map (fun n => BitVec.ofNat 8 n)⟩)

end Lampe.Builtin
