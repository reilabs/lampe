import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the builtin array constructor.
-/
def mkArray (n : U 32) := newGenericPureBuiltin
  (fun (argTps, tp) => ⟨argTps, (.array tp n)⟩)
  (fun (argTps, tp) args => ⟨argTps = List.replicate n.toNat tp,
    fun h => HList.toVec args h⟩)

/--
Defines the indexing of a array `l : Array tp n` with `i : U 32`
We make the following assumptions:
- If `i < n`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T; n]` and `i: uint32`.
-/
def arrayIndex := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n, .u 32], tp⟩)
  (fun (_, n) h![l, i] => ⟨i.toNat < n.toNat,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/--
Defines the function that evaluates to an array's length `n`.
This builtin evaluates to an `U 32`. Hence, we assume that `n < 2^32`.

In Noir, this corresponds to `fn len(self) -> u32` implemented for `[_; n]`.
-/
def arrayLen := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n], .u 32⟩)
  (fun (_, _) h![a] => ⟨a.length < 2^32,
    fun _ => a.length⟩)

/--
Defines the function that converts an array to a slice.

In Noir, this corresponds to `fn as_slice(self) -> [T]` implemented for `[T; n]`.
-/
def arrayAsSlice := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n], .slice tp⟩)
  (fun (_, _) h![a] => ⟨True,
    fun _ => a.toList⟩)

end Lampe.Builtin
