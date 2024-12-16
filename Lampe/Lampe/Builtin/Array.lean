import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the builtin array constructor.
-/
def mkArray (n : Nat) := newGenericPureBuiltin
  (fun (argTps, tp) => ⟨argTps, (.array tp n)⟩)
  (fun (argTps, tp) args => ⟨argTps = List.replicate n tp ∧ n < 2^32,
    fun h => Mathlib.Vector.ofFn fun i => List.get (HList.toList args (by tauto)) (by
      have hn : BitVec.toNat (n := 32) ↑n = n := by
        simp_all
      rw [hn] at i
      convert i
      apply HList.toList_len_is_n
  )⟩)

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
