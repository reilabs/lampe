import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

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
