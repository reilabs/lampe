import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the function that evaluates to an array's length `n`.
This builtin evaluates to an `U 32`. Hence, we assume that `n < 2^32`.

In Noir, this corresponds to `fn len(self) -> u32` implemented for `[_; n]`.
-/
def arrayLen {tp : Tp} {n : U 32} : Builtin := newPureBuiltin
  [(.array tp n)] (.u 32)
  (fun _ => True)
  (fun _ _ => n)

/--
Defines the function that converts an array to a slice.

In Noir, this corresponds to `fn as_slice(self) -> [T]` implemented for `[T; n]`.
-/
def arrayAsSlice {tp : Tp} {n : U 32}: Builtin := newPureBuiltin
  [(.array tp n)] (.slice tp)
  (fun _ => True)
  (fun h![a] _ => a.toList)

end Lampe.Builtin
