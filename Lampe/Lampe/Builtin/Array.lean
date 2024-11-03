import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the function that evaluates to an array's length `n`.
This builtin evaluates to an `U 32`. Hence, we assume that `n < 2^32`.

In Noir, this corresponds to `fn len(self) -> u32` implemented for `[_; n]`.
-/
def arrayLen : Builtin := newGenPureBuiltin
  (fun (tp, n) => [.array tp n])
  (fun _ => .u 32)
  (fun (_, _) h![a] => a.length < 2^32)
  (fun (_, _) h![a] _ => a.length)


/--
Defines the function that converts an array to a slice.

In Noir, this corresponds to `fn as_slice(self) -> [T]` implemented for `[T; n]`.
-/
def arrayAsSlice : Builtin := newGenPureBuiltin
  (fun (tp, n) => [.array tp n])
  (fun (tp, _) => .slice tp)
  (fun (_, _) _ => True)
  (fun (_, _) h![a] _ => a.toList)

end Lampe.Builtin
