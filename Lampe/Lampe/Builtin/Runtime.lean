import Lampe.Builtin.Basic

namespace Lampe.Builtin

/--
Returns whether the execution is performed in an unconstrained context.

Note we always return false, as otherwise we would be unable to reason about the code.
-/
def isUnconstrained := newTotalPureBuiltin
  ([], .bool)
  (fun _ => false)

/--
Noir's `#[builtin(assert_constant)]` compiler hint.

Semantically a no-op: takes any value of any type and returns `unit`.
The Noir compiler uses this to mark values that must be constant at
proof-generation time; the Lampe model ignores the runtime hint.
-/
def assertConstant := newGenericTotalPureBuiltin
  (fun (tp : Tp) => ⟨[tp], .unit⟩)
  (fun _ _ => ())

