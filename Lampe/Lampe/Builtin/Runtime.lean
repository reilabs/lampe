import Lampe.Builtin.Basic

namespace Lampe.Builtin

/--
Returns whether the execution is performed in an unconstrained context.

Note we always return false, as otherwise we would be unable to reason about the code.
-/
def isUnconstrained := newTotalPureBuiltin 
  ([], .bool)
  (fun _ => false)

