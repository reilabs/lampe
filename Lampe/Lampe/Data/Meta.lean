import Lean
import Lampe.Data.HList

open Lean PrettyPrinter Delaborator

namespace Lampe

/-- Disable a delaborator unless an option is set to true. Used in Lampe to disable pretty printers
until they are stabilized. -/
def whenDelabOptionSet (name : Name) (f : DelabM α) : DelabM α := do
  if (← getOptions).getBool name then f else failure

/-- Apply a delaborator only on a fully applied function application. This prevents the delaborator
from firing on partial applications which could lead to annoying visibility issues for the user. -/
def whenFullyApplied (expr : Expr) (f : DelabM α) : DelabM α := do
  let numArgs := expr.getAppNumArgs
  let fType ← Meta.inferType expr.getAppFn
  let arity := fType.getNumHeadForalls
  let arity2 := fType.getNumHeadLambdas
  if numArgs == arity + arity2 then f else failure
