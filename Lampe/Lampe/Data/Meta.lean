import Lean

open Lean PrettyPrinter Delaborator

def whenDelabOptionSet (name : Name) (f : DelabM α) : DelabM α := do
  if (← getOptions).getBool name true then f else failure

def whenFullyApplied (expr : Expr) (f : DelabM α) : DelabM α := do
  let numArgs := expr.getAppNumArgs
  let fType ← Meta.inferType expr.getAppFn
  let arity := fType.getNumHeadForalls
  let arity2 := fType.getNumHeadLambdas
  if numArgs == arity + arity2 then f else failure

