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

/-- Helper function to build a `HList` literal from a list of elements -/
def mkHListLit [Monad m] [MonadQuotation m] : List (TSyntax `term) → m (TSyntax `term)
| [] => `(HList.nil)
| x :: xs => do
  let tail ← mkHListLit xs
  `(HList.cons $x $tail)

end Lampe

/-- Optionally matches on a `HList` literal, and returns the list of `Lean.Expr` elements -/
partial def Lean.Expr.hListLit? (e : Expr) : Option $ List Expr :=
  let rec loop (e : Expr) (acc : List Expr) :=
    if e.isAppOfArity' ``HList.nil 2 then
      some acc.reverse
    else if e.isAppOfArity' ``HList.cons 6 then
      loop e.appArg!' (e.appFn!'.appArg!' :: acc)
    else
      none
  loop e []
