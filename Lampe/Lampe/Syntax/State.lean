import Std.Data.HashMap

import Lampe.Syntax.Utils

namespace Lampe

open Lean
open Lampe

/-- Carries information on patterns that can be used for destructuring. -/
inductive Binder where
| variable (name : Lean.Ident)
| mutable (name : Lean.Ident)
| tuple (elems : List Binder)
| invalid

instance : Inhabited Binder where
  default := Binder.invalid

/-- A container for a lambda parameter, including both pattern and type. -/
structure LambdaParam where
  binder : Binder
  type : TSyntax `term

/-- The state for the desugaring process from the DSL syntax into native Lean/lampe constructs. -/
structure DSLState where
  autoDeref : Std.HashMap Name Bool
  nextFresh : Nat

/--
The monad under which the desugaring operations all operate.

In particular, it ensures that we are always carrying a DesugarState around in addition to the
functionality provided by MonadUtil.
-/
class MonadDSL (m : Type → Type) extends
  MonadUtil m,
  MonadStateOf DSLState m

/--
Make typeclass resolution not so stupid, and make sure that the type checker knows that this is the
right thing.
-/
@[default_instance]
instance
  [MonadUtil m]
  [MonadStateOf DSLState m]
: MonadDSL m where

instance [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] :
    MonadDSL (StateT DSLState m) where
  add x y := StateT.lift $ AddErrorMessageContext.add x y

/-- Runs the DSL monad beginning with an empty state. -/
def MonadDSL.run [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m]
    (a : StateT DSLState m α) : m α :=
  StateT.run' a ⟨Std.HashMap.emptyWithCapacity 1000, 0⟩

/-- Checks if the provided name `i` is subject to auto-dereferencing. -/
def isAutoDerefd [MonadDSL m] (i : Name) : m Bool := do -- FIXME name is temporary
  let st ← get
  pure $ st.autoDeref.getD i False

/-- Registers the provided name `i` for auto-dereferencing. -/
def regAutoDeref [MonadDSL m] (i : Name) : m Unit := do
  modify fun st => { st with autoDeref := st.autoDeref.insert i True }

/--
Retrieves the name if provided, or generates a fresh name if none is available.
-/
def nameOf [MonadDSL m] : Option Lean.Ident → m Lean.Ident
| none => modifyGet fun s =>
    (mkIdent (Name.mkSimple s!"#v_{s.nextFresh}"), { s with nextFresh := s.nextFresh + 1 })
| some n => pure n

/-- Wraps the provided ident in a let binding and then passes the let name to the continuation k. -/
def wrapInLet [MonadDSL m]
    (e : TSyntax `term)
    (ident : Option Lean.Ident)
    (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := do
  let ident ← nameOf ident
  match k with
  | some k => do
    let rest ← k ident
    ``(Expr.letIn $e fun $ident => $rest)
  | none => do
    pure e

/-- A container for arguments and the corresponding identifiers. -/
structure Args where
  args : List (TSyntax `noir_expr)
  idents : List Lean.Ident
  lastId : Nat

namespace Args

/-- Creates an empty set of arguments. -/
def empty : Args := ⟨[], [], 0⟩

/--
Returns a new `Args` container with the given expression `expr` associated with a unique identifier.

Returns the corresponding identifier along with the new `Args` container.
-/
def next (a : Args) (expr : TSyntax `noir_expr) : (Lean.Ident × Args) :=
  let ident := mkIdent $ Name.mkSimple $ "#arg_" ++ (toString a.lastId)
  (ident , ⟨expr :: a.args, ident :: a.idents, a.lastId + 1⟩)

def wrap [MonadDSL m] (a : Args) (argVals : List $ TSyntax `term) (expr : TSyntax `term)
  : m (TSyntax `term) := do
  if argVals.isEmpty then
    `($expr)
  else
    `((fun args => match args with | $(←makeHListLit a.idents) => $expr) $(←makeHListLit argVals))

end Args

instance : Inhabited Args where
  default := Args.empty

/-- An LValue reference, namely the value that `modifyLens` should be called with. -/
inductive LValueRef where
/-- The source is a mutable let binding. -/
| ident (id : TSyntax `ident)
/-- The source is the result of an expression which returns a reference. -/
| expr (expr : TSyntax `noir_expr)
/-- The LValue is malformed. -/
| none

instance : Inhabited LValueRef := ⟨.none⟩

/--
Generates an `LValRef` from the provided syntax tree `lVal`, or returns an error if it is malformed.

We consider two types of l-values:

1. Those whose "sources" are mutable let bindings, which is already represented as a reference and
   hence this reference can have `modifyLens` called directly on it.
2. Those whose "sources" are expressions that return a reference, in which case we need to evaluate
   the expression and call `modifyLens` on the result of the expression (which is a reference).
-/
partial def getLValueRef [MonadUtil m] (lVal : TSyntax `noir_lval) : m LValueRef := match lVal with
| `(noir_lval|(*$e:noir_expr : $_)) => do pure $ .expr e
| `(noir_lval|($dataExpr . $_ : $_)) => getLValueRef dataExpr
| `(noir_lval|($arrayExpr [ $_ ] : $_)) => getLValueRef arrayExpr
| `(noir_lval|($sliceExpr [[ $_ ]] : $_)) => getLValueRef sliceExpr
| `(noir_lval|$id:ident) => pure $ .ident id
| l => throwError "Encountered invalid lvalue reference {l}"

