import Std.Data.HashMap

import Lampe.Syntax.Utils

namespace Lampe

open Lean
open Lampe

/-- Carries information on patterns that can be used for destructuring. -/
inductive Binder where
| variable (name : Lean.Ident)
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
  nextFresh : Nat
  /--
  Maps the (printed) syntax of a type annotation to the identifier its built term has been bound
  to, so that repeated annotations reuse one binding. See `makeNoirTypeShared`.
  -/
  sharedTypeCache : Std.HashMap String Lean.Ident := {}
  /--
  The bindings backing `sharedTypeCache`, in creation order. `wrapSharedTypeLets` emits these as
  `let`s around the finished term.
  -/
  sharedTypeLets : Array (Lean.Ident × TSyntax `term) := #[]

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
  StateT.run' a ⟨0, {}, #[]⟩

/--
The number of syntax nodes a type annotation must have before it is worth sharing via
`makeNoirTypeShared`. Small types (`u32`, generic parameters, …) are cheap to re-elaborate, and
`let`-binding them would only add noise.
-/
def sharedTypeThreshold : Nat := 16

/-- The number of nodes in a syntax tree, used as the size measure for `sharedTypeThreshold`. -/
private partial def syntaxWeight : Syntax → Nat
| .node _ _ args => args.foldl (fun acc s => acc + syntaxWeight s) 1
| _ => 1

/-- Whether the syntax contains a hole (`_`), whose elaboration is context-dependent and which
therefore can never be shared between use sites. -/
private partial def containsHole : Syntax → Bool
| s@(.node _ _ args) => s.isOfKind ``Lean.Parser.Term.hole || args.any containsHole
| _ => false

/--
Builds the term for the provided type annotation, sharing the result between identical
annotations within one run of the DSL monad.

Extracted code repeats the same (frequently enormous) type annotation on every call, builtin,
and reference that touches the type. Building the term anew for each occurrence makes the
generated definition — and its elaboration cost — grow with the number of occurrences rather
than the number of distinct types. Instead, the first occurrence of a sufficiently large type
binds its term to a fresh identifier (registered in the state; `wrapSharedTypeLets` later emits
the `let` for it), and every further occurrence elaborates to just that identifier. Since
`let`-bound variables are definitionally transparent, downstream elaboration and unification
treat the identifier exactly like the type it abbreviates.

Types below `sharedTypeThreshold`, and types whose built term contains a context-dependent hole
(`_`), fall back to plain `makeNoirType`.
-/
def makeNoirTypeShared [MonadDSL m] (stx : TSyntax `noir_type) : m (TSyntax `term) := do
  if syntaxWeight stx.raw < sharedTypeThreshold then
    makeNoirType stx
  else
    let key := toString stx.raw
    if let some ident := (←get).sharedTypeCache[key]? then
      return ident
    let t ← makeNoirType stx
    if containsHole t.raw then
      return t
    let ident ← modifyGet fun s =>
      let ident := mkIdent $ Name.mkSimple s!"#tp_{s.sharedTypeLets.size}"
      (ident, { s with
        sharedTypeCache := s.sharedTypeCache.insert key ident
        sharedTypeLets := s.sharedTypeLets.push (ident, t) })
    return ident

/--
Wraps `body` in `let`-bindings for every type shared (via `makeNoirTypeShared`) during the
current run of the DSL monad. Must be applied to the finished term before it leaves the run —
and, since the shared types may mention the definition's generic parameters, at a point that is
still under the generics' binders.
-/
def wrapSharedTypeLets [MonadDSL m] (body : TSyntax `term) : m (TSyntax `term) := do
  (←get).sharedTypeLets.foldrM (init := body) fun (ident, t) acc =>
    `(let $ident : Lampe.Tp := $t; $acc)

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
  args : Array (TSyntax `noir_expr)
  idents : Array Lean.Ident
  lastId : Nat

namespace Args

/-- Creates an empty set of arguments. -/
def empty : Args := ⟨#[], #[], 0⟩

/--
Returns a new `Args` container with the given expression `expr` associated with a unique identifier.

Returns the corresponding identifier along with the new `Args` container.
-/
def next (a : Args) (expr : TSyntax `noir_expr) : (Lean.Ident × Args) :=
  let ident := mkIdent $ Name.mkSimple $ "#arg_" ++ (toString a.lastId)
  (ident , ⟨a.args.push expr, a.idents.push ident, a.lastId + 1⟩)

def wrap [MonadDSL m] (a : Args) (argVals : Array (TSyntax `term)) (expr : TSyntax `term)
  : m (TSyntax `term) := do
  if argVals.isEmpty then
    `($expr)
  else
    `((fun args => match args with | $(←makeHListLit (a.idents.map fun i => (i : TSyntax `term))) => $expr) $(←makeHListLit argVals))

end Args

instance : Inhabited Args where
  default := Args.empty

/-- An LValue reference, namely the value that `modifyLens` should be called with. -/
inductive LValueRef where
/-- The source is a mutable let binding, already represented as a reference. -/
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
| `(noir_lval|($vectorExpr [[ $_ ]] : $_)) => getLValueRef vectorExpr
| `(noir_lval|$id:ident) => pure $ .ident id
| l => throwError "Encountered invalid lvalue reference {l}"
