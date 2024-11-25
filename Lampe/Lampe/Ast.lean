import Mathlib

import Lampe.Tp
import Lampe.Data.HList
import Lampe.SeparationLogic.ValHeap
import Lampe.Builtin

namespace Lampe

abbrev Ident := String

/-- A reference to a lambda is represented as a reference to a unit type -/
abbrev Tp.lambdaRef := Tp.ref .unit

inductive FunctionIdent {rep : Tp → Type} : Type where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent -- a function declared at the module level
| lambda : rep .lambdaRef → FunctionIdent

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

inductive Expr (rep : Tp → Type) : Tp → Type where
| lit : (tp : Tp) → Nat → Expr rep tp
| var : rep tp → Expr rep tp
| letIn : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| call : HList Kind.denote tyKinds → (argTypes : List Tp) → (res : Tp) → @FunctionIdent rep → HList rep argTypes → Expr rep res
| ite : rep .bool → Expr rep a → Expr rep a → Expr rep a
| skip : Expr rep .unit
| loop : rep (.u s) → rep (.u s) → (rep (.u s) → Expr rep r) → Expr rep .unit
| lambda : (argTps : List Tp) → (outTp : Tp) → (HList rep argTps → Expr rep outTp) → Expr rep .lambdaRef

structure Function : Type _ where
  generics : List Kind
  inTps : HList Kind.denote generics → List Tp
  outTp : HList Kind.denote generics → Tp
  body : (rep : Tp → Type) → (gs : HList Kind.denote generics) →
    HList rep (inTps gs) →
    Expr rep (outTp gs)

/-- Polymorphic identity -/
example : Function := {
  generics := [.type]
  inTps := fun h![x] => [x]
  outTp := fun h![x] => x
  body := fun _ h![_] h![x] => .var x
}

structure Lambda where
  rep : Tp → Type
  argTps : List Tp
  outTp : Tp
  body : HList rep argTps → Expr rep outTp

structure FunctionDecl where
  name : Ident
  fn : Function

structure Module where
  decls : List FunctionDecl

structure Struct where
  name : String
  tyArgKinds : List Kind
  fieldTypes : HList Kind.denote tyArgKinds → List Tp

-- @[reducible]
-- def Struct.tp (s: Struct): HList Kind.denote s.tyArgKinds → Tp :=
--   fun tyArgs => .struct $ s.fieldTypes tyArgs

-- @[reducible]
-- def Struct.constructor (s: Struct):
--   (tyArgs: HList Kind.denote s.tyArgKinds) →
--   HList (Expr rep) (s.fieldTypes tyArgs) →
--   Expr rep (s.tp tyArgs) :=
--   fun _ fieldExprs => .struct fieldExprs

end Lampe
