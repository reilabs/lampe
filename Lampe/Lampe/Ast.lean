import Mathlib

import Lampe.Tp
import Lampe.Data.HList
import Lampe.SeparationLogic.ValHeap
import Lampe.Builtin.Basic

namespace Lampe

abbrev Ident := String

/-- A reference to a lambda is represented as a reference to a unit type -/
abbrev Tp.lambdaRef := Tp.ref .unit

structure TraitRef where
  name : Ident
  traitGenericKinds : List Kind
  traitGenerics : HList Kind.denote traitGenericKinds

structure TraitImplRef where
  trait : TraitRef
  self : Tp

structure TraitMethodImplRef where
  trait : TraitImplRef
  method : Ident

inductive FunctionIdent (rep : Tp → Type) : Type where
| builtin : Builtin → FunctionIdent rep
| decl : Ident → FunctionIdent rep
| lambda : rep .lambdaRef → FunctionIdent rep
| trait : TraitMethodImplRef → FunctionIdent rep

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

inductive Expr (rep : Tp → Type) : Tp → Type where
| lit : (tp : Tp) → Nat → Expr rep tp
| var : rep tp → Expr rep tp
| letIn : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| call : HList Kind.denote tyKinds → (argTypes : List Tp) → (res : Tp) → FunctionIdent rep → HList rep argTypes → Expr rep res
| ite : rep .bool → Expr rep a → Expr rep a → Expr rep a
| skip : Expr rep .unit
| loop : rep (.u s) → rep (.u s) → (rep (.u s) → Expr rep r) → Expr rep .unit
| lambda : (argTps : List Tp) → (outTp : Tp) → (HList rep argTps → Expr rep outTp) → Expr rep .lambdaRef
| struct : (name : String) → (fieldTps : List Tp) → (fieldArgs : HList rep fieldTps) → Expr rep (.tuple (some name) fieldTps)

structure Lambda (rep : Tp → Type) where
  argTps : List Tp
  outTp : Tp
  body : HList rep argTps → Expr rep outTp

structure Function : Type _ where
  generics : List Kind
  body : ∀ (rep : Tp → Type), (HList Kind.denote generics) → Lambda rep

/-- Polymorphic identity -/
example : Function := {
  generics := [.type]
  body := fun _ h![tp] => ⟨[tp], tp, fun h![x] => .var x⟩
}

structure FunctionDecl where
  name : Ident
  fn : Function

structure Module where
  decls : List FunctionDecl

structure Struct where
  name : String
  genericKinds : List Kind
  fieldTypes : HList Kind.denote genericKinds → List Tp

structure TraitImpl where
  traitGenericKinds : List Kind
  implGenericKinds : List Kind
  traitGenerics : HList Kind.denote implGenericKinds → HList Kind.denote traitGenericKinds
  constraints : HList Kind.denote implGenericKinds → List TraitImplRef
  self : HList Kind.denote implGenericKinds → Tp
  impl : HList Kind.denote implGenericKinds → List (Ident × Function)

@[reducible]
def Struct.tp (s: Struct) : HList Kind.denote s.genericKinds → Tp :=
  fun generics => .tuple (some s.name) $ s.fieldTypes generics

@[reducible]
def Struct.constructor (s: Struct) :
  (generics : HList Kind.denote s.genericKinds) →
  HList rep (s.fieldTypes generics) →
  Expr rep (s.tp generics) :=
  fun generics fieldExprs => .struct s.name (s.fieldTypes generics) fieldExprs

end Lampe
