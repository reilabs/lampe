import Lampe.Tp
import Lampe.Data.HList
import Lampe.SeparationLogic.ValHeap
import Lampe.Builtin.Basic

namespace Lampe

abbrev Ident := String

/--
Represents a reference to a trait.
Note that `TraitRef`s do not actually refer to a concrete value of, e.g., some `Trait` type.
We assume that the traits referred to by `TraitRef`s already exist, since we are only concerned with Noir programs that pass type-checking.
-/
structure TraitRef where
  name : Ident
  traitGenericKinds : List Kind
  traitGenerics : HList Kind.denote traitGenericKinds

/--
Represents a reference to a trait implementation `TraitImpl` stored in the environment `Env`.
-/
structure TraitImplRef where
  /-- The implemented trait. -/
  trait : TraitRef
  /-- The concrete type that implements the trait `trait`. -/
  self : CTp

/--
Represents a reference to a method in a particular trait implementation.
-/
structure TraitMethodImplRef where
  /-- The trait implementation -/
  impl : TraitImplRef
  /-- The name of the method in the implementation `impl` -/
  method : Ident

/--
Represents an expression.
-/
inductive Expr (rep : Tp → Type) : Tp → Type where
| litNum : (tp : Tp) → Nat → Expr rep tp
| litStr : (len : U 32) → List.Vector Char len.toNat → Expr rep (CTp.str len)
| fn : (argTps : List Tp) → (outTp : Tp) → (r : FuncRef argTps outTp) → Expr rep (CTp.fn argTps outTp)
| var : rep tp → Expr rep tp
| letIn : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| call : (argTps : List Tp) → (outTp : Tp) → (rep $ CTp.fn argTps outTp) → (args : HList rep argTps) → Expr rep outTp
| callBuiltin : (argTps : List Tp) → (outTp : Tp) → (b : Builtin) → (args : HList rep argTps) → Expr rep outTp
| ite : rep CTp.bool → Expr rep a → Expr rep a → Expr rep a
| skip : Expr rep CTp.unit
| loop : rep (CTp.u s) → rep (CTp.u s) → (rep (CTp.u s) → Expr rep r) → Expr rep CTp.unit
| lam : (argTps : List Tp) → (outTp : Tp) → (HList rep argTps → Expr rep outTp) → Expr rep (CTp.fn argTps outTp)

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
  fieldTypes : HList Kind.denote genericKinds → List CTp

structure TraitImpl where
  traitGenericKinds : List Kind
  implGenericKinds : List Kind
  traitGenerics : HList Kind.denote implGenericKinds → HList Kind.denote traitGenericKinds
  constraints : HList Kind.denote implGenericKinds → List TraitImplRef
  self : HList Kind.denote implGenericKinds → CTp
  impl : HList Kind.denote implGenericKinds → List (Ident × Function)

/--
Returns a constructor (over generic values) for the concrete type of a struct.
Note that structs are represented as named tuples.
-/
@[reducible]
def Struct.tp (s : Struct) : HList Kind.denote s.genericKinds → CTp :=
  fun generics => CTp.tuple (some s.name) $ s.fieldTypes generics

end Lampe
