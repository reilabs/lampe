import Mathlib
import Lampe.Tp
import Lampe.Data.HList
import Lampe.State
import Lampe.Builtin

namespace Lampe

abbrev Ident := String

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

inductive FunctionIdent : Type where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent
| trait : TraitMethodImplRef → FunctionIdent

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

inductive Expr (rep : Tp → Type): Tp → Type where
| lit : (tp : Tp) → Nat → Expr rep tp
| var : rep tp → Expr rep tp
| letIn : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| call : HList Kind.denote tyKinds → (argTypes : List Tp) → (res : Tp) → FunctionIdent → HList rep argTypes → Expr rep res
| ite : rep .bool → Expr rep a → Expr rep a → Expr rep a
| skip : Expr rep .unit
| loop : rep (.u s) → rep (.u s) → (rep (.u s) → Expr rep r) → Expr rep .unit

structure Function : Type _ where
  generics : List Kind
  inTps : HList Kind.denote generics → List Tp
  outTp : HList Kind.denote generics → Tp
  body : ∀ rep, (gs : HList Kind.denote generics) → HList rep (inTps gs) → Expr rep (outTp gs)

/-- Polymorphic identity -/
example : Function := {
  generics := [.type]
  inTps := fun h![x] => [x]
  outTp := fun h![x] => x
  body := fun _ h![_] h![x] => .var x
}

structure FunctionDecl where
name : Ident
fn : Function

structure Module where
decls : List FunctionDecl

structure Struct where
  name : String
  tyArgKinds : List Kind
  fieldTypes : HList Kind.denote tyArgKinds → List Tp

structure TraitImpl where
traitGenericKinds : List Kind
implGenericKinds : List Kind
traitGenerics : HList Kind.denote implGenericKinds → HList Kind.denote traitGenericKinds
constraints : HList Kind.denote implGenericKinds → List TraitImplRef
self : HList Kind.denote implGenericKinds → Tp
impl : HList Kind.denote implGenericKinds → List (Ident × Function)

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
