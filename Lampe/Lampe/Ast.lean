import Mathlib
import Lampe.Tp
import Lampe.Data.HList

namespace Lampe

abbrev Ident := String

inductive Builtin : Type where
| add
| sub
| mul
| div
| eq
| assert
| not
| lt
| index
| cast
| modulusNumBits
| toLeBytes
| fresh

inductive FunctionIdent : Type where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent

inductive Expr (rep : Tp → Type): Tp → Type where
| lit : (tp : Tp) → Nat → Expr rep tp
| var : rep tp → Expr rep tp
| letIn : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| seq : Expr rep _ → Expr rep t → Expr rep t
| call : HList Kind.denote tyKinds → (argTypes : List Tp) → (res : Tp) → FunctionIdent → HList (Expr rep) argTypes → Expr rep res
| ite : Expr rep .bool → Expr rep a → Expr rep a → Expr rep a
| skip : Expr rep .unit
| loop : Expr rep (.u s) → Expr rep (.u s) → (rep (.u s) → Expr rep r) → Expr rep .unit

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

end Lampe
