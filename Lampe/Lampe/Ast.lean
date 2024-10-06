import Mathlib
import Lampe.Tp
import Lampe.Data.HList
import Lampe.State

namespace Lampe

abbrev Ident := String

abbrev BuiltinOmni := ∀(P:Prime),
    State P →
    (argTps : List Tp) →
    (outTp : Tp) →
    HList (Tp.denote P) argTps →
    (Option (State P × Tp.denote P outTp) → Prop) →
    Prop

-- def omni_conseq (omni : BuiltinOmni) {P st atps otp args Q Q'}: Prop :=


structure Builtin where
  bigStep: ∀(P:Prime),
    State P →
    (args: List Tp) →
    (out: Tp) →
    HList (Tp.denote P) args →
    Option (State P × Tp.denote P out) →
    Prop
  omni: ∀(P:Prime),
    State P →
    (argTps : List Tp) →
    (outTp : Tp) →
    HList (Tp.denote P) argTps →
    (Option (State P × Tp.denote P outTp) → Prop) →
    Prop
  -- omni_conseq {P st atps otp args Q Q'}: omni P st atps otp args Q → (∀ r, Q r → Q' r) → omni P st atps otp args Q'
  -- omni_frame:
  --   Omni p Γ st₁ e Q →
  --   st₁.Disjoint st₂ →
  --   Omni p Γ (st₁ ∪ st₂) e (fun st => match st with
  --     | some (st', v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st'
  --     | none => Q none
  --   )




inductive FunctionIdent : Type where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

inductive Expr (rep : Tp → Type): Tp → Type where
| lit : (tp : Tp) → Nat → Expr rep tp
| var : rep tp → Expr rep tp
| letIn : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| seq : Expr rep _ → Expr rep t → Expr rep t
| call : HList Kind.denote tyKinds → (argTypes : List Tp) → (res : Tp) → FunctionIdent → HList rep argTypes → Expr rep res
| struct {fieldTps}: HList (Expr rep) fieldTps → Expr rep (Tp.struct fieldTps)
| proj : (mem : Member tp fieldTps) → Expr rep (Tp.struct fieldTps) → Expr rep tp
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

structure Struct where
  name : String
  tyArgKinds : List Kind
  fieldTypes : HList Kind.denote tyArgKinds → List Tp

@[reducible]
def Struct.tp (s: Struct): HList Kind.denote s.tyArgKinds → Tp :=
  fun tyArgs => .struct $ s.fieldTypes tyArgs

@[reducible]
def Struct.constructor (s: Struct):
  (tyArgs: HList Kind.denote s.tyArgKinds) →
  HList (Expr rep) (s.fieldTypes tyArgs) →
  Expr rep (s.tp tyArgs) :=
  fun _ fieldExprs => .struct fieldExprs

end Lampe
