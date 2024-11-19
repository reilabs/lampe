import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Mathlib
import Lampe.State


namespace Lampe

variable (P : Prime)

structure Env where
  functions : List (Ident × Function)
  traits : List (Ident × TraitImpl)

inductive TraitResolvable (Γ : Env): TraitImplRef → Prop where
| ok {ref impl}:
  (ref.trait.name, impl) ∈ Γ.traits →
  (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds) →
  (implGenerics : HList Kind.denote impl.implGenericKinds) →
  (ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics) →
  ref.self = impl.self implGenerics →
  (∀constraint ∈ impl.constraints implGenerics, TraitResolvable Γ constraint) →
  TraitResolvable Γ ref

inductive TraitResolution (Γ : Env): TraitImplRef → List (Ident × Function) → Prop where
| ok {ref impl}:
  (ref.trait.name, impl) ∈ Γ.traits →
  (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds) →
  (implGenerics : HList Kind.denote impl.implGenericKinds) →
  (ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics) →
  ref.self = impl.self implGenerics →
  (∀constraint ∈ impl.constraints implGenerics, TraitResolvable Γ constraint) →
  TraitResolution Γ ref (impl.impl implGenerics)

inductive Omni : Env → State P → Expr (Tp.denote P) tp → (Option (State P × tp.denote P) → Prop) → Prop where
| litField : Q (some (st, n)) → Omni Γ st (.lit .field n) Q
| litFalse : Q (some (st, false)) → Omni Γ st (.lit .bool 0) Q
| litTrue : Q (some (st, true)) → Omni Γ st (.lit .bool 1) Q
| litU {Q} : Q (some (st, ↑n)) → Omni Γ st (.lit (.u s) n) Q
| var : Q (some (st, v)) → Omni Γ st (.var v) Q
| skip : Q (some (st, ())) → Omni Γ st (.skip) Q
| iteTrue {mainBranch elseBranch} :
  Omni Γ st mainBranch Q →
  Omni Γ st (Expr.ite true mainBranch elseBranch) Q
| iteFalse {mainBranch elseBranch} :
  Omni Γ st elseBranch Q →
  Omni Γ st (Expr.ite false mainBranch elseBranch) Q
| letIn :
    Omni Γ st e Q₁ →
    (∀v s, Q₁ (some (s, v)) → Omni Γ s (b v) Q) →
    (Q₁ none → Q none) →
    Omni Γ st (.letIn e b) Q
| callBuiltin {Q} :
    (b.omni P st argTypes resType args Q) →
    Omni Γ st (Expr.call h![] argTypes resType (.builtin b) args) Q
| callDecl:
    (fname, fn) ∈ Γ.functions →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    Omni Γ st (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ args)) Q →
    Omni Γ st (@Expr.call _ tyKinds generics argTypes res (.decl fname) args) Q
| callTrait {impl}:
    TraitResolution Γ traitRef impl →
    (fname, fn) ∈ impl →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    Omni Γ st (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ args)) Q →
    Omni Γ st (@Expr.call _ tyKinds generics argTypes res (.trait ⟨traitRef, fname⟩) args) Q
| loopDone :
    lo ≥ hi →
    Omni Γ st (.loop lo hi body) Q
| loopNext {s} {lo hi : U s} {body} :
    lo < hi →
    Omni Γ st (.letIn (body lo) (fun _ => .loop (lo + 1) hi body)) Q →
    Omni Γ st (.loop lo hi body) Q

theorem Omni.consequence {p Γ st tp} {e : Expr (Tp.denote p) tp} {Q Q'}:
    Omni p Γ st e Q →
    (∀ v, Q v → Q' v) →
    Omni p Γ st e Q' := by
  intro h
  induction h <;> try (
    intro
    constructor
    all_goals tauto
  )
  case callBuiltin =>
    cases_type Builtin
    tauto
  case loopNext =>
    intro
    apply loopNext (by assumption)
    tauto

theorem Omni.frame {p Γ tp st₁ st₂} {e : Expr (Tp.denote p) tp} {Q}:
    Omni p Γ st₁ e Q →
    st₁.Disjoint st₂ →
    Omni p Γ (st₁ ∪ st₂) e (fun st => match st with
      | some (st', v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st'
      | none => Q none
    ) := by
  intro h
  induction h with
  | litField hq
  | skip
  | litFalse hq
  | litTrue hq
  | litU _
  | var hq =>
    intro
    constructor
    repeat apply Exists.intro
    tauto
  | letIn _ _ hN ihE ihB =>
    intro
    constructor
    apply ihE
    assumption
    · intro _ _ h
      cases h
      casesm* ∃ _, _, _∧_
      subst_vars
      apply ihB
      assumption
      assumption
    · simp_all
  | callBuiltin hq =>
    cases_type Builtin
    tauto
  | callDecl _ _ _ _ _ ih =>
    intro
    constructor
    all_goals (try assumption)
    tauto
  | callTrait _ _ _ _ _ _ ih =>
    intro
    constructor
    all_goals (try assumption)
    tauto
  | loopDone =>
    intro
    constructor
    assumption
  | loopNext =>
    intro
    apply loopNext (by assumption)
    tauto
  | iteTrue _ ih
  | iteFalse _ ih =>
    intro
    constructor
    apply ih
    assumption

end Lampe
