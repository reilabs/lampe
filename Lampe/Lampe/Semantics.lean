import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.SeparationLogic.State

namespace Lampe

variable (p : Prime)

structure Env where
  functions : List (Ident × Function)
  traits : List (Ident × TraitImpl)

inductive TraitResolvable (Γ : Env) : TraitImplRef → Prop where
| ok {ref impl} :
  (ref.trait.name, impl) ∈ Γ.traits →
  (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds) →
  (implGenerics : HList Kind.denote impl.implGenericKinds) →
  (ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics) →
  ref.self = impl.self implGenerics →
  (∀constraint ∈ impl.constraints implGenerics, TraitResolvable Γ constraint) →
  TraitResolvable Γ ref

inductive TraitResolution (Γ : Env) : TraitImplRef → List (Ident × Function) → Prop where
| ok {ref impl}
  (h_mem : (ref.trait.name, impl) ∈ Γ.traits)
  (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds)
  (implGenerics : HList Kind.denote impl.implGenericKinds)
  (_ : ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics)
  (_ : ref.self = impl.self implGenerics)
  (_ : ∀constraint ∈ impl.constraints implGenerics, TraitResolvable Γ constraint) :
  TraitResolution Γ ref (impl.impl implGenerics)

inductive Omni : Env → State p → Expr (Tp.denote p) tp → (Option (State p × Tp.denote p tp) → Prop) → Prop where
| litField {Q} : Q (some (st, n)) → Omni Γ st (.litNum .field n) Q
| litStr {Q} : Q (some (st, ns)) → Omni Γ st (.litStr u ns) Q
| fmtStr {Q} : Q (some (st, ns)) → Omni Γ st (.fmtStr _ _ ns) Q
| litFalse {Q} : Q (some (st, false)) → Omni Γ st (.litNum .bool 0) Q
| litTrue {Q} : Q (some (st, true)) → Omni Γ st (.litNum .bool 1) Q
| litU {Q} : Q (some (st, ↑n)) → Omni Γ st (.litNum (.u s) n) Q
| litUnit {Q} : Q (some (st, ())) → Omni Γ st (.litNum .unit n) Q
| fn {Q} : Q (some (st, r)) → Omni Γ st (.fn _ _ r) Q
| var {Q} : Q (some (st, v)) → Omni Γ st (.var v) Q
| skip {Q} : Q (some (st, ())) → Omni Γ st (.skip) Q
| iteTrue {mainBranch elseBranch} :
  Omni Γ st mainBranch Q →
  Omni Γ st (Expr.ite true mainBranch elseBranch) Q
| iteFalse {mainBranch elseBranch} :
  Omni Γ st elseBranch Q →
  Omni Γ st (Expr.ite false mainBranch elseBranch) Q
| letIn :
  Omni Γ st e Q₁ →
  (∀v st, Q₁ (some (st, v)) → Omni Γ st (b v) Q) →
  (Q₁ none → Q none) →
  Omni Γ st (.letIn e b) Q
| callTrait {fnRef} :
  fnRef = (.trait selfTp traitName traitKinds traitGenerics fnName kinds generics) →
  TraitResolution Γ ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls →
  (fnName, fn) ∈ impls →
  (hkc : fn.generics = kinds) →
  (htci : (fn.body (Tp.denote p) (hkc ▸ generics) |>.argTps) = argTps) →
  (htco : (fn.body (Tp.denote p) (hkc ▸ generics) |>.outTp) = outTp) →
  Omni Γ ⟨vh, lambdas⟩ (htco ▸ (fn.body (Tp.denote p) (hkc ▸ generics) |>.body (htci ▸ args))) Q →
  Omni Γ ⟨vh, lambdas⟩ (Expr.call argTps outTp fnRef args) Q
| callLambda {fnRef} {lambdaBody : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp} :
  fnRef = (.lambda ref) →
  lambdas.lookup ref = some ⟨argTps, outTp, lambdaBody⟩ →
  Omni Γ ⟨vh, lambdas⟩ (lambdaBody args) Q →
  Omni Γ ⟨vh, lambdas⟩ (Expr.call argTps outTp fnRef args) Q
| callDecl {fnRef} :
  fnRef = (.decl fnName kinds generics) →
  (fnName, fn) ∈ Γ.functions →
  (hkc : fn.generics = kinds) →
  (htci : (fn.body (Tp.denote p) (hkc ▸ generics) |>.argTps) = argTps) →
  (htco : (fn.body (Tp.denote p) (hkc ▸ generics) |>.outTp) = outTp) →
  Omni Γ ⟨vh, lambdas⟩ (htco ▸ (fn.body (Tp.denote p) (hkc ▸ generics) |>.body (htci ▸ args))) Q →
  Omni Γ ⟨vh, lambdas⟩ (Expr.call argTps outTp fnRef args) Q
| lam {Q} :
  (∀ ref, ref ∉ lambdas → Q (some (⟨vh, lambdas.insert ref ⟨argTps, outTp, lambdaBody⟩⟩, FuncRef.lambda ref))) →
  Omni Γ ⟨vh, lambdas⟩ (Expr.lam argTps outTp lambdaBody) Q
| callBuiltin {Q} :
  (b.omni p st argTps outTp args (mapToValHeapCondition st.lambdas Q)) →
  Omni Γ st (Expr.callBuiltin argTps outTp b args) Q
| loopDone :
  lo ≥ hi →
  Omni Γ st (.loop lo hi body) Q
| loopNext {s} {lo hi : U s} {body} :
  lo < hi →
  Omni Γ st (.letIn (body lo) (fun _ => .loop (lo + 1) hi body)) Q →
  Omni Γ st (.loop lo hi body) Q

theorem Omni.consequence {p Γ st tp} {e : Expr (Tp.denote p) tp} {Q Q'} :
    Omni p Γ st e Q →
    (∀ v, Q v → Q' v) →
    Omni p Γ st e Q' := by
  intro h
  induction h with
  | callDecl =>
    intro
    apply Omni.callDecl <;> tauto
  | callLambda =>
    intro
    apply Omni.callLambda <;> tauto
  | callBuiltin =>
    cases_type Builtin
    intros
    constructor
    tauto
  | loopNext =>
    intro
    apply loopNext (by assumption)
    tauto
  | _ =>
    intro
    constructor
    all_goals tauto


theorem Omni.frame {p Γ tp} {st₁ st₂ : State p} {e : Expr (Tp.denote p) tp} {Q} :
    Omni p Γ st₁ e Q →
    LawfulHeap.disjoint st₁ st₂ →
    Omni p Γ (st₁ ∪ st₂) e (fun stv => match stv with
      | some (st', v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st'
      | none => Q none
    ) := by
  intro h
  induction h with
  | litField hq
  | litStr hq
  | litFalse hq
  | litTrue hq
  | litU hq
  | litUnit
  | fmtStr hq
  | skip hq
  | fn
  | var hq =>
    intro
    constructor
    simp only
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
  | callDecl =>
    intro
    apply Omni.callDecl <;> tauto
  | callTrait =>
    intro
    apply Omni.callTrait <;> tauto
  | callLambda h =>
    intro hd
    apply Omni.callLambda <;> try tauto
    simp_all
  | callBuiltin hq =>
    rename Builtin => b
    intros
    constructor
    simp only [State.union_closures, State.union_vals]
    rename_i _ st₁ _ _ _ _ hd
    have hf := b.frame hq (st₂ := st₂)
    unfold mapToValHeapCondition at *
    simp_all only [LawfulHeap.disjoint, true_implies]
    convert hf
    funext
    rename Option _ → Prop => Q'
    casesm Option (ValHeap _ × _) <;> try rfl
    simp_all only [SLP.star, eq_iff_iff]
    apply Iff.intro
    all_goals (
      intros hin
      obtain ⟨s₁, ⟨s₂, ⟨hin₁, hin₂, hin₃, hin₄⟩⟩⟩ := hin
    )
    . exists s₁, s₂
      simp only [LawfulHeap.disjoint] at *
      refine ⟨by tauto, ?_, ?_, by tauto⟩
      . simp only [State.union_parts] at hin₂
        injection hin₂
      . have hc : s₁.lambdas = st₁.lambdas := by
          obtain ⟨_, hd₂⟩ := hin₁
          rw [State.union_parts] at hin₂
          injection hin₂ with _ hu
          rw [State.mk.injEq] at hin₄
          obtain ⟨_, hin₀⟩ := hin₄
          rw [←hin₀] at hu
          obtain ⟨_, hd₁⟩ := hd
          rw [←hin₀] at hd₁
          rw [Finmap.union_cancel hd₁ hd₂] at hu
          tauto
        rw [←hc]
        tauto
    . exists ⟨s₁, st₁.lambdas⟩, ⟨s₂, st₂.lambdas⟩
      simp only [LawfulHeap.disjoint] at *
      refine ⟨by tauto, ?_, by tauto, ?_⟩
      . simp only [State.union_parts, State.mk.injEq]
        tauto
      . rw [hin₄]
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
    tauto
  | lam =>
    intros h
    simp only [LawfulHeap.disjoint, State.union_parts_left] at *
    obtain ⟨_, hd⟩ := h
    constructor
    intros
    simp only
    rename Lambdas _ => lmbs
    rename ValHeap _ => vh
    rename Ref => r
    generalize hL : (⟨_, _, _⟩ : Lambda _) = lambda
    have hi : r ∉ lmbs ∧ r ∉ st₂.lambdas := by aesop
    have hd₁ : Finmap.Disjoint lmbs (Finmap.singleton r lambda) := by
      apply Finmap.Disjoint.symm
      apply Finmap.singleton_disjoint_iff_not_mem.mpr
      tauto
    have hd₂ : Finmap.Disjoint (Finmap.singleton r lambda) st₂.lambdas := by
      apply Finmap.singleton_disjoint_iff_not_mem.mpr
      tauto
    exists ⟨vh, lmbs ∪ Finmap.singleton r lambda⟩, st₂
    refine ⟨?_, ?_, ?_, by tauto⟩
    . simp only [LawfulHeap.disjoint]
      refine ⟨by tauto, ?_⟩
      simp only [Finmap.disjoint_union_left]
      tauto
    . simp only [State.union_parts_left, State.mk.injEq]
      refine ⟨by tauto, ?_⟩
      simp only [Finmap.insert_eq_singleton_union]
      simp only [Finmap.union_comm_of_disjoint hd₁, Finmap.union_assoc]
    . simp [Finmap.union_comm_of_disjoint, Finmap.insert_eq_singleton_union]
      rename (∀ref ∉ lmbs, _) => hQ
      rw [hL] at hQ
      simp only [Finmap.insert_eq_singleton_union] at hQ
      rw [Finmap.union_comm_of_disjoint hd₁]
      tauto

end Lampe
