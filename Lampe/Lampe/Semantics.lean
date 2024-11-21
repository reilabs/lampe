import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Mathlib
import Lampe.State

namespace Lampe

def Env := Ident → Option Function

def Env.ofModule (m : Module) : Env := fun i => (m.decls.find? fun d => d.name == i).map (·.fn)

@[reducible]
def Env.extend (Γ₁ : Env) (Γ₂ : Env) : Env := fun i => Γ₁ i <|> Γ₂ i

inductive Omni : (p : Prime) → Env → State p → Expr (Tp.denote p) tp → (Option (State p × Tp.denote p tp) → Prop) → Prop where
| litField {Q} : Q (some (st, n)) → Omni p Γ st (.lit .field n) Q
| litFalse {Q} : Q (some (st, false)) → Omni p Γ st (.lit .bool 0) Q
| litTrue {Q} : Q (some (st, true)) → Omni p Γ st (.lit .bool 1) Q
| litRef {Q} : Q (some (st, ⟨r⟩)) → Omni p Γ st (.lit (.ref tp) r) Q
| litU {Q} : Q (some (st, ↑n)) → Omni p Γ st (.lit (.u s) n) Q
| var {Q} : Q (some (st, v)) → Omni p Γ st (.var v) Q
| skip {Q} : Q (some (st, ())) → Omni p Γ st (.skip) Q
| iteTrue {mainBranch elseBranch} :
  Omni p Γ st mainBranch Q →
  Omni p Γ st (Expr.ite true mainBranch elseBranch) Q
| iteFalse {mainBranch elseBranch} :
  Omni p Γ st elseBranch Q →
  Omni p Γ st (Expr.ite false mainBranch elseBranch) Q
| letIn :
    Omni p Γ ⟨vh₁, cls⟩ e Q₁ →
    (∀v vh, Q₁ (some (⟨vh, cls⟩, v)) → Omni p Γ ⟨vh, cls⟩ (b v) Q) →
    (Q₁ none → Q none) →
    Omni p Γ ⟨vh₁, cls⟩ (.letIn e b) Q
| callBuiltin {Q} {vh₁ cls} :
    (b.omni p vh₁ argTypes resType args (mapToValHeapCondition Q cls)) →
    Omni p Γ ⟨vh₁, cls⟩ (Expr.call h![] argTypes resType (.builtin b) args) Q
| callDecl :
    Γ fname = some fn →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    Omni p Γ st (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ args)) Q →
    Omni p Γ st (@Expr.call _ tyKinds generics argTypes res (.decl fname) args) Q
| callLambda {cls : Closures} :
  cls.get? lambdaRef.val = some fn →
  (hg : fn.generics = []) →
  (hi : fn.inTps (hg ▸ h![]) = argTps) →
  (ho : fn.outTp (hg ▸ h![]) = outTp) →
  Omni p Γ st (ho ▸ fn.body _ (hg ▸ h![]) (hi ▸ args)) Q →
  Omni p Γ st (Expr.call h![] argTps outTp (.lambda lambdaRef) args) Q
| loopDone :
    lo ≥ hi →
    Omni p Γ st (.loop lo hi body) Q
| loopNext {s} {lo hi : U s} {body} :
    lo < hi →
    Omni p Γ st (.letIn (body lo) (fun _ => .loop (lo + 1) hi body)) Q →
    Omni p Γ st (.loop lo hi body) Q

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

theorem Omni.frame {p Γ tp} {vh₁ vh₂ : ValHeap p}  {cls : Closures} {e : Expr (Tp.denote p) tp} {Q}:
    Omni p Γ ⟨vh₁, cls⟩ e Q →
    vh₁.Disjoint vh₂ →
    Omni p Γ ⟨(vh₁ ∪ vh₂), cls⟩ e (fun stv => match stv with
      | some (st, v) => ((fun vals => Q (some (⟨vals, cls⟩, v))) ⋆ (fun vals => vals = vh₂)) st.vals
      | none => Q none
    ) := by
  intro h
  generalize hc : State.mk vh₁ cls = st₁
  rw [hc] at h
  induction h with
  | litField hq
  | skip hq
  | litFalse hq
  | litTrue hq
  | litU hq
  | litRef hq
  | var hq =>
    intro
    subst hc
    constructor
    exists vh₁, vh₂
  | letIn _ _ hN ihE ihB =>
    intro
    constructor
    apply ihE
    assumption
    assumption
    · intro _ _ h
      cases h
      casesm* ∃ _, _, _∧_
      simp_all only
      apply ihB
      simp_all only [State.mk.injEq]
      tauto
      . aesop
      . assumption
    · simp_all
  | callBuiltin hq =>
    cases_type Builtin
    intro
    constructor
    aesop
  | callDecl _ _ _ _ _ ih =>
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
    <;> tauto
  | callLambda =>
    intro
    constructor <;> try tauto

end Lampe
