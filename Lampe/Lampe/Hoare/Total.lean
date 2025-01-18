import Lampe.Ast
import Lampe.Tp
import Lampe.Semantics
import Lampe.SeparationLogic.LawfulHeap
import Lampe.Builtin.Memory

namespace Lampe

def THoare
    {tp : Tp}
    (p : Prime)
    (Γ : Env)
    (P : SLP (State p))
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP (State p)) : Prop :=
  ∀st, P st → Omni p Γ st e (fun r => match r with
    | none => True
    | some (st', v) => Q v st')

namespace THoare

theorem consequence {Q₁ Q₂} {H₂ : SLP (State p)}
    (h_pre_conseq : H₂ ⊢ H₁)
    (h_hoare: THoare p Γ H₁ e Q₁)
    (h_post_conseq : ∀ v, Q₁ v ⊢ Q₂ v) :
    THoare p Γ H₂ e Q₂ := by
  unfold THoare
  intros
  apply Omni.consequence
  any_goals tauto
  rintro (_|_) <;> tauto

theorem var_intro {v} {P : Tp.denote p tp → SLP (State p)} :
    THoare p Γ (P v) (.var v) P := by
  tauto

theorem letIn_intro {P Q}
    (h₁ : THoare p Γ H e₁ P)
    (h₂ : ∀v, THoare p Γ (P v) (e₂ v) Q) :
    THoare p Γ H (.letIn e₁ e₂) Q := by
  unfold THoare
  intros
  constructor <;> tauto

theorem ref_intro {tp : CTp} {v P} :
    THoare p Γ
      (fun st => ∀r, r ∉ st → P r ⟨(st.vals.insert r ⟨tp, v⟩), st.lambdas⟩)
      (.callBuiltin [tp] (CTp.ref tp) Builtin.ref h![v])
      P := by
  unfold THoare
  intros
  constructor
  constructor
  tauto

theorem readRef_intro {ref} {tp : CTp} {v P}:
    THoare p Γ
      (fun st => st.vals.lookup ref = some ⟨(.concrete tp), v⟩ ∧ P v st)
      (.callBuiltin [CTp.ref tp] tp .readRef h![ref])
      P := by
  unfold THoare
  intros
  constructor
  constructor <;> tauto

theorem writeRef_intro {ref} {tp : CTp} {v P} :
    THoare p Γ
      (fun st => ref ∈ st ∧ P () ⟨(st.vals.insert ref ⟨tp, v⟩), st.lambdas⟩)
      (.callBuiltin [CTp.ref tp, tp] CTp.unit .writeRef h![ref, v])
      P := by
  unfold THoare
  intros
  constructor
  constructor <;> tauto

theorem fresh_intro {P} :
    THoare p Γ
      (∀∀v, P v)
      (.callBuiltin [] tp .fresh h![])
      P := by
  unfold THoare
  intro st h
  constructor
  constructor
  tauto

end Lampe.THoare
