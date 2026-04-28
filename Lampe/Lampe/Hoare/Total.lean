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

theorem ref_intro {v P} :
    THoare p Γ
      (fun st => ∀r, r ∉ st → P (LensRef.mk r []) ⟨(st.vals.insert r ⟨tp, v⟩), st.lambdas⟩)
      (.callBuiltin [tp] (.ref tp) .ref h![v])
      P := by
  unfold THoare
  intros
  constructor
  constructor
  tauto

theorem readRef_intro {lensRef : LensRef} {base_tp : Tp} {base_val : Tp.denote p base_tp} :
    THoare p Γ
      (fun st => st.vals.lookup lensRef.ref = some ⟨base_tp, base_val⟩ ∧
                 Tp.followPath (p := p) base_tp base_val lensRef.path tp = some v ∧ P v st)
      (.callBuiltin [.ref tp] tp .readRef h![lensRef])
      P := by
  unfold THoare
  intro st ⟨h1, h2, h3⟩
  constructor
  exact Builtin.readRefOmni.mk h1 h2 h3

theorem writeRef_intro {lensRef : LensRef} {base_tp : Tp}
    {base_val : Tp.denote p base_tp} {base_val' : Tp.denote p base_tp} {v : Tp.denote p tp} :
    THoare p Γ
      (fun st => st.vals.lookup lensRef.ref = some ⟨base_tp, base_val⟩ ∧
                 Tp.modifyAtPath (p := p) base_tp base_val lensRef.path tp v = some base_val' ∧
                 P () ⟨(st.vals.insert lensRef.ref ⟨base_tp, base_val'⟩), st.lambdas⟩)
      (.callBuiltin [.ref tp, tp] .unit .writeRef h![lensRef, v])
      P := by
  unfold THoare
  intro st ⟨h1, h2, h3⟩
  constructor
  exact Builtin.writeRefOmni.mk h1 h2 h3

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
