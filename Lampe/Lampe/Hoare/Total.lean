import Lampe.Ast
import Lampe.Tp
import Lampe.Semantics
import Lampe.SeparationLogic

namespace Lampe

def THoare
    {tp : Tp}
    (p : Prime)
    (Γ : Env)
    (P : SLP p)
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP p): Prop :=
  ∀st, P st.vals → Omni p Γ st e (fun r => match r with
    | none => True
    | some (st', v) => Q v st'.vals)

namespace THoare

variable
  {p : Prime}
  {H H₁ H₂ : SLP p}
  {Γ : Env}
  {tp : Tp}
  {e : Expr (Tp.denote p) tp}

theorem consequence {Q₁ Q₂}
    (h_pre_conseq : H₂ ⊢ H₁)
    (h_hoare: THoare p Γ H₁ e Q₁)
    (h_post_conseq : ∀ v, Q₁ v ⊢ Q₂ v):
    THoare p Γ H₂ e Q₂ := by
  unfold THoare
  intros
  apply Omni.consequence
  any_goals tauto
  rintro (_|_) <;> tauto

theorem var_intro {v} {P : Tp.denote p tp → SLP p}:
    THoare p Γ (P v) (.var v) P := by
  tauto

/-- [TODO] there's probably a generic lemma for pure builtins to abstract this proof structure? -/
theorem assert_intro {v: Bool} (h : v ⋆ P ⊢ Q ()):
    THoare p Γ P (.call h![] [.bool] .unit (.builtin Builtin.assert) h![v]) Q := by
  unfold THoare
  intros
  constructor
  simp only [Builtin.assert]
  cases v
  · apply Builtin.genericPureOmni.err
    · simp
    · tauto
    · exact ()
  · apply Builtin.genericPureOmni.ok
    · simp_all; tauto
    · exact ()
    · simp_all

theorem letIn_intro {P Q}
    (h₁ : THoare p Γ H e₁ P)
    (h₂ : ∀v, THoare p Γ (P v) (e₂ v) Q):
    THoare p Γ H (.letIn e₁ e₂) Q := by
  unfold THoare
  intros
  constructor <;> tauto

theorem ref_intro {v}:
    THoare p Γ
      (fun st => ∀r, r ∉ st → P r (st.insert r ⟨tp, v⟩))
      (.call h![] [tp] (Tp.ref tp) (.builtin .ref) h![v])
      P := by
  unfold THoare
  intros
  constructor
  constructor
  tauto

theorem readRef_intro {ref}:
    THoare p Γ
      (fun st => st.lookup ref = some ⟨tp, v⟩ ∧ P v st)
      (.call h![] [tp.ref] tp (.builtin .readRef) h![ref])
      P := by
  unfold THoare
  intros
  constructor
  constructor
  tauto
  tauto

theorem writeRef_intro {ref v}:
    THoare p Γ
      (fun st => ref ∈ st ∧ P () (st.insert ref ⟨tp, v⟩))
      (.call h![] [tp.ref, tp] .unit (.builtin .writeRef) h![ref, v])
      P := by
  unfold THoare
  intros
  constructor
  constructor
  tauto
  tauto

theorem fresh_intro:
    THoare p Γ
      (∀∀v, P v)
      (.call h![] [] tp (.builtin .fresh) h![])
      P := by
  unfold THoare
  intro st h
  constructor
  constructor
  tauto

end Lampe.THoare
