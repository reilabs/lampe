import Lampe.Hoare.SepTotal

open Lampe

namespace LoopDoneRegression

theorem empty_loop_iff (p : Prime) (Γ : Env) (st : State p)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp}
    (Q : Option (State p × Unit) → Prop) (hle : lo ≥ hi) :
    Omni p Γ st (.loop lo hi body) Q ↔ Q (some (st, ())) := by
  constructor
  · intro h
    cases h with
    | loopDone _ hq => exact hq
    | loopNext hlt _ => exact False.elim ((STHoare.BitVec.not_lt.mpr hle) hlt)
  · exact Omni.loopDone hle

-- `empty_loop_iff` and `empty_loop_rejects_false_triple` are enough to pin the fixed behaviour.
theorem empty_loop_preserves_state (p : Prime) (Γ : Env) (st : State p)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    Omni p Γ st (.loop lo hi body) (fun result => result = some (st, ())) := by
  exact Omni.loopDone hle rfl

theorem empty_loop_rejects_false (p : Prime) (Γ : Env) (st : State p)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    ¬ Omni p Γ st (.loop lo hi body) (fun _ => False) := by
  intro h
  exact (empty_loop_iff p Γ st _ hle).mp h

theorem empty_loop_triple (p : Prime) (Γ : Env) (P : SLP (State p))
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    STHoare p Γ P (.loop lo hi body) (fun _ => P) :=
  STHoare.loopDone_intro_of_ge hle

theorem empty_loop_rejects_false_triple (p : Prime) (Γ : Env)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    ¬ STHoare p Γ ⟦⟧ (.loop lo hi body) (fun _ => ⟦False⟧) := by
  intro h
  have hrun := h ⟦⟧ ∅ (by simp [SLP.lift])
  have hpost := (empty_loop_iff p Γ ∅ _ hle).mp hrun
  simp [SLP.star, SLP.lift] at hpost

end LoopDoneRegression
