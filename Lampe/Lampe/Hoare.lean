import Lampe.Ast
import Lampe.Assignable
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Mathlib

namespace Lampe

variable {p : Prime}

def Hoare
    {tp : Tp}
    (Γ : Env)
    (P : State p → Prop)
    (e : Expr (Tp.denote p) tp)
    (Q : State p → tp.denote p → Prop)
    : Prop
  := ∀st, P st ↔ Assignable Γ st e Q

def Hoare.Args
    {tps : List Tp}
    (Γ : Env)
    (P : State p → Prop)
    (es : HList (Expr (Tp.denote p)) tps)
    (Q : State p → HList (Tp.denote p) tps → Prop)
    : Prop
  := ∀st, P st ↔ Assignable.Args Γ st es Q

def Hoare.Call
    {tps : List Tp}
    {tp : Tp}
    (Γ : Env)
    (P : State p → HList (Tp.denote p) tps → Prop)
    (body : HList (Tp.denote p) tps → Expr (Tp.denote p) tp)
    (Q : State p → tp.denote p → Prop)
    : Prop
  := ∀st args, P st args ↔ Assignable Γ st (body args) Q

def Hoare.Builtin
    {tps : List Tp}
    {tp : Tp}
    (P : State p → HList (Tp.denote p) tps → Prop)
    (builtin : Builtin)
    (Q : State p → tp.denote p → Prop)
    : Prop
  := ∀st args, P st args ↔ Assignable.Builtin tps tp builtin args fun v => Q st v

namespace Hoare

theorem Call.intro {P : State p → HList (Tp.denote p) tps → Prop}:
  (∀ args, Hoare Γ (fun st => P st args) (body args) Q) →
  Hoare.Call Γ P body Q := by
  unfold Hoare Hoare.Call
  intro h
  simp [←h]

theorem Args.nil_intro:
    Hoare.Args Γ Q HList.nil (fun st _ => Q st) := by
  unfold Hoare.Args
  noir_simp

theorem Args.cons_intro {P : State p → HList (Tp.denote p) (tp :: tps) → Prop}:
    Hoare Γ P' e P'' →
    (∀v, Hoare.Args Γ (P'' · v) es (fun st args => P st (HList.cons v args))) →
    Hoare.Args Γ P' (HList.cons e es) P := by
  unfold Hoare Hoare.Args
  noir_simp only
  intro he hes st
  rw [he]
  apply Iff.of_eq
  congr
  funext
  rw [hes]

theorem pre_congr {P P' : State p → Prop} (h : P = P'):
    Hoare Γ P e Q → Hoare Γ P' e Q := by
  intros
  simp_all [Hoare]

theorem post_congr(h : Q = Q'):
    Hoare Γ P e Q → Hoare Γ P e Q' := by cases h; intro h; exact h;


theorem var_intro:
    (Hoare Γ (Q · n) (Expr.var n) Q) := by
  unfold Hoare
  noir_simp

theorem lit_u_intro {Q : State p → U s → Prop}:
    (Hoare Γ (Q · n) (Expr.lit (.u s) n) Q) := by
  unfold Hoare
  noir_simp

theorem seq_intro
    (hl : Hoare Γ P e₁ (fun st _ => Q st))
    (hr : Hoare Γ Q e₂ R)
    : Hoare Γ P (Expr.seq e₁ e₂) R := by
  unfold Hoare at *
  noir_simp [hr, hl]

theorem call_builtin_intro
    (hargs : Hoare.Args Γ P es Q)
    (hbuiltin : Hoare.Builtin (tp := tp) Q builtin R)
    : Hoare Γ P (Expr.call HList.nil tp (.builtin builtin) es) R := by
  unfold Hoare Hoare.Args Hoare.Builtin at *
  noir_simp [←hbuiltin, ←hargs]

theorem call_decl_intro {es : HList (Expr (Tp.denote p)) inTps}
    (hlookup : Γ fName = some fn)
    (hc : fn.generics = tyKinds)
    (htci : fn.inTps (hc ▸ generics) = inTps)
    (htco : fn.outTp (hc ▸ generics) = tp)
    (hargs : Hoare.Args Γ P es Q)
    (hbody : Hoare.Call Γ Q (fun args => htco ▸ fn.body _ (hc ▸ generics) (htci ▸ args)) R)
    : Hoare Γ P (Expr.call generics tp (.decl fName) es) R := by
  unfold Hoare Hoare.Args Hoare.Call at *
  intro
  rw [Assignable.callDecl_iff, hargs]
  any_goals assumption
  apply Iff.of_eq
  congr
  funext
  rw [hbody]

theorem letIn_intro
    (hdef : Hoare Γ P e₁ Q)
    (hbody : ∀v, Hoare Γ (Q · v) (e₂ v) R)
    : Hoare Γ P (Expr.letIn e₁ e₂) R := by
  unfold Hoare at *
  noir_simp [←hdef, ←hbody]

theorem Builtin.eq_u_intro {P : State p → Tp.bool.denote p → Prop}:
    Hoare.Builtin
      (tps := [.u s, .u s])
      (fun st h![a, b] => P st (a == b))
      Builtin.eq
      P := by
  unfold Hoare.Builtin
  intros
  casesm* HList _ _
  noir_simp

theorem Builtin.pre_congr {P P' : State p → HList (Tp.denote p) tps → Prop} {Q: State p → Tp.denote p tp → Prop}
    (hl : Hoare.Builtin P  b Q)
    (heq : ∀ st b, P st b ↔ P' st b):
    Hoare.Builtin P' b Q := by
  intros
  simp_all [Hoare.Builtin]

theorem Builtin.fresh_intro {P: State p → Tp.denote p tp → Prop}:
    Hoare.Builtin (tps := []) (p := p) (tp := tp)
      Q
      Builtin.fresh
      (fun st _ => Q st h![]) := by
  unfold Hoare.Builtin
  intros;
  casesm* HList _ _
  noir_simp only

theorem Builtin.assert_intro {P : State p → Tp.unit.denote p → Prop}:
    Hoare.Builtin
      (fun st h![(a : Tp.denote p .bool)] => a ∧ P st ())
      Builtin.assert
      P := by
  unfold Hoare.Builtin
  intros;
  casesm* HList _ _
  noir_simp

end Hoare

end Lampe
