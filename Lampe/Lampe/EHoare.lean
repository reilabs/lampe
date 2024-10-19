import Lampe.Ast
import Lampe.Assignable
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Mathlib

namespace Lampe

variable (p : Prime)

-- structure StatePredicate (α) where
--   refs : List Ref
--   pred : HList (fun _ => AnyValue p) refs → α → Prop

-- def StatePredicate.eval {p} (sp : StatePredicate p α) (st : State p) (a : α): Prop := go sp.refs sp.pred st a where
--   go (refs : List Ref) (pred : HList (fun _ => AnyValue p) refs → α → Prop) (st : State p) (a : α): Prop :=
--     match refs with
--     | [] => pred h![] a
--     | r :: refs => match st.get? p r with
--       | some v => go refs (fun vs a => pred (HList.cons v vs) a) st a
--       | none => False

-- def StatePredicate.comap {p} (sp : StatePredicate p α) (f : β → α) : StatePredicate p β :=
--   {sp with pred := fun vs b => sp.pred vs (f b)}

-- def StatePredicate.and' {p} (sp : StatePredicate p α) (f : α → Prop): StatePredicate p α :=
--   {sp with pred := fun vs a => sp.pred vs a ∧ f a}

-- def StatePredicate.and {p} (sp : StatePredicate p α) (sp' : StatePredicate p α): StatePredicate p α :=
--   {refs := sp.refs ++ sp'.refs, pred := fun vs a => sp.pred (HList.take sp.refs vs) a ∧ sp'.pred (HList.drop sp.refs vs) a}

-- def StatePredicate.true {p} : StatePredicate p Unit :=
--   {refs := [], pred := fun _ _ => True}

-- def StatePredicate.const (r : Prop): StatePredicate p Unit :=
--   {refs := [], pred := fun _ _ => r}

def StatePredicate (α) := State p → α → Prop

def StatePredicate.eval {p} {α} (sp : StatePredicate p α) (st : State p) (a : α): Prop := sp st a

def StatePredicate.comap {p} {α β} (sp : StatePredicate p α) (f : β → α) : StatePredicate p β :=
  fun st b => sp st (f b)

@[simp]
theorem StatePredicate.comap_eval {sp : StatePredicate p α} {f : β → α} {st : State p} {b : β}:
    (sp.comap f).eval st b ↔ sp.eval st (f b) := by
  rfl

def EHoare
    {tp : Tp}
    (Γ : Env)
    (Q : StatePredicate p Unit)
    (e : Expr (Tp.denote p) tp)
    (P : StatePredicate p (tp.denote p)): Prop :=
  ∀st, Assignable Γ st e P → Q.eval st ()

def EHoare.Args
    {tps : List Tp}
    (Γ : Env)
    (Q : StatePredicate p Unit)
    (es : HList (Expr (Tp.denote p)) tps)
    (P : StatePredicate p (HList (Tp.denote p) tps)): Prop :=
  ∀st, Assignable.Args Γ st es P → Q.eval st ()

def EHoare.Builtin
    (tps : List Tp)
    (tp : Tp)
    (Q : StatePredicate p (HList (Tp.denote p) tps))
    (builtin : Builtin)
    (P : StatePredicate p (Tp.denote p tp)): Prop :=
  ∀st args, Assignable.Builtin tps tp builtin args (fun v => P st v) → Q.eval st args

theorem Assignable.Args.weaken : Assignable.Args Γ st es P → (∀ st vs, P st vs → P' st vs) → Assignable.Args Γ st es P' := by
  intro h h'
  rcases h with ⟨st, v, bs, P⟩
  apply Exists.intro
  apply Exists.intro
  apply And.intro
  assumption
  apply h'
  assumption

theorem Assignable.weaken : Assignable Γ st es P → (∀ st vs, P st vs → P' st vs) → Assignable Γ st es P' := by
  intro h h'
  rcases h with ⟨st, v, bs, P⟩
  apply Exists.intro
  apply Exists.intro
  apply And.intro
  assumption
  apply h'
  assumption

namespace EHoare

theorem Args.nil_intro:
    EHoare.Args p Γ (fun st _ => Q st h![]) HList.nil Q := by
  unfold Args
  noir_simp [StatePredicate.eval]

theorem Args.nil_intro':
    (∀st, Q st h![] → P st ()) →
    EHoare.Args p Γ P HList.nil Q := by
  noir_simp [Args, StatePredicate.eval]

theorem Args.nil_intro'':
    EHoare.Args p Γ P HList.nil (fun st _ => P st ()) := by
  noir_simp [Args, StatePredicate.eval]

theorem Args.cons_intro {R : StatePredicate p (HList (Tp.denote p) (tp :: tps))}:
    EHoare p Γ P e Q →
    (∀ v, EHoare.Args p Γ (fun st _ => Q st v) es (fun st vs => R st (HList.cons v vs))) →
    EHoare.Args p Γ P (HList.cons e es) R := by
  unfold EHoare Args Assignable Assignable.Args
  simp only [StatePredicate.eval]
  rintro e es st ⟨st, ⟨st', ba, r⟩⟩
  apply e
  cases ba
  repeat apply Exists.intro
  apply And.intro
  assumption
  apply es
  repeat apply Exists.intro
  apply And.intro
  assumption
  assumption

theorem Builtin.assert_intro:
    EHoare.Builtin p [.bool] .unit (fun st h![a] => a ∧ P st ()) .assert P := by
  unfold Builtin
  intro _ args
  casesm* HList _ _
  noir_simp [StatePredicate.eval]

theorem Builtin.post_weaken:
    EHoare.Builtin p tps tp Q builtin P →
    (∀ st v, Q st v → Q' st v) →
    EHoare.Builtin p tps tp Q' builtin P := by
  intro h h' _
  intros
  noir_simp [StatePredicate.eval]
  apply_assumption
  unfold Builtin at h
  simp [StatePredicate.eval] at h
  apply h
  assumption

theorem Builtin.fresh_intro:
    EHoare.Builtin p [] .field (fun st _ => ∃ a, P st a) .fresh P := by
  intro _ _
  casesm* HList _ _
  noir_simp [StatePredicate.eval]

theorem Builtin.fresh_intro':
    EHoare.Builtin p [] .field Q .fresh (fun st _ => Q st h![]) := by
  intro _ _
  casesm* HList _ _
  noir_simp [StatePredicate.eval]

theorem Builtin.eq_f_intro:
    EHoare.Builtin p [.field, .field] .bool (fun st h![a, b] => P st (a == b)) .eq P := by
  intro _ _
  casesm* HList _ _
  noir_simp [StatePredicate.eval]

theorem call_builtin_intro:
    EHoare.Args (tps := tps) p Γ P es Q →
    EHoare.Builtin p tps tp Q builtin R →
    EHoare p Γ P (Expr.call HList.nil tp (.builtin builtin) es) R := by
  intro hA hB st
  noir_simp
  intro hAA
  apply hA
  apply Assignable.Args.weaken
  apply hAA
  exact hB

theorem var_intro:
    EHoare p Γ (fun st _ => Q st v) (Expr.var v) Q := by
  unfold EHoare
  noir_simp [StatePredicate.eval]

theorem letIn_intro:
    EHoare p Γ P e₁ Q →
    (∀v, EHoare p Γ (fun st _ => Q st v) (e₂ v) R) →
    EHoare p Γ P (Expr.letIn e₁ e₂) R := by
  noir_simp only [EHoare, StatePredicate.eval]
  intros
  apply_assumption
  apply Assignable.weaken
  assumption
  intros
  apply_assumption
  assumption

theorem letIn_intro' {P Q : StatePredicate p (Tp.denote p tp)}:
    (∀v, Q st v → v = v') →
    EHoare p Γ (fun st _ => P st v') e₁ Q →
    EHoare p Γ (fun st _ => Q st v') (e₂ v') R →
    EHoare p Γ (fun st _ => P st v') (Expr.letIn e₁ e₂) R := by
  noir_simp only [EHoare, StatePredicate.eval]
  intro h
  intros
  apply_assumption
  apply Assignable.weaken
  assumption
  intros
  have : Q st v' := by apply_assumption







theorem seq_intro:
    EHoare p Γ P e₁ (fun st _ => Q st ()) →
    EHoare p Γ Q e₂ R →
    EHoare p Γ P (Expr.seq e₁ e₂) R := by
  noir_simp only [EHoare, StatePredicate.eval]
  intros
  apply_assumption
  apply Assignable.weaken
  assumption
  intros
  apply_assumption
  assumption

end EHoare

end Lampe

nr_def assert<>(x : bool) -> Unit {
  #assert(x) : Unit;
}

nr_def weirdEq<>(x : Field, y : Field) -> Unit {
  let a = #fresh() : Field;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}

open Lampe

example {a : Bool}:
    EHoare p Γ (fun st _ => a ∧ P st ()) (assert.fn.body _ h![] h![a]) P := by
  apply EHoare.call_builtin_intro
  rotate_left
  apply EHoare.Builtin.assert_intro
  apply EHoare.Args.cons_intro
  apply EHoare.var_intro
  intro
  apply EHoare.Args.nil_intro'
  tauto

example {a b : Fp p}:
    EHoare p Γ (fun st _ => a = b ∧ P st ()) (weirdEq.fn.body _ h![] h![a, b]) P := by
  apply EHoare.letIn_intro
  apply EHoare.call_builtin_intro
  apply EHoare.Args.nil_intro''
  apply EHoare.Builtin.post_weaken
  apply EHoare.Builtin.fresh_intro
  intro st _
  rotate_left
  intro v
  apply EHoare.seq_intro

  apply EHoare.call_builtin_intro
  apply EHoare.Args.cons_intro
  apply EHoare.call_builtin_intro
  apply EHoare.Args.cons_intro
  apply EHoare.var_intro
  intro
  apply EHoare.Args.cons_intro
  apply EHoare.var_intro
  intro
  apply EHoare.Args.nil_intro'
  rotate_left
  apply EHoare.Builtin.eq_f_intro
  intro
  apply EHoare.Args.nil_intro
  apply EHoare.Builtin.assert_intro

  apply EHoare.call_builtin_intro
  apply EHoare.Args.cons_intro
  apply EHoare.call_builtin_intro
  apply EHoare.Args.cons_intro
  apply EHoare.var_intro
  intro
  apply EHoare.Args.cons_intro
  apply EHoare.var_intro
  intro
  apply EHoare.Args.nil_intro
  apply EHoare.Builtin.eq_f_intro
  intro
  apply EHoare.Args.nil_intro
  apply EHoare.Builtin.assert_intro

  rotate_left

  simp
  intros
  subst_vars
  rotate_left
  intros

  apply EHoare.call_builtin_intro
  apply EHoare.Args.nil_intro''
  apply EHoare.Builtin.fresh_intro'
  intros
  subst_vars



theorem callAssert (e : Expr (Tp.denote p) .bool):
  EHoare p Γ P e Q →
  (∀ st v, Q st v → v = true) →
  PHoare p Γ P expr![#assert(${e}):Unit] (fun st v => Q st true) := by sorry

theorem assertEq_ph (a b : U 32):
  PHoare p Γ
    (fun _ _ => True)
    expr![ #assert(#eq(${Expr.lit (.u 32) a}, ${Expr.lit (.u 32) b}): bool): Unit ]
    (fun _ _ => a = b) := by
  apply PHoare.callBuiltin_intro
  intro args
  apply PHoare.Args.cons_intro
  apply PHoare.callBuiltin_intro
  apply PHoare.Args.cons_intro
  apply PHoare.lit_u_intro'
  intro



theorem weirdEq.ph_intro {P : StatePredicate _ _}:
    PHoare.Call p Γ
      (P.comap fun args => (args, ()))
      (weirdEq.fn.body _ h![.field])
      (P.and' fun (h![a, b], _) => a = b) := by
  apply PHoare.Call.intro
  intro args
  casesm* HList _ _
  simp only [weirdEq]
  apply PHoare.letIn_intro


/---

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
    (hlookup : Γ fName = some func)
    (hc : func.generics = tyKinds)
    (htci : func.inTps (hc ▸ generics) = inTps)
    (htco : func.outTp (hc ▸ generics) = tp)
    (hargs : Hoare.Args Γ P es Q)
    (hbody : Hoare.Call Γ Q (fun args => htco ▸ func.body _ (hc ▸ generics) (htci ▸ args)) R)
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
  noir_simp
  sorry

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
