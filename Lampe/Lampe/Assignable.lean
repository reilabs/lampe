import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Mathlib

namespace Lampe

def Assignable (Γ : Env) (st : State P) (e : Expr (Tp.denote P) tp) (Q : State P → (tp.denote P) → Prop) : Prop :=
  ∃st' v, BigStep P Γ st e st' v ∧ Q st' v

def Assignable.Args {atps : List Tp} (Γ : Env) (st : State P) (es : HList (Expr (Tp.denote P)) atps) (Q: State P → HList (Tp.denote P) atps → Prop): Prop :=
  ∃st' vs, BigStepArgs P Γ st es st' vs ∧ Q st' vs

def Assignable.Builtin (argTypes : List Tp) (resType : Tp) (b : Builtin) (as : HList (Tp.denote P) argTypes) (Q : Tp.denote P resType → Prop): Prop :=
  ∃r, BigStepBuiltin P argTypes resType b as r ∧ Q r

def Assignable.Ite (Γ : Env) (st : State P) (b : Bool) (t e : Expr (Tp.denote P) a) (Q : State P → Tp.denote P a → Prop): Prop :=
    (b ∧ Assignable Γ st t Q) ∨
    (!b ∧ Assignable Γ st e Q)

def Assignable.Fields {fields : List Tp} (Γ : Env) (st : State P) (es : HList (Expr (Tp.denote P)) fields) (Q: State P → Tp.denoteArgs P fields → Prop): Prop :=
  ∃st' vs, BigStepFields P Γ st es st' vs ∧ Q st' vs

theorem Assignable.Args.nil_iff:
    Assignable.Args Γ st HList.nil Q ↔ Q st HList.nil := by
  simp [Assignable.Args]
  apply Iff.intro
  · intro_cases
    casesm BigStepArgs _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Args.cons_iff:
    Assignable.Args Γ st (HList.cons e es) Q ↔
    Assignable Γ st e (fun st' v => Assignable.Args Γ st' es (fun st' vs => Q st' (HList.cons v vs))) := by
  simp [Assignable.Args]
  apply Iff.intro
  · intro_cases
    casesm BigStepArgs _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · rintro ⟨_, _, _, _, _, _, _⟩
    repeat apply Exists.intro
    apply And.intro
    apply BigStepArgs.cons <;> assumption
    assumption

theorem Assignable.seq_iff:
    Assignable Γ st (.seq e1 e2) Q ↔
    Assignable Γ st e1 (fun st' _ => Assignable Γ st' e2 Q) := by
  unfold Assignable
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStep.seq <;> assumption
    · assumption

theorem Assignable.letIn_iff:
    Assignable Γ st (.letIn e f) Q ↔
    Assignable Γ st e (fun st' v => Assignable Γ st' (f v) Q) := by
  unfold Assignable
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStep.letIn <;> assumption
    · assumption

theorem Assignable.callDecl_iff
  {P} {generics : HList Kind.denote tyKinds} {args : HList (Expr (Tp.denote P)) inTps} {Q : State P → Tp.denote P outTp → Prop} {st : State P}
  (hlookup : Γ fname = some fn)
  (hc : fn.generics = tyKinds)
  (htci : fn.inTps (hc ▸ generics) = inTps)
  (htco : fn.outTp (hc ▸ generics) = outTp):
    Assignable Γ st (.call generics outTp (.decl fname) args) Q ↔
    Assignable.Args Γ st args (fun st' vs =>
      Assignable Γ st' (htco ▸ fn.body _ (hc ▸ generics) (htci ▸ vs)) Q) := by
  unfold Assignable
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro
    rename BigStep _ _ _ _ _ _ => h
    convert h
    rw [hlookup] at *
    rename (some _ = some _) => hp
    cases hp
    rfl
    assumption
  · rintro ⟨st', args, bsa, _, _, body, q⟩
    rcases fn
    cases htci
    cases htco
    rcases hc
    repeat apply Exists.intro
    apply And.intro
    apply BigStep.callDecl
    assumption
    assumption
    rotate_left
    rfl
    rfl
    rfl
    assumption
    assumption

theorem Assignable.var_iff:
    Assignable Γ st (.var x) Q ↔
    Q st x := by
  unfold Assignable
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    assumption
  · intro_cases
    tauto

theorem Assignable.callBuiltin_iff:
    Assignable Γ st (@Expr.call _ [] intps HList.nil outtp (.builtin b) args) Q ↔
    Assignable.Args Γ st args (fun st' args => Assignable.Builtin intps outtp b args fun v => Q st' v) := by
  apply Iff.intro
  · intro h
    rcases h with ⟨_, _, h, _⟩
    cases h
    apply Exists.intro
    apply Exists.intro
    apply And.intro
    assumption
    apply Exists.intro
    apply And.intro <;> assumption
  · rintro ⟨_, _, _, _, _, _⟩
    repeat apply Exists.intro
    apply And.intro
    apply BigStep.callBuiltin <;> assumption
    assumption

theorem Assignable.Builtin.eq_f_iff :
    Assignable.Builtin (P := P) [.field, .field] .bool .eq h![a, b] Q ↔ Q (a == b) := by
  unfold Assignable.Builtin
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    assumption
  · intro
    apply Exists.intro
    apply And.intro
    apply BigStepBuiltin.eqF
    assumption

theorem Assignable.Builtin.eq_u_iff :
    Assignable.Builtin (P := P) [.u n, .u n] .bool .eq h![a, b] Q ↔ Q (a == b) := by
  unfold Assignable.Builtin
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    assumption
  · intro
    apply Exists.intro
    apply And.intro
    apply BigStepBuiltin.eqU
    assumption

theorem Assignable.Builtin.assert_iff :
  Assignable.Builtin [.bool] .unit .assert h![p] Q ↔ p ∧ Q ():= by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem Assignable.Builtin.sub_u_iff :
  Assignable.Builtin [.u n, .u n] (.u n) .sub h![a, b] Q ↔ b.val ≤ a.val ∧ Q (a - b) := by
  simp [Assignable.Builtin, and_assoc]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem Assignable.Builtin.add_u_iff :
  Assignable.Builtin [.u n, .u n] (.u n) .add h![a, b] Q ↔ a.val + b.val < 2^n ∧ Q (a + b) := by
  simp [Assignable.Builtin, and_assoc]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem Assignable.Builtin.fresh_iff :
  Assignable.Builtin [] tp .fresh HList.nil Q ↔ ∃v, Q v := by
  unfold Assignable.Builtin; tauto

theorem Assignable.ite_iff:
    Assignable Γ st (.ite b t e) Q ↔
    Assignable Γ st b (fun st' v => Assignable.Ite Γ st' v t e Q) := by
  simp [Assignable, Assignable.Ite]
  apply Iff.intro
  · intro_cases
    rename BigStep _ _ _ _ _ _ => h
    cases h
    · repeat apply Exists.intro
      apply Or.inr
      apply And.intro
      assumption
      repeat apply Exists.intro
      apply And.intro <;> assumption
    · repeat apply Exists.intro
      apply Or.inl
      apply And.intro
      assumption
      repeat apply Exists.intro
      apply And.intro <;> assumption
  · intro_cases
    casesm* _ ∨ _ <;> {
      casesm* _ ∧ _, ∃ _, _
      subst_vars
      repeat apply Exists.intro
      apply And.intro
      · try (apply BigStep.iteTrue <;> assumption)
        try (apply BigStep.iteFalse <;> assumption)
      · assumption
    }

theorem Assignable.Ite.iff_true (hb : b = true):
    Assignable.Ite Γ st b t e Q ↔ Assignable Γ st t Q := by
  simp [Assignable.Ite, hb]

theorem Assignable.Ite.iff_false (hb : b = false):
    Assignable.Ite Γ st b t e Q ↔ Assignable Γ st e Q := by
  simp [Assignable.Ite, hb]

theorem Assignable.lit_field_iff : Assignable (P:=P) Γ st (.lit .field v) Q ↔ Q st v := by
  simp [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.lit_u_iff : Assignable (P:=P) Γ st  (.lit (.u n) v ) Q ↔ Q st v := by
  simp only [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.lit_false_iff : Assignable (P:=P) Γ st (.lit .bool 0) Q ↔ Q st false := by
  simp only [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.lit_true_iff : Assignable (P:=P) Γ st (.lit .bool 1) Q ↔ Q st true := by
  simp only [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.struct_iff:
    Assignable Γ st (.struct fields) Q ↔
    Assignable.Fields Γ st fields Q := by
  simp [Assignable.Fields, Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.proj_iff:
    Assignable (P:=P) Γ st (.proj mem struct) Q ↔
    Assignable Γ st struct (fun st' v => Q st' (getProj P mem v)) := by
  simp [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Fields.nil_iff:
    Assignable.Fields Γ st HList.nil Q ↔ Q st () := by
  simp [Assignable.Fields]
  apply Iff.intro
  · intro_cases
    casesm BigStepFields _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Fields.cons_iff:
    Assignable.Fields Γ st (HList.cons e es) Q ↔
    Assignable Γ st e (fun st' v => Assignable.Fields Γ st' es (fun st' vs => Q st' (v, vs))) := by
  simp [Assignable.Fields]
  apply Iff.intro
  · intro_cases
    casesm BigStepFields _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · unfold Assignable
    intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStepFields.cons <;> assumption
    · assumption

end Lampe
