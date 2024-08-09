import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Mathlib

namespace Lampe

variable {P : Prime}

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

def Assignable.Loop (Γ : Env) (st : State P) (lo hi : Nat) (body : U s → Expr (Tp.denote P) tp) (Q : State P → Prop) : Prop :=
  ∃st', BigStepLoop P Γ st lo hi body st' ∧ Q st'

theorem Assignable.Args.nil_iff:
    Assignable.Args (P:=P) Γ st HList.nil Q ↔ Q st HList.nil := by
  simp [Assignable.Args]
  apply Iff.intro
  · intro_cases
    casesm BigStepArgs _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Args.cons_iff:
    Assignable.Args (P:=P) Γ st (HList.cons e es) Q ↔
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
    Assignable (P:=P) Γ st (.seq e1 e2) Q ↔
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
    Assignable (P:=P) Γ st (.letIn e f) Q ↔
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

theorem Assignable.letMutIn_iff {e : Expr _ tp}:
    Assignable (P:=P) Γ st (.letMutIn e f) Q ↔
    Assignable Γ st e (fun st' v => Assignable Γ (st'.alloc P tp v) (f st'.nextRef) Q) := by
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
    · apply BigStep.letMutIn <;> assumption
    · assumption

theorem Assignable.callDecl_iff
  {generics : HList Kind.denote tyKinds} {args : HList (Expr (Tp.denote P)) inTps} {Q : State P → Tp.denote P outTp → Prop} {st : State P}
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
    Assignable (P:=P) Γ st (.var x) Q ↔
    Q st x := by
  unfold Assignable
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    assumption
  · intro_cases
    tauto

theorem Assignable.callBuiltin_iff:
    Assignable (P:=P) Γ st (@Expr.call _ [] intps HList.nil outtp (.builtin b) args) Q ↔
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

theorem Assignable.Builtin.lt_u_iff :
    Assignable.Builtin (P:=P) [.u n, .u n] .bool .lt h![a, b] Q ↔ Q (a < b) := by
  simp only [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.assert_iff :
  Assignable.Builtin (P:=P) [.bool] .unit .assert h![p] Q ↔ p ∧ Q ():= by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem Assignable.Builtin.not_iff :
  Assignable.Builtin (P:=P) [.bool] .bool .not h![p] Q ↔ Q (!p) := by
  simp only [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.div_f_iff :
    Assignable.Builtin (P:=P) [.field, .field] .field .div h![a, b] Q ↔ (b ≠ 0) ∧ Q (a / b) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.div_u_iff :
    Assignable.Builtin (P:=P) [.u n, .u n] (.u n) .div h![a, b] Q ↔ (b ≠ 0) ∧ Q (a / b) := by
  simp only [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.sub_f_iff :
    Assignable.Builtin (P:=P) [.field, .field] .field .sub h![a, b] Q ↔ Q (a - b) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.sub_u_iff :
    Assignable.Builtin (P:=P) [.u n, .u n] (.u n) .sub h![a, b] Q ↔ b.val ≤ a.val ∧ Q (a - b) := by
  simp [Assignable.Builtin, and_assoc]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem Assignable.Builtin.add_u_iff :
  Assignable.Builtin (P:=P) [.u n, .u n] (.u n) .add h![a, b] Q ↔ a.val + b.val < 2^n ∧ Q (a + b) := by
  simp [Assignable.Builtin, and_assoc]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem Assignable.Builtin.add_f_iff :
  Assignable.Builtin (P:=P) [.field, .field] .field .add h![a, b] Q ↔ Q (a + b) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.fresh_iff :
  Assignable.Builtin (P:=P) [] tp .fresh HList.nil Q ↔ ∃v, Q v := by
  unfold Assignable.Builtin; tauto

theorem Assignable.Builtin.cast_uu_iff :
  Assignable.Builtin (P:=P) [.u s] (.u t) .cast h![n] Q ↔ Q n := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.cast_uf_iff :
  Assignable.Builtin (P:=P) [.u s] .field .cast h![n] Q ↔ Q (uToFp P n) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.cast_fu_iff :
  Assignable.Builtin (P:=P) [.field] (.u s) .cast h![n] Q ↔ Q (fpToU P n) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.modulusNumBits_iff :
  Assignable.Builtin (P:=P) [] (.u 64) .modulusNumBits HList.nil Q ↔ Q (numBits P.natVal) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.toLeBytes_iff : Assignable.Builtin (P:=P) [.field, .u 32] (.slice (.u 8)) .toLeBytes h![n, s] Q ↔
  ∃(result : List (U 8)), result.length = s.val ∧ ∑i, (result.get i).val * 2^i.val = n ∧ Q result := by
  simp only [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Builtin.index_iff {slice : List (t.denote P)} (h : List.length slice > i.val):
  Assignable.Builtin (P:=P) [.slice t, .u s] t .index h![slice, i] Q ↔
  Q (slice.get ⟨i, h⟩) := by
  simp [Assignable.Builtin]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.ite_iff:
    Assignable (P:=P) Γ st (.ite b t e) Q ↔
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
    Assignable.Ite (P:=P) Γ st b t e Q ↔ Assignable Γ st t Q := by
  simp [Assignable.Ite, hb]

theorem Assignable.Ite.iff_false (hb : b = false):
    Assignable.Ite (P:=P) Γ st b t e Q ↔ Assignable Γ st e Q := by
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
    Assignable (P:=P) Γ st (.struct fields) Q ↔
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
    Assignable.Fields (P:=P) Γ st HList.nil Q ↔ Q st () := by
  simp [Assignable.Fields]
  apply Iff.intro
  · intro_cases
    casesm BigStepFields _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem Assignable.Fields.cons_iff:
    Assignable.Fields (P:=P) Γ st (HList.cons e es) Q ↔
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

theorem Assignable.loop_iff:
    Assignable (P:=P) Γ st (.loop elo ehi body) Q ↔
    Assignable Γ st elo fun st vlo =>
      Assignable Γ st ehi fun st vhi =>
        Assignable.Loop Γ st vlo vhi body fun st => Q st () := by
  simp [Assignable.Loop, Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStep.loop <;> assumption
    · assumption

theorem Assignable.Loop.stop_iff {lo hi : ℕ} (h: lo ≥ hi):
    Assignable.Loop (P:=P) Γ st lo hi body Q ↔
    Q st := by
  simp [Assignable.Loop]
  apply Iff.intro
  · intro_cases
    casesm BigStepLoop _ _ _ _ _ _ _
    have := Nat.not_lt_of_le h (by assumption)
    cases this
    assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    apply BigStepLoop.done (by assumption)
    assumption

theorem Assignable.Loop.continue_iff {lo hi : ℕ} (h: lo < hi):
    Assignable.Loop (s := s) (P:=P) Γ st lo hi body Q ↔
    Assignable Γ st (body (lo : U s)) fun st _ => Assignable.Loop Γ st lo.succ hi body Q := by
  simp only [Assignable.Loop, Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStepLoop _ _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
    cases Nat.not_le_of_lt h (by assumption)
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStepLoop.cont <;> assumption
    · assumption

theorem Assignable.readRef_iff {ref : Tp.denote P (.ref tp)} (h: st.get? P ref = some ⟨tp, v⟩):
    Assignable (P:=P) Γ st (.readRef (.var ref)) Q ↔ Q st v := by
  simp [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    rw [h] at *
    rename some _ = some _ => hp
    cases hp
    tauto
  · intro_cases
    tauto

theorem Assignable.writeRef_iff {e : Expr (Tp.denote P) tp}:
    Assignable Γ st (.writeRef (.var ref) e) Q ↔
    Assignable Γ st e (fun st' v => Q (st'.set P ref tp v) ()) := by
  simp [Assignable]
  apply Iff.intro
  · intro_cases
    casesm BigStep _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStep.writeRef <;> assumption
    · assumption

section macros

open Lean Elab.Tactic Parser.Tactic Lean.Meta

def discharge (prop : Lean.Expr) : SimpM (Option Lean.Expr) := do
    try
      let mvar ← mkFreshExprMVar prop
      withTransparency TransparencyMode.all mvar.mvarId!.refl
      return some mvar
    catch _ => pure ()

    Simp.dischargeDefault? prop

elab "noir_simp_discharge" : tactic => wrapSimpDischarger discharge

syntax "noir_simp" (config)? (discharger)? (&" only")? (simpArgs)? (location)? : tactic

lemma decidable_and_true (P Q : Prop) [Decidable P] (h : P) : P ∧ Q ↔ Q := by tauto

def nrNormTheorems : List Name := [
    ``Assignable.callBuiltin_iff,
    ``Assignable.callDecl_iff,
    ``Assignable.ite_iff,
    ``Assignable.letIn_iff,
    ``Assignable.letMutIn_iff,
    ``Assignable.lit_field_iff,
    ``Assignable.lit_u_iff,
    ``Assignable.lit_true_iff,
    ``Assignable.lit_false_iff,
    ``Assignable.loop_iff,
    ``Assignable.proj_iff,
    ``Assignable.readRef_iff,
    ``Assignable.seq_iff,
    ``Assignable.struct_iff,
    ``Assignable.var_iff,
    ``Assignable.writeRef_iff,

    ``Assignable.Args.nil_iff,
    ``Assignable.Args.cons_iff,

    ``Assignable.Builtin.add_f_iff,
    ``Assignable.Builtin.add_u_iff,
    ``Assignable.Builtin.assert_iff,
    ``Assignable.Builtin.cast_fu_iff,
    ``Assignable.Builtin.cast_uf_iff,
    ``Assignable.Builtin.cast_uu_iff,
    ``Assignable.Builtin.div_f_iff,
    ``Assignable.Builtin.div_u_iff,
    ``Assignable.Builtin.eq_f_iff,
    ``Assignable.Builtin.eq_u_iff,
    ``Assignable.Builtin.fresh_iff,
    ``Assignable.Builtin.index_iff,
    ``Assignable.Builtin.lt_u_iff,
    ``Assignable.Builtin.not_iff,
    ``Assignable.Builtin.sub_f_iff,
    ``Assignable.Builtin.sub_u_iff,
    ``Assignable.Builtin.toLeBytes_iff,
    ``Assignable.Builtin.modulusNumBits_iff,

    ``Assignable.Fields.nil_iff,
    ``Assignable.Fields.cons_iff,

    ``Assignable.Ite.iff_true,
    ``Assignable.Ite.iff_false,

    ``Assignable.Fields.nil_iff,
    ``Assignable.Fields.cons_iff,

    ``Assignable.Loop.stop_iff,
    ``Assignable.Loop.continue_iff,

    ``State.alloc_allocs_singleton,
    ``State.allocs_allocs_singleton,
    ``List.length_cons,
    ``List.length_nil,

    ``decidable_and_true,
    ``true_and,
]

elab_rules : tactic
| `(tactic|noir_simp $[$cfg:config]? $[(discharger := $dis)]? $[only%$only?]?
    $[$sa:simpArgs]? $[$loc:location]?) => withMainContext do
  let cfg ← elabSimpConfig (mkOptionalNode cfg) .simp
  let loc := expandOptLocation (mkOptionalNode loc)
  let dis ← match dis with
  | none =>
    let ⟨_, d⟩ ← tacticToDischarge (←`(tactic|(first | noir_simp_discharge | decide)))
    pure d
  | some d => do
    let ⟨_, d⟩ ← tacticToDischarge d
    pure d

  let thms0 ← if only?.isSome then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else getSimpTheorems

  let thmsWithBuiltins ← nrNormTheorems.foldlM (·.addConst · (prio := eval_prio low)) thms0

  let ctx : Simp.Context := {
     simpTheorems := #[thmsWithBuiltins]
     congrTheorems := ← getSimpCongrTheorems
     config := cfg
  }

  let mut r ← elabSimpArgs (sa.getD ⟨.missing⟩) ctx (simprocs := {}) (eraseLocal := false) .simp
  _ ← simpLocation r.ctx {} dis loc

end macros


end Lampe
