-- This module serves as the root of the `Lampe` library.
-- Import modules here that should be built as part of the library.
import «Lampe».Basic
import Lean.Meta.Tactic.Simp.Main

-- abbrev testMod := noir! {
--   fn recursiveMul(n,k) {
--     if n == (0 : u 64) then (0 : u 64) else {
--       let n = n - (1 : u 64);
--       k + recursiveMul(n, k)
--     }
--   }

--   fn assertEq(a,b) {
--     let x = fresh;
--     assert(x == a);
--     assert(x == b);
--   }

--   fn lt_fallback(x, y) {
--     let num_bytes = (((field::modulus_num_bits() #as u 32) + (7: u 32)) / (8 : u 32));
--     let x_bytes = field::Field::to_le_bytes(x, num_bytes);
--     let y_bytes = field::Field::to_le_bytes(y, num_bytes);
--     let mut x_is_lt = false;
--     let mut done = false;
--     for i in (0 : u 32) .. num_bytes {
--         if (!done) then {
--             let x_byte = x_bytes[((num_bytes - (1 : u 32)) - i)] #as u 8;
--             let y_byte = y_bytes[((num_bytes - (1 : u 32)) - i)] #as u 8;
--             let bytes_match = (x_byte == y_byte);
--             if (!bytes_match) then {
--                 x_is_lt = (x_byte < y_byte);
--                 done = true;
--             }
--         }
--     };
--     x_is_lt
--   }
-- }

def assertEq : Lampe.Function := Sigma.mk [.field, .field] $ Sigma.mk .unit $ fun h![a, b] =>
  .letIn (.call [] .field (.builtin .fresh) h![]) (fun x => .seq
    (.call [.bool] .unit (.builtin .assert) h![.call [.field, .field] .bool (.builtin .eq) h![.var x, .var a]])
    (.call [.bool] .unit (.builtin .assert) h![.call [.field, .field] .bool (.builtin .eq) h![.var x, .var b]])
  )

def testMod : Lampe.Module := ⟨[⟨"assertEq", assertEq⟩]⟩

theorem simplify_binder {p : α → Prop} (hp : ∀x, p x → y = x) : (∃x, p x) ↔ p y := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rw [hp x hp']
    assumption
  · intro hp'
    apply Exists.intro y
    assumption

theorem simplify_binder_under_ex {p : α → Prop} {q : β → α} (hp : ∀x, p x → ∃y, x = q y) : (∃x, p x) ↔ ∃y, p (q y) := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rcases hp x hp' with ⟨_, ⟨_⟩⟩
    apply Exists.intro
    assumption
  · intro ⟨y, hp'⟩
    apply Exists.intro
    assumption

syntax "introB": tactic
macro_rules | `(tactic|introB) => `(tactic | (intros ; try casesm* _ ∧ _, ∃_, _))

syntax "ex_dsch" :tactic
macro_rules | `(tactic|ex_dsch) => `(tactic | (introB; (first | assumption | (symm; assumption))))

syntax "binder_simp" : tactic
macro_rules
| `(tactic | binder_simp) =>
  `(tactic | (first | simp (disch := ex_dsch) only [simplify_binder]))

syntax "ex_dsch2" :tactic
macro_rules
| `(tactic|ex_dsch2) =>
  `(tactic| introB; apply Exists.intro; assumption)

section macros
open Lean Elab.Tactic Parser.Tactic Lean.Meta

def discharge (prop : Expr) : SimpM (Option Expr) := do
    try
      let mvar ← mkFreshExprMVar prop
      withTransparency TransparencyMode.all mvar.mvarId!.refl
      return some mvar
    catch _ => pure ()

    Simp.dischargeDefault? prop

elab "noir_simp_discharge" : tactic => wrapSimpDischarger discharge

syntax "noir_simp" (config)? (discharger)? (&" only")? (simpArgs)? (location)? : tactic

elab_rules : tactic
| `(tactic|noir_simp $[$cfg:config]? $[(discharger := $dis)]? $[only%$only?]?
    $[$sa:simpArgs]? $[$loc:location]?) => withMainContext do
  let cfg ← elabSimpConfig (mkOptionalNode cfg) .simp



syntax "crush" : tactic
macro_rules
| `(tactic|crush) => `(tactic|
  repeat (first | simp | simp (disch := ex_dsch) only [simplify_binder] | simp (disch := ex_dsch2) only [simplify_binder_under_ex] | simp (disch := with_unfolding_all rfl) only [Lampe.BigStepAux.callArgPrepDeclDone_iff]))
end macros

open Lampe

def ConvergeWithPostCond (Γ : Env) (st : State P) (e : Expr' (InstanceOf P) tp) (Q : State P → (InstanceOf P tp) → Prop) : Prop :=
  ∃st' v, BigStepAux P Γ st e st' v ∧ Q st' v

def ArgsWPC {atps : List Tp} (Γ : Env) (st : State P) (es : HList (Expr' (InstanceOf P)) atps) (Q: State P → HList (InstanceOf P) atps → Prop): Prop :=
  ∃st' vs, BigStepArgs P Γ st es st' vs ∧ Q st' vs

theorem ArgsWPC.nil_iff:
    ArgsWPC Γ st HList.nil Q ↔ Q st HList.nil := by
  simp [ArgsWPC]
  apply Iff.intro
  · intro_cases
    casesm BigStepArgs _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem ArgsWPC.cons_iff:
    ArgsWPC Γ st (HList.cons e es) Q ↔
    ConvergeWithPostCond Γ st e (fun st' v => ArgsWPC Γ st' es (fun st' vs => Q st' (HList.cons v vs))) := by
  simp [ArgsWPC]
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

def ConvergeWithPostCond.of_BigStepAux :
  BigStepAux P Γ st e st' v ↔ ConvergeWithPostCond Γ st e (λ st'' v' => st' = st'' ∧ v' = v) := by
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro h
    repeat apply Exists.intro
    apply And.intro h
    tauto
  · intro_cases
    subst_vars
    assumption


-- theorem BigStepAux.exists_scope_blockNext_iff :
--   (∃sc', BigStepAux P Γ st sc (.expr (.block es fe)) st' sc' v) ↔
--   BigStepAux P Γ st sc (.expr (.block es fe)) st' sc v := by
--   cases es <;> simp

-- theorem BigStepAux.blockNext_iff':
--     BigStepAux P Γ st sc (.expr (.block (e::es) r)) st' sc' v ↔
--     (∃st'' sc'' a, BigStepAux P Γ st sc (.expr e) st'' sc'' a ∧ BigStepAux P Γ st'' sc'' (.expr (.block es r)) st' sc'' v) ∧ sc' = sc := by
--   apply Iff.intro
--   · simp
--     intro_cases
--     subst_vars
--     apply And.intro <;> try rfl
--     repeat apply Exists.intro
--     apply And.intro
--     · apply Exists.intro
--       assumption
--     · assumption
--   · simp
--     intro_cases
--     apply And.intro <;> try assumption
--     repeat apply Exists.intro
--     apply And.intro <;> assumption

theorem ConvergeWithPostCond.seq_iff:
    ConvergeWithPostCond Γ st (.seq e1 e2) Q ↔
    ConvergeWithPostCond Γ st e1 (fun st' _ => ConvergeWithPostCond Γ st' e2 Q) := by
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro_cases
    casesm BigStepAux _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStepAux.seq <;> assumption
    · assumption

-- theorem ConvergeWithPostCond.blockNext_iff:
--     ConvergeWithPostCond Γ st sc (.expr (.block (e::es) r)) Q ↔
--     ConvergeWithPostCond Γ st sc (.expr e) (fun st' sc' _ => ConvergeWithPostCond Γ st' sc' (.expr (.block es r)) fun st' sc'' v => sc' = sc'' ∧ Q st' sc v) := by
--     simp [ConvergeWithPostCond]
--     apply Iff.intro
--     · intro_cases
--       subst_vars
--       tauto
--     · intro_cases
--       subst_vars
--       tauto

-- theorem ConvergeWithPostCond.blockDone_iff:
--     ConvergeWithPostCond Γ st sc (.expr (.block [] r)) Q ↔
--     ConvergeWithPostCond Γ st sc (.expr r) (fun st' _ v => Q st' sc v) := by
--   simp [ConvergeWithPostCond]
--   apply Iff.intro
--   · intro_cases
--     subst_vars
--     tauto
--   · intro_cases
--     subst_vars
--     tauto

theorem ConvergeWithPostCond.letIn_iff:
    ConvergeWithPostCond Γ st (.letIn e f) Q ↔
    ConvergeWithPostCond Γ st e (fun st' v => ConvergeWithPostCond Γ st' (f v) Q) := by
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro_cases
    casesm BigStepAux _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStepAux.letIn <;> assumption
    · assumption

-- theorem ConvergeWithPostCond.declareVar_iff:
--     ConvergeWithPostCond Γ st sc (.expr (.declareVar x v)) Q ↔
--     ConvergeWithPostCond Γ st sc (.expr v) (fun st' sc' v' => sc' = sc ∧ Q st' (sc.update x (.value v')) ⟨.unit, ()⟩) := by
--   simp [ConvergeWithPostCond]
--   apply Iff.intro
--   · intro_cases
--     subst_vars
--     tauto
--   · intro_cases
--     subst_vars
--     tauto

-- theorem ConvergeWithPostCond.fresh_iff:
--     ConvergeWithPostCond Γ st sc (.expr .fresh) Q ↔
--     ∃v, Q st sc v := by
--   simp [ConvergeWithPostCond]
--   apply Iff.intro <;> {
--     intro_cases
--     subst_vars
--     tauto
--   }

theorem ConvergeWithPostCond.callDecl_iff
  {P} {args : HList (Expr' (InstanceOf P)) inTps} {Q : State P → InstanceOf P outTp → Prop} {st : State P}
  (hlookup : Γ fname = some fn) (hin : fn.1 = inTps) (hout : fn.2.1 = outTp):
    ConvergeWithPostCond (P := P) Γ st (.call inTps outTp (.decl fname) args) Q ↔
    ArgsWPC (P := P) Γ st args fun st' vs =>
      ConvergeWithPostCond Γ st' (hout ▸ fn.2.2 (hin ▸ vs)) Q
     := by
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro_cases
    casesm BigStepAux _ _ _ _ _ _
    repeat apply Exists.intro
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro
    rename BigStepAux _ _ _ _ _ _ => h
    convert h
    rw [hlookup] at *
    rename (some _ = some _) => hp
    cases hp
    rfl
    assumption
  · rintro ⟨st', args, bsa, _, _, body, q⟩
    cases hin
    cases hout
    repeat apply Exists.intro
    apply And.intro
    apply BigStepAux.callDecl <;> assumption
    assumption

theorem ConvergeWithPostCond.var_iff:
    ConvergeWithPostCond Γ st (.var x) Q ↔
    Q st x := by
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro_cases
    casesm BigStepAux _ _ _ _ _ _
    assumption
  · intro_cases
    tauto

-- theorem ConvergeWithPostCond.var_value_iff (hp : sc x = some (.value v)):
--     ConvergeWithPostCond Γ st sc (.expr (.var x)) Q ↔
--     Q st sc v := by
--   simp [ConvergeWithPostCond]
--   apply Iff.intro
--   · intro_cases
--     subst_vars
--     rename _ ∨ _ => hp
--     simp_all
--   · intro_cases
--     subst_vars
--     tauto

def BuiltinCWPC (argTypes : List Tp) (resType : Tp) (b : Builtin) (as : HList (InstanceOf P) argTypes) (Q : InstanceOf P resType → Prop): Prop :=
  ∃r, BigStepBuiltin P argTypes resType b as r ∧ Q r

theorem ConvergeWithPostCond.callBuiltin_iff:
    ConvergeWithPostCond Γ st (.call intps outtp (.builtin b) args) Q ↔
    ArgsWPC Γ st args (fun st' args => BuiltinCWPC intps outtp b args fun v => Q st' v) := by
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
    apply BigStepAux.callBuiltin <;> assumption
    assumption

theorem ConvergeWithPostCond.callArgsPrepDoneBuiltin_iff:
    ConvergeWithPostCond Γ st (.callArgPrep (.builtin b) as []) Q ↔
    BuiltinCWPC b as (fun r => Q st r) := by
  simp [ConvergeWithPostCond, BuiltinCWPC]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

def CallWithPostCond (Γ : Env) (st : State P) (f : Function) (args : Mathlib.Vector (Value P) f.1) (Q : State P → Value P → Prop): Prop :=
  ConvergeWithPostCond Γ st (.expr (f.2 _ _ args)) Q

theorem ConvergeWithPostCond.callArgPrepDeclDone_iff (hpr : Γ fName = some f) (hpl : args.length = f.1):
    ConvergeWithPostCond Γ st (.callArgPrep (.decl fName) args []) Q ↔
    CallWithPostCond Γ st f ⟨args, hpl⟩ Q := by
  unfold CallWithPostCond
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro_cases
    casesm (BigStepAux _ _ _ _ _ _)
    rw [hpr] at *
    rename (some _ = some _) => hp
    cases hp
    repeat apply Exists.intro
    apply And.intro (by assumption) (by assumption)
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    · apply BigStepAux.callArgPrepDeclDone <;> assumption
    · assumption

theorem BuiltinCWPC.eq_iff :
    BuiltinCWPC (P := P) [tp, tp] .bool .eq h![a, b] Q ↔ Q (a == b) := by
  unfold BuiltinCWPC
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    assumption
  · intro
    apply Exists.intro
    apply And.intro
    apply BigStepBuiltin.eq
    assumption


theorem BuiltinCWPC.assert_iff :
  BuiltinCWPC [.bool] .unit .assert h![p] Q ↔ p ∧ Q ():= by
  simp [BuiltinCWPC]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem BuiltinCWPC.sub_u_iff :
  BuiltinCWPC .sub [⟨.u n, a⟩, ⟨.u n, b⟩] Q ↔ b.val ≤ a.val ∧ Q ⟨.u n, a - b⟩ := by
  simp [BuiltinCWPC, and_assoc]

theorem BuiltinCWPC.add_u_iff :
  BuiltinCWPC .add [⟨.u n, a⟩, ⟨.u n, b⟩] Q ↔ a.val + b.val < 2 ^ n ∧ Q ⟨.u n, a + b⟩ := by
  simp [BuiltinCWPC, and_assoc]

theorem BuiltinCWPC.fresh_iff :
  BuiltinCWPC [] tp .fresh h![] Q ↔ ∃v, Q v := by
  unfold BuiltinCWPC; tauto

def IteWPC (Γ : Env) (st : State P) (b : Value P) (t e : Expr' (Value P) Nat) (Q : State P → Value P → Prop): Prop :=
    (b = ⟨.bool, true⟩ ∧ ConvergeWithPostCond Γ st (.expr t) Q) ∨
    (b = ⟨.bool, false⟩ ∧ ConvergeWithPostCond Γ st (.expr e) Q)

theorem ConvergeWithPostCond.ite_iff:
    ConvergeWithPostCond Γ st (.expr (.ite b t e)) Q ↔
    ConvergeWithPostCond Γ st (.expr b) (fun st' v => IteWPC Γ st' v t e Q) := by
  simp [ConvergeWithPostCond, IteWPC]
  apply Iff.intro
  · intro_cases
    rename BigStepAux _ _ _ _ _ _ => h
    cases h <;> {
      repeat apply Exists.intro
      apply And.intro (by assumption)
      simp only [Value.mk.injEq, heq_eq_eq, Bool.true_eq_false, true_and, false_and, false_or, or_false]
      repeat apply Exists.intro
      apply And.intro <;> assumption
    }
  · intro_cases
    casesm* _ ∨ _ <;> {
      casesm* _ ∧ _, ∃ _, _
      subst_vars
      repeat apply Exists.intro
      apply And.intro
      · try (apply BigStepAux.iteTrue <;> assumption)
        try (apply BigStepAux.iteFalse <;> assumption)
      · assumption
    }

theorem IteWPC.iff_true (hb : b = true):
    IteWPC Γ st ⟨.bool, b⟩ t e Q ↔ ConvergeWithPostCond Γ st (.expr t) Q := by
  simp [IteWPC, hb]

theorem IteWPC.iff_false (hb : b = false):
    IteWPC Γ st ⟨.bool, b⟩ t e Q ↔ ConvergeWithPostCond Γ st (.expr e) Q := by
  simp [IteWPC, hb]

theorem ConvergeWithPostCond.lit_field_iff : ConvergeWithPostCond (P:=P) Γ st (.expr (.lit v .field)) Q ↔ Q st ⟨.field, (v : ZMod P)⟩ := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

theorem ConvergeWithPostCond.lit_u_iff : ConvergeWithPostCond (P:=P) Γ st (.expr (.lit v (.u n))) Q ↔ Q st ⟨.u n, (v : U n)⟩ := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

-- theorem BigStepAux

theorem Mathlib.Vector.get_mk_zero: get (⟨a :: as, h⟩ : Vector α (n + 1)) 0 = a := by
  simp [Mathlib.Vector.get]

theorem Mathlib.Vector.get_mk_cons {n : Nat} {a b : α} {as : List α} {h : (a :: b :: as).length = n.succ.succ}:
    Mathlib.Vector.get (⟨a :: (b :: as), h⟩ : Vector α n.succ.succ) (@OfNat.ofNat (Fin n.succ.succ) (Nat.succ i) _) = get (⟨b :: as, by simp_all⟩ : Vector α n.succ) (OfNat.ofNat i) := by

  -- simp [Mathlib.Vector.get, OfNat.ofNat]
  sorry

syntax "nr_simp_wip" : tactic
macro_rules
|`(tactic|nr_simp_wip) => `(tactic|
  simp (disch := (first | noir_simp_discharge | decide)) [
    -- true_and,
    -- and_true,
    -- ConvergeWithPostCond.of_BigStepAux,
    -- ConvergeWithPostCond.blockNext_iff,
    ConvergeWithPostCond.letIn_iff,
    ConvergeWithPostCond.seq_iff,

    -- ConvergeWithPostCond.fresh_iff,
    ConvergeWithPostCond.callDecl_iff,
    ConvergeWithPostCond.callBuiltin_iff,

    ArgsWPC.nil_iff,
    ArgsWPC.cons_iff,
    -- ConvergeWithPostCond.callArgPrepNext_iff,
    ConvergeWithPostCond.var_iff,
    -- ConvergeWithPostCond.callArgsPrepDoneBuiltin_iff,
    -- ConvergeWithPostCond.blockDone_iff,
    -- List.nil_append,
    -- List.cons_append,
    -- List.indexOf_cons_ne,
    -- List.indexOf_cons_eq,
    -- List.get!_cons_succ,
    -- List.get!_cons_zero,
    -- decide_eq_true_iff,
    BuiltinCWPC.eq_iff,
    BuiltinCWPC.assert_iff,
    -- BuiltinCWPC.add_u_iff,
    -- BuiltinCWPC.sub_u_iff,
    BuiltinCWPC.fresh_iff,
    -- Mathlib.Vector.get_mk_cons,
    -- Mathlib.Vector.get_mk_zero,
    -- ConvergeWithPostCond.ite_iff,
    -- IteWPC.iff_true,
    -- IteWPC.iff_false,
    -- ConvergeWithPostCond.lit_field_iff,
    -- ConvergeWithPostCond.lit_u_iff,

  ]
)


theorem assignableEq:
  ConvergeWithPostCond (Lampe.Env.ofModule testMod) st (assertEq.2.2 h![a, b]) Q ↔
  a = b ∧ Q st () := by
  unfold assertEq
  nr_simp_wip


theorem assignableRecursiveMul [Fact (Nat.Prime P)]:
    ConvergeWithPostCond (P := P) (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "recursiveMul") [⟨.u 64, a⟩, ⟨.u 64, b⟩] []) Q ↔
    (a.val * b.val < 2 ^ 64) ∧ Q st sc ⟨.u 64, a * b⟩ := by
  rcases a with ⟨a, ha⟩
  induction a generalizing sc Q with
  | zero =>
      simp (disch := noir_simp_discharge) only [
        ConvergeWithPostCond.callArgPrepDeclDone_iff,
      ]
      simp only [CallWithPostCond]
      nr_simp_wip
      simp
  | succ a ih =>
      simp (disch := noir_simp_discharge) only [
        ConvergeWithPostCond.callArgPrepDeclDone_iff,
      ]
      simp only [CallWithPostCond]
      have : decide (Value.mk (P := P) (.u 64) ⟨a + 1, ha⟩ = ⟨.u 64, 0⟩) = false := by
        simp
        rintro ⟨rfl⟩
      nr_simp_wip
      have : (Fin.mk (a + 1) ha) - ↑1 = Fin.mk a (by linarith) := by
        conv_lhs => whnf
        conv_rhs => whnf
        simp_arith
        linarith
      have : a < 2 ^ 64 := by linarith
      simp only [Nat.cast_one, *]
      nr_simp_wip




  -- noir_simp only
  -- crush
  -- induction a generalizing sc sc' v with
  -- | zero =>
  --   unfold BigStepCall
  --   crush
  --   tauto
  -- | succ a ih =>
  --   have ap1_def : (⟨a + 1, ha⟩ : ZMod (p+1)) = (⟨a, by linarith⟩) + 1 := by
  --     congr
  --     repeat (rw [Nat.mod_eq_of_lt] <;> try linarith)

  --   have : (⟨a, by linarith⟩: ZMod (p+1)) + 1 ≠ 0 := by
  --     intro h
  --     injection h with h
  --     repeat rw [Nat.mod_eq_of_lt] at h
  --     any_goals linarith
  --     rw [Nat.mod_eq_of_lt]
  --     any_goals linarith

  --   noir_simp only [this, ap1_def, ih]
  --   unfold BigStepCall
  --   crush
  --   simp only [this, ap1_def, ih]
  --   crush
  --   simp only [this, ap1_def, ih]
  --   crush
  --   ring_nf
  --   tauto

  -- crush
  -- tauto

example :
    ∃st' sc', BigStepAux 17 (stdlib.extend (Lampe.Env.ofModule testMod)) st sc (.callArgPrep (.decl "lt_fallback") [⟨.field, 10⟩, ⟨.field, 5⟩] []) st' sc' ⟨.bool, true⟩ := by
  simp (disch := with_unfolding_all rfl) only [BigStepAux.callArgPrepDeclDone_iff3]
  unfold BigStepCall
  crush
  simp [Field.numBits, Nat.log2]
  conv in (occs := *) (Fin.val _ / Fin.val _) => whnf
  simp [BigStepAux.loopCont_iff]
  crush
  apply And.intro
  · decide
  · apply Exists.intro
    use [10]
    crush
    apply And.intro (by decide)
    use [22]
    crush
    apply And.intro (by decide)
    apply And.intro rfl
    simp [State.alloc, State.set]
