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


#check HList.below
#check HList.brecOn
#check HList.casesOn
#check HList.rec

def testHListCasesOn : HList α [] → Nat
| h![] => 0

set_option pp.match false

#print testHListCasesOn
#print testHListCasesOn.match_1

def testHListCasesOn2 : HList α [] → Nat :=
fun l => HList.casesOn (motive := fun a) l 17 (fun _ _ => nomatch)

def assertEq : Lampe.Function := {
  generics := []
  inTps := fun _ => [.field, .field]
  outTp := fun _ => .unit
  body := fun _ => fun h![] => fun h![a, b] =>
    .letIn (.call h![] [] .field (.builtin .fresh) h![]) fun f =>
      .seq
        (.call h![] [.bool] .unit (.builtin .assert) h![
          .call h![] [.field, .field] .bool (.builtin .eq) h![.var f, .var a]
        ])
        (.call h![] [.bool] .unit (.builtin .assert) h![
          .call h![] [.field, .field] .bool (.builtin .eq) h![.var f, .var b]
        ])
}

#print assertEq

def recursiveMul : Lampe.Function := {
  generics := []
  inTps := fun _ => [.u 64, .u 64]
  outTp := fun _ => .u 64
  body := fun _ => fun h![] => fun h![n, k] =>
    .ite
      (.call h![] [.u 64, .u 64] .bool (.builtin .eq) h![.var n, .lit (.u 64) 0])
      (.lit (.u 64) 0)
      (.letIn (.call h![] [.u 64, .u 64] (.u 64) (.builtin .sub) h![.var n, .lit (.u 64) 1]) fun n =>
        .call h![] [.u 64, .u 64] (.u 64) (.builtin .add) h![
          .var k,
          .call h![] [.u 64, .u 64] (.u 64) (.decl "recursiveMul") h![.var n, .var k]
        ]
      )

}

def testMod : Lampe.Module := ⟨[⟨"assertEq", assertEq⟩, ⟨"recursiveMul", recursiveMul⟩]⟩

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

def ConvergeWithPostCond (Γ : Env) (st : State P) (e : Expr' (ClosedType.denote P) tp) (Q : State P → (tp.denote P) → Prop) : Prop :=
  ∃st' v, BigStepAux P Γ st e st' v ∧ Q st' v

def ArgsWPC {atps : List ClosedType} (Γ : Env) (st : State P) (es : HListI (Expr' (ClosedType.denote P)) atps) (Q: State P → HListI (ClosedType.denote P) atps → Prop): Prop :=
  ∃st' vs, BigStepArgs P Γ st es st' vs ∧ Q st' vs

theorem ArgsWPC.nil_iff:
    ArgsWPC Γ st HListI.nil Q ↔ Q st HListI.nil := by
  simp [ArgsWPC]
  apply Iff.intro
  · intro_cases
    casesm BigStepArgs _ _ _ _ _ _
    tauto
  · intro_cases
    tauto

theorem ArgsWPC.cons_iff:
    ArgsWPC Γ st (HListI.cons e es) Q ↔
    ConvergeWithPostCond Γ st e (fun st' v => ArgsWPC Γ st' es (fun st' vs => Q st' (HListI.cons v vs))) := by
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
  {P} {generics : HListI PrimKind.denote tyKinds} {args : HListI (Expr' (ClosedType.denote P)) inTps} {Q : State P → ClosedType.denote P outTp → Prop} {st : State P}
  (hlookup : Γ fname = some fn)
  (hc : fn.generics = tyKinds)
  (htci : fn.inTps (hc ▸ generics) = inTps)
  (htco : fn.outTp (hc ▸ generics) = outTp):
    ConvergeWithPostCond Γ st (.call generics inTps outTp (.decl fname) args) Q ↔
    ArgsWPC Γ st args (fun st' vs =>
      ConvergeWithPostCond Γ st' (htco ▸ fn.body _ (hc ▸ generics) (htci ▸ vs)) Q) := by
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
    rcases fn
    cases htci
    cases htco
    rcases hc
    repeat apply Exists.intro
    apply And.intro
    apply BigStepAux.callDecl
    assumption
    assumption
    rotate_left
    rfl
    rfl
    rfl
    assumption
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

-- (inp: List ClosedType) → (out : ClosedType) → Builtin → HListI (ClosedType.denote P) inp

def BuiltinCWPC (argTypes : List ClosedType) (resType : ClosedType) (b : Builtin) (as : HListI (ClosedType.denote P) argTypes) (Q : ClosedType.denote P resType → Prop): Prop :=
  ∃r, BigStepBuiltin P argTypes resType b as r ∧ Q r

theorem ConvergeWithPostCond.callBuiltin_iff:
    ConvergeWithPostCond Γ st (@Expr'.call _ [] HListI.nil intps outtp (.builtin b) args) Q ↔
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

theorem BuiltinCWPC.eq_f_iff :
    BuiltinCWPC (P := P) [.field, .field] .bool .eq h![a, b] Q ↔ Q (a == b) := by
  unfold BuiltinCWPC
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    assumption
  · intro
    apply Exists.intro
    apply And.intro
    apply BigStepBuiltin.eqF
    assumption

theorem BuiltinCWPC.eq_u_iff :
    BuiltinCWPC (P := P) [.u n, .u n] .bool .eq h![a, b] Q ↔ Q (a == b) := by
  unfold BuiltinCWPC
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    assumption
  · intro
    apply Exists.intro
    apply And.intro
    apply BigStepBuiltin.eqU
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
  BuiltinCWPC [.u n, .u n] (.u n) .sub h![a, b] Q ↔ b.val ≤ a.val ∧ Q (a - b) := by
  simp [BuiltinCWPC, and_assoc]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem BuiltinCWPC.add_u_iff :
  BuiltinCWPC [.u n, .u n] (.u n) .add h![a, b] Q ↔ a.val + b.val < 2^n ∧ Q (a + b) := by
  simp [BuiltinCWPC, and_assoc]
  apply Iff.intro
  · intro_cases
    casesm BigStepBuiltin _ _ _ _ _ _
    tauto
  · intro_cases
    subst_vars
    tauto

theorem BuiltinCWPC.fresh_iff :
  BuiltinCWPC [] tp .fresh HListI.nil Q ↔ ∃v, Q v := by
  unfold BuiltinCWPC; tauto

def IteWPC (Γ : Env) (st : State P) (b : Bool) (t e : Expr' (ClosedType.denote P) a) (Q : State P → ClosedType.denote P a → Prop): Prop :=
    (b ∧ ConvergeWithPostCond Γ st t Q) ∨
    (!b ∧ ConvergeWithPostCond Γ st e Q)

theorem ConvergeWithPostCond.ite_iff:
    ConvergeWithPostCond Γ st (.ite b t e) Q ↔
    ConvergeWithPostCond Γ st b (fun st' v => IteWPC Γ st' v t e Q) := by
  simp [ConvergeWithPostCond, IteWPC]
  apply Iff.intro
  · intro_cases
    rename BigStepAux _ _ _ _ _ _ => h
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
      · try (apply BigStepAux.iteTrue <;> assumption)
        try (apply BigStepAux.iteFalse <;> assumption)
      · assumption
    }

theorem IteWPC.iff_true (hb : b = true):
    IteWPC Γ st b t e Q ↔ ConvergeWithPostCond Γ st t Q := by
  simp [IteWPC, hb]

theorem IteWPC.iff_false (hb : b = false):
    IteWPC Γ st b t e Q ↔ ConvergeWithPostCond Γ st e Q := by
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

theorem ConvergeWithPostCond.lit_u_iff : ConvergeWithPostCond (P:=P) Γ st  (.lit (.u n) v ) Q ↔ Q st v := by
  simp only [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    casesm BigStepAux _ _ _ _ _ _
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
  simp (disch := (first | noir_simp_discharge | decide)) only [
    -- true_and,
    -- and_true,
    -- ConvergeWithPostCond.of_BigStepAux,
    -- ConvergeWithPostCond.blockNext_iff,
    ConvergeWithPostCond.callBuiltin_iff,
    ConvergeWithPostCond.callDecl_iff,
    ConvergeWithPostCond.ite_iff,
    ConvergeWithPostCond.letIn_iff,
    ConvergeWithPostCond.lit_u_iff,
    ConvergeWithPostCond.seq_iff,
    ConvergeWithPostCond.var_iff,



    ArgsWPC.nil_iff,
    ArgsWPC.cons_iff,
    -- ConvergeWithPostCond.callArgPrepNext_iff,
    -- ConvergeWithPostCond.callArgsPrepDoneBuiltin_iff,
    -- ConvergeWithPostCond.blockDone_iff,
    -- List.nil_append,
    -- List.cons_append,
    -- List.indexOf_cons_ne,
    -- List.indexOf_cons_eq,
    -- List.get!_cons_succ,
    -- List.get!_cons_zero,
    -- decide_eq_true_iff,
    -- BuiltinCWPC.assert_iff,
    BuiltinCWPC.add_u_iff,
    BuiltinCWPC.assert_iff,
    BuiltinCWPC.eq_f_iff,
    BuiltinCWPC.eq_u_iff,
    BuiltinCWPC.fresh_iff,
    BuiltinCWPC.sub_u_iff,

    -- Mathlib.Vector.get_mk_cons,
    -- Mathlib.Vector.get_mk_zero,
    IteWPC.iff_true,
    IteWPC.iff_false,
    -- ConvergeWithPostCond.lit_field_iff,

  ]
)


theorem assignableEq:
  ConvergeWithPostCond (Lampe.Env.ofModule testMod) st (assertEq.body _ h![] h![a, b]) Q ↔
  a = b ∧ Q st () := by
  simp only [assertEq]
  nr_simp_wip
  simp


theorem Fin.succ_mul : Fin.succ a * b = b + a.castSucc * b := by
  cases a
  cases b
  conv => lhs; whnf
  conv => rhs; whnf
  simp_arith [Nat.add_mul, add_comm]


theorem Fin.castSucc_val : Fin.val (Fin.castSucc a) = a := by
  rfl

theorem Fin.succ_val : Fin.val (Fin.succ a) = a.val + 1 := by
  rfl

theorem assignableRecursiveMul [Fact (Nat.Prime P)]:
    ConvergeWithPostCond (P := P) (Lampe.Env.ofModule testMod) st (recursiveMul.body _ h![] h![a, b]) Q ↔
    (a.val * b.val < 2 ^ 64) ∧ Q st (a * b) := by
  induction a using Fin.induction generalizing Q with
  | zero =>
      simp only [recursiveMul]
      nr_simp_wip
      simp
  | succ a ih =>
      simp only [recursiveMul]
      nr_simp_wip
      have : a.succ - Nat.cast 1 = a.castSucc := by
        cases a
        conv => lhs; whnf
        conv => rhs; whnf
        simp_arith
        linarith
      simp only [this, ih, Fin.mul_def, Fin.add_def, Fin.castSucc_val, Fin.succ_val]
      simp_arith [Nat.add_mul, Nat.add_comm]
      apply Iff.intro
      · intro_cases
        apply And.intro <;> try assumption
        rename _ + _ * _ % _ ≤ _ => h
        rw [Nat.mod_eq_of_lt] at h <;> linarith
      · intro_cases
        apply And.intro (by linarith)
        apply And.intro
        · rw [Nat.mod_eq_of_lt] <;> linarith
        · assumption

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
