import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq Lampe.STHoare

initialize
  Lean.registerTraceClass `Lampe.SL
  Lean.registerTraceClass `Lampe.STHoare.Helpers

inductive SLTerm where
| top : SLTerm
| star : Expr → SLTerm → SLTerm → SLTerm
| lift : Expr → SLTerm
| singleton : Expr → Expr → SLTerm
| lmbSingleton : Expr → Expr → SLTerm
| mvar : Expr → SLTerm
| all : Expr → SLTerm
| exi : Expr → SLTerm
| wand : SLTerm → SLTerm → SLTerm
| unrecognized : Expr → SLTerm

def SLTerm.toString : SLTerm → String
| top => "⊤"
| wand a b => s!"{a.toString} -⋆ {b.toString}"
| exi e => s!"∃∃ {e}"
| all e => s!"∀∀ {e}"
| star _ a b => s!"({a.toString} ⋆ {b.toString})"
| lift e => s!"⟦{e.dbgToString}⟧"
| singleton e₁ _ => s!"[{e₁.dbgToString} ↦ _]"
| lmbSingleton e₁ _ => s!"[λ {e₁.dbgToString} ↦ _]"
| mvar e => s!"MV{e.dbgToString}"
| unrecognized e => s!"<unrecognized: {e.dbgToString}>"

def SLTerm.printShape : SLTerm → String
| SLTerm.top => "⊤"
| wand a b => s!"({a.printShape} -⋆ {b.printShape})"
| exi e => s!"(∃∃)"
| all e => s!"(∀∀)"
| star _ a b => s!"({a.printShape} ⋆ {b.printShape})"
| lift e => s!"⟦⟧"
| singleton e₁ _ => s!"[_ ↦ _]"
| lmbSingleton e₁ _ => s!"[λ _ ↦ _]"
| mvar e => s!"MV"
| unrecognized e => s!"<unrecognized>"



def SLTerm.isMVar : SLTerm → Bool
| SLTerm.mvar _ => true
| _ => false

def SLTerm.isTop : SLTerm → Bool
| SLTerm.top => true
| _ => false

def SLTerm.isForAll : SLTerm → Bool
| SLTerm.all _ => true
| _ => false

instance : ToString SLTerm := ⟨SLTerm.toString⟩

instance : Inhabited SLTerm := ⟨SLTerm.top⟩

theorem star_exists [LawfulHeap α] {P : SLP α} {Q : β → SLP α} : ((∃∃x, Q x) ⋆ P) = (∃∃x, Q x ⋆ P) := by
  unfold SLP.exists' SLP.star
  funext st
  simp
  tauto

theorem exists_star [LawfulHeap α] {P : SLP α} {Q : β → SLP α} : ((∃∃x, Q x) ⋆ P) = (∃∃x, P ⋆ Q x) := by
  rw [star_exists]
  simp [SLP.star_comm]

theorem Lampe.STHoare.litU_intro: STHoare p Γ ⟦⟧ (.litNum (.u s) n) fun v => v = n := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem Lampe.STHoare.litField_intro: STHoare p Γ ⟦⟧ (.litNum .field n) fun v => v = n := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem Lampe.STHoare.litStr_intro: STHoare p Γ ⟦⟧ (.litStr u s) fun v => v = s := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem Lampe.STHoare.fmtStr_intro : STHoare p Γ ⟦⟧ (.fmtStr u tps s) fun v => v = s := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem Lampe.STHoare.litFalse_intro: STHoare p Γ ⟦⟧ (.litNum .bool 0) fun v => v = false := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem Lampe.STHoare.litTrue_intro: STHoare p Γ ⟦⟧ (.litNum .bool 1) fun v => v = true := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem Lampe.STHoare.litUnit_intro: STHoare p Γ ⟦⟧ (.litNum .unit n) fun v => v = unit := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem ref_intro' {p} {x : Tp.denote p tp} {Γ P}:
    STHoare p Γ P (.ref x) fun v => [v ↦ ⟨tp, x⟩] ⋆ P := by
  apply ramified_frame_top
  apply ref_intro
  simp
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  rw [SLP.star_comm, ←SLP.star_assoc]
  apply SLP.ent_star_top


theorem Lampe.SLP.skip_fst : (R₁ ⊢ Q ⋆ X) → ([a ↦ b] ⋆ X ⊢ R₂) → ([a ↦ b] ⋆ R₁ ⊢ Q ⋆ R₂) := by
  intro h₁ h₂
  apply entails_trans
  rotate_left
  apply star_mono_l
  apply h₂
  apply entails_trans
  apply star_mono_l
  apply h₁
  rw [SLP.star_comm, SLP.star_assoc]
  apply star_mono_l
  rw [SLP.star_comm]
  apply entails_self

theorem Lampe.SLP.skip_fst' : (⟦⟧ ⊢ Q ⋆ X) → ([a ↦ b] ⋆ X ⊢ R₂) → ([a ↦ b] ⊢ Q ⋆ R₂) := by
  intro h₁ h₂
  rw [←SLP.star_true (H:=[a ↦ b])]
  apply Lampe.SLP.skip_fst
  assumption
  assumption

theorem Lampe.SLP.entails_star_true [LawfulHeap α] {H : SLP α} : H ⊢ H ⋆ ⟦⟧ := by
  simp [SLP.entails_self]

theorem SLP.eq_of_iff [LawfulHeap α] {P Q : SLP α} : (P ⊢ Q) → (Q ⊢ P) → P = Q := by
  intros
  apply funext
  intro
  apply eq_iff_iff.mpr
  apply Iff.intro <;> apply_assumption

theorem exi_pure [LawfulHeap α] {P : β → Prop} : (SLP.exists' fun x =>  ⟦P x⟧) = SLP.lift (α := α) (∃x, P x) := by
  unfold SLP.exists' SLP.lift
  simp

theorem pluck_pure_l {P : Prop} : ([a ↦ b] ⋆ P) = (P ⋆ [a ↦ b]) := by
  simp [SLP.star_comm]

theorem pluck_pure_all_l [LawfulHeap α] {P : Prop} {f : β → SLP α} : (SLP.forall' f ⋆ P) = (P ⋆ SLP.forall' f) := by
  simp [SLP.star_comm]

theorem pluck_pure_exi_l [LawfulHeap α] {P : Prop} {f : β → SLP α} : (SLP.exists' f ⋆ P) = (P ⋆ SLP.exists' f) := by
  simp [SLP.star_comm]

theorem pluck_pure_l_assoc {P : Prop} {Q : SLP (State p)} : ([a ↦ b] ⋆ P ⋆ Q) = (P ⋆ [a ↦ b] ⋆ Q) := by
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.eq_of_iff <;> {apply SLP.star_mono_l; rw [SLP.star_comm]; apply SLP.entails_self}

theorem pluck_pure_l_exi_assoc {P : Prop} {Q : SLP (State p)} : (SLP.exists' f ⋆ P ⋆ Q) = (P ⋆ SLP.exists' f ⋆ Q) := by
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.eq_of_iff <;> {apply SLP.star_mono_l; rw [SLP.star_comm]; apply SLP.entails_self}

theorem SLP.pure_star_pure [LawfulHeap α] {P Q : Prop} : (P ⋆ Q) = (⟦P ∧ Q⟧ : SLP α) := by
  unfold SLP.star SLP.lift
  funext st
  apply eq_iff_iff.mpr
  apply Iff.intro
  · intro_cases
    simp_all
  · intro_cases
    use ∅, ∅
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    apply LawfulHeap.disjoint_empty
    all_goals simp_all [LawfulHeap.disjoint_empty]

macro "h_norm" : tactic => `(tactic|(
  try simp only [SLP.star_assoc,
    pluck_pure_l, pluck_pure_l_assoc, pluck_pure_all_l, pluck_pure_exi_l, pluck_pure_l_exi_assoc,
    SLP.star_true, SLP.true_star, exi_pure];
  -- repeat (apply STHoare.pure_left; intro_cases);
  -- repeat (apply SLP.pure_left; intro_cases);
  subst_vars;
))

theorem SLP.pure_leftX [LawfulHeap α] {H Q R : SLP α} : (P → (H ⊢ Q ⋆ R)) → (P ⋆ H ⊢ Q ⋆ P ⋆ R) := by
  intro
  apply SLP.pure_left
  intro
  rw [SLP.star_comm]
  rw [SLP.star_assoc]
  apply SLP.pure_right
  tauto
  rw [SLP.star_comm]
  tauto

/-- only finisher, will waste mvars for top! -/
theorem SLP.pure_ent_star_top [LawfulHeap α] : (P → Q) → ((P : SLP α) ⊢ Q ⋆ ⊤) := by
  intro h st hp
  rcases hp with ⟨_, rfl, hp⟩
  use ∅, ∅
  refine ⟨?_, ?_, ?_, ?_⟩
  apply LawfulHeap.disjoint_empty
  all_goals simp_all [LawfulHeap.disjoint_empty, SLP.lift]

theorem star_mono_l_sing : (P ⊢ Q) → (v₁ = v₂) → ([r ↦ v₁] ⋆ P ⊢ [r ↦ v₂] ⋆ Q) := by
  intro h₁ h₂
  rw [h₂]
  apply SLP.star_mono_l
  apply h₁

theorem star_mono_l_sing' : (⟦⟧ ⊢ Q) → (v₁ = v₂) → ([r ↦ v₁] ⊢ [r ↦ v₂] ⋆ Q) := by
  intro h₁ h₂
  rw [h₂]
  apply SLP.star_mono_l'
  apply h₁

partial def extractTripleExpr (e: Expr): TacticM (Option Expr) := do
  if e.isAppOf ``STHoare then
    let args := e.getAppArgsN 5
    return args[3]?
  else return none

def isLetIn (e : Expr) : Bool := e.isAppOf ``Lampe.Expr.letIn

def getLetInVarName (e : Expr) : TacticM (Option Name) := do
  let args := Expr.getAppArgs e
  let body := args[4]!
  match body with
  | Lean.Expr.lam n _ _ _ => return some n
  | _ => return none

#check Expr.letIn


def builtinLemmas : List Name :=
  [ ``Lampe.STHoare.litU_intro
  , ``Lampe.STHoare.litField_intro
  , ``Lampe.STHoare.litStr_intro
  , ``Lampe.STHoare.fmtStr_intro
  , ``Lampe.STHoare.litTrue_intro
  , ``Lampe.STHoare.litFalse_intro
  , ``Lampe.STHoare.litUnit_intro
  , ``fn_intro
  , ``fresh_intro
  , ``assert_intro
  , ``skip_intro
  , ``lam_intro
  , ``cast_intro
  -- memory
  , ``var_intro
  , ``ref_intro
  , ``readRef_intro
  , ``writeRef_intro
  -- array
  -- , ``mkArray_intro
  , ``arrayLen_intro
  , ``arrayIndex_intro
  , ``arrayAsSlice_intro
  -- slice
  , ``mkSlice_intro
  , ``sliceLen_intro
  , ``sliceIndex_intro
  , ``slicePushBack_intro
  -- equality
  , ``unitEq_intro
  , ``bEq_intro
  , ``fEq_intro
  , ``uEq_intro
  , ``iEq_intro
  , ``bigIntEq_intro
  , ``strEq_intro
  -- negation
  , ``fNeg_intro
  , ``iNeg_intro
  -- addition
  , ``fAdd_intro
  , ``uAdd_intro
  , ``iAdd_intro
  , ``bigIntAdd_intro
  -- subtraction
  , ``fSub_intro
  , ``uSub_intro
  , ``iSub_intro
  , ``bigIntSub_intro
  -- division
  , ``fDiv_intro
  , ``uDiv_intro
  , ``iDiv_intro
  , ``bigIntDiv_intro
  -- multiplication
  , ``fMul_intro
  , ``uMul_intro
  , ``iMul_intro
  , ``bigIntMul_intro
  -- remainder
  , ``uRem_intro
  , ``iRem_intro
  -- struct
  , ``mkTuple_intro
  , ``projectTuple_intro
  -- lens
  , ``modifyLens_intro
  , ``getLens_intro
  -- bitwise
  , ``uShr_intro
  , ``uShl_intro
  , ``uOr_intro
  , ``uAnd_intro
  , ``uXor_intro
  ]

def getClosingTerm (val : Expr) : TacticM (Option (TSyntax `term × Bool)) := do
  let head := val.getAppFn
  match head with
  | Lean.Expr.const n _ =>
    match n with
    | ``Expr.var => return some (←``(var_intro), true)
    | ``Expr.mkTuple => return some (←``(genericTotalPureBuiltin_intro (a := (_,_)) Builtin.mkTuple rfl), true)
    | ``Expr.mkArray =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := ($size, _)) rfl), true)
    | ``Expr.mkRepArray =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := ($size, _)) rfl), true)
    | ``Expr.getLens => return some (←``(getLens_intro), false)
    | ``Expr.modifyLens => return some (←``(modifyLens_intro), false)
    | ``Lampe.Expr.fn => return some (←``(fn_intro), true)
    | ``Lampe.Expr.callBuiltin =>
      let some builtin := val.getAppArgs[3]? | throwError "malformed builtin"
      let builtinName := builtin.getAppFn
      match builtinName with
      | Lean.Expr.const n _ =>
        match n with
        | ``Lampe.Builtin.uNot => return some (←``(genericTotalPureBuiltin_intro Builtin.uNot rfl), true)
        | ``Lampe.Builtin.uAnd => return some (←``(genericTotalPureBuiltin_intro Builtin.uAnd rfl), true)
        | ``Lampe.Builtin.uOr => return some (←``(genericTotalPureBuiltin_intro Builtin.uOr rfl), true)
        | ``Lampe.Builtin.uXor => return some (←``(genericTotalPureBuiltin_intro Builtin.uXor rfl), true)
        | ``Lampe.Builtin.uShl => return some (←``(genericTotalPureBuiltin_intro Builtin.uShl rfl), true)
        | ``Lampe.Builtin.uShr => return some (←``(genericTotalPureBuiltin_intro Builtin.uShr rfl), true)

        | ``Lampe.Builtin.cast => return some (←``(cast_intro), true)

        | ``Lampe.Builtin.fAdd => return some (←``(genericTotalPureBuiltin_intro Builtin.fAdd rfl (a := ())), true)
        | ``Lampe.Builtin.fMul => return some (←``(genericTotalPureBuiltin_intro Builtin.fMul rfl (a := ())), true)
        | ``Lampe.Builtin.fSub => return some (←``(genericTotalPureBuiltin_intro Builtin.fSub rfl (a := ())), true)
        | ``Lampe.Builtin.fNeg => return some (←``(genericTotalPureBuiltin_intro Builtin.fNeg rfl (a := ())), true)

        | ``Lampe.Builtin.uAdd => return some (←``(uAdd_intro), false)

        | ``Lampe.Builtin.mkArray => return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray rfl), true)
        | ``Lampe.Builtin.arrayIndex => return some (←``(arrayIndex_intro), false)
        | ``Lampe.Builtin.arrayLen => return some (←``(genericTotalPureBuiltin_intro Builtin.arrayLen rfl), true)
        | ``Lampe.Builtin.arrayAsSlice => return some (←``(genericTotalPureBuiltin_intro Builtin.arrayAsSlice (a := (_,_)) rfl), true)
        | _ => return none
      | _ => return none
    | ``Lampe.Expr.ref => return some (←``(ref_intro), false)
    | ``Lampe.Expr.readRef => return some (←``(readRef_intro), false)
    | ``Lampe.Expr.litNum =>
      let some vtp := val.getAppArgs[1]? | throwError "malformed litNum"
      let  Lean.Expr.const vtp _ := vtp.getAppFn | throwError "malformed litNum"
      match vtp with
      | ``Tp.field => return some (←``(litField_intro), true)
      | ``Tp.u => return some (←``(litU_intro), true)
      | _ => return none
    | _ => return none

  | _ => pure none

def getLetInHeadClosingTheorem (e : Expr) : TacticM (Option (TSyntax `term × Bool)) := do
  let args := Expr.getAppArgs e
  let some val := args[3]? | throwError "malformed letIn"
  getClosingTerm val

def isIte (e : Expr) : Bool := e.isAppOf `Lampe.Expr.ite

partial def parseSLExpr (e: Expr): TacticM SLTerm := do
  if e.isAppOf ``SLP.star then
    let args := e.getAppArgs
    let fst ← parseSLExpr (←liftOption args[2]?)
    let snd ← parseSLExpr (←liftOption args[3]?)
    return SLTerm.star e fst snd
  if e.isAppOf ``State.valSingleton then
    let args := e.getAppArgs
    let fst ← liftOption args[1]?
    let snd ← liftOption args[2]?
    return SLTerm.singleton fst snd
  else if e.isAppOf ``State.lmbSingleton then
    let args := e.getAppArgs
    let fst ← liftOption args[1]?
    let snd ← liftOption args[2]?
    return SLTerm.lmbSingleton fst snd
  else if e.isAppOf ``SLP.top then
    return SLTerm.top
  else if e.isAppOf ``SLP.lift then
    let args := e.getAppArgs
    return SLTerm.lift (←liftOption args[2]?)
  else if e.getAppFn.isMVar then
    return SLTerm.mvar e
  else if e.isAppOf ``SLP.forall' then
    let args := e.getAppArgs
    return SLTerm.all (←liftOption args[3]?)
  else if e.isAppOf ``SLP.exists' then
    let args := e.getAppArgs
    return SLTerm.exi (←liftOption args[3]?)
  else if e.isAppOf ``SLP.wand then
    let args := e.getAppArgs
    let lhs ← parseSLExpr (←liftOption args[2]?)
    let rhs ← parseSLExpr (←liftOption args[3]?)
    return SLTerm.wand lhs rhs
  -- else if e.isAppOf ``SLTerm.lift then
  --   let args := e.getAppArgs
  --   return SLTerm.lift args[0]
  -- else if e.isAppOf ``SLTerm.singleton then
  --   let args := e.getAppArgs
  --   return SLTerm.singleton args[0] args[1]
  -- else if e.isAppOf ``SLTerm.mvar then
  --   let args := e.getAppArgs
  --   return SLTerm.mvar args[0]
  else pure $ .unrecognized e

partial def parseEntailment (e: Expr): TacticM (SLTerm × SLTerm) := do
  if e.isAppOf ``SLP.entails then
    let args := e.getAppArgs
    let pre ← parseSLExpr (←liftOption args[2]?)
    let post ← parseSLExpr (←liftOption args[3]?)
    return (pre, post)
  else throwError "not an entailment {e}"

theorem star_top_of_star_mvar [LawfulHeap α] {H Q R : SLP α} : (H ⊢ Q ⋆ R) → (H ⊢ Q ⋆ ⊤) := by
  intro h
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  apply SLP.entails_top

theorem solve_left_with_leftovers [LawfulHeap α] {H Q R : SLP α} : (H ⊢ Q ⋆ R) → (R ⊢ P) → (H ⊢ Q ⋆ P) := by
  intros
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  assumption

theorem solve_with_true [LawfulHeap α] {H Q : SLP α}: (H ⊢ Q) → (H ⊢ Q ⋆ ⟦⟧) := by
  aesop
-- partial def solveNonMVarEntailment (goal : MVarId) (lhs : SLTerm) (rhs : SLTerm): TacticM (List MVarId × SLTerm) := do

theorem pure_ent_pure_star_mv [LawfulHeap α] : (P → Q) → ((P : SLP α) ⊢ Q ⋆ P) := by
  intro h
  apply SLP.pure_left'
  intro
  apply SLP.pure_right
  tauto
  simp [*, SLP.entails_self]

theorem pure_star_H_ent_pure_star_mv [LawfulHeap α] {H Q R : SLP α} :
  (P → (H ⊢ Q ⋆ R)) → (P ⋆ H ⊢ Q ⋆ P ⋆ R) := by
  intro
  apply SLP.pure_left
  intro
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.pure_right
  assumption
  rw [SLP.star_comm]
  tauto

theorem skip_left_ent_star_mv [LawfulHeap α] {R L P H : SLP α} : (R ⊢ P ⋆ H) → (L ⋆ R ⊢ P ⋆ L ⋆ H) := by
  intro h
  apply SLP.entails_trans
  apply SLP.star_mono_l
  assumption
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.star_mono_l
  rw [SLP.star_comm]
  apply SLP.entails_self

theorem skip_evidence_pure [LawfulHeap α] {H : SLP α} : Q → (H ⊢ Q ⋆ H) := by
  intro
  apply SLP.pure_right
  tauto
  tauto

theorem SLP.exists_intro [LawfulHeap α] {H : SLP α} {Q : β → SLP α} {a} : (H ⊢ Q a) → (H ⊢ ∃∃a, Q a) := by
  intro h st H
  unfold SLP.exists'
  exists a
  tauto

theorem exi_prop [LawfulHeap α] {P : Prop} {H : SLP α} {Q : P → SLP α} :
  (H ⊢ P ⋆ ⊤) → (∀(p : P), H ⊢ Q p) → (H ⊢ ∃∃p, Q p) := by
  intro h₁ h₂
  unfold SLP.entails at *
  intro st hH
  rcases h₁ st hH with ⟨_, _, _, _, h, _⟩
  rcases h
  apply Exists.intro
  apply_assumption
  apply_assumption
  assumption

theorem SLP.exists_intro_l [LawfulHeap α] {H : β → SLP α} {Q : SLP α}:
  (∀ a, (H a ⊢ Q)) → ((∃∃a, H a) ⊢ Q) := by
  intro h st
  unfold SLP.entails SLP.exists' at *
  rintro ⟨v, hH⟩
  apply h
  use hH

theorem exi_prop_l [LawfulHeap α] {P : Prop} {H : P → SLP α} {Q : SLP α} :
  ((x : P) → ((P ⋆ H x) ⊢ Q)) → ((∃∃x, H x) ⊢ Q) := by
  intro h st
  unfold SLP.entails SLP.exists' at *
  rintro ⟨v, hH⟩
  apply h
  use ∅, st
  refine ⟨?_, ?_, ?_, ?_⟩
  apply LawfulHeap.empty_disjoint
  all_goals simp_all [LawfulHeap.disjoint_empty, SLP.lift]

theorem use_right [LawfulHeap α] {R L G H : SLP α} : (R ⊢ G ⋆ H) → (L ⋆ R ⊢ G ⋆ L ⋆ H) := by
  intro
  apply SLP.entails_trans
  apply SLP.star_mono_l
  assumption
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.star_mono_l
  rw [SLP.star_comm]
  apply SLP.entails_self

theorem singleton_congr {p} {r} {v₁ v₂ : AnyValue p} : (v₁ = v₂) → ([r ↦ v₁] ⊢ [r ↦ v₂]) := by
  intro h
  rw [h]
  apply SLP.entails_self

theorem singleton_congr_mv {p} {r} {v₁ v₂ : AnyValue p} : (v₁ = v₂) → ([r ↦ v₁] ⊢ [r ↦ v₂] ⋆ ⟦⟧) := by
  rintro rfl
  simp
  apply SLP.entails_self

theorem lmbSingleton_congr_mv {p} {r} {l₁ l₂ : Lambda _} : (l₁ = l₂) → (([λr ↦ l₁] : SLP (State p)) ⊢ [λr ↦ l₂] ⋆ ⟦⟧) := by
  rintro rfl
  simp
  apply SLP.entails_self

theorem exi_singleton_congr_mv {p} {r} {v₁ : AnyValue p} {v₂ : α → AnyValue p} : (∀a, v₁ = v₂ a) →
    ((∃∃a, [r ↦ v₂ a]) ⊢ [r ↦ v₁] ⋆ ⟦⟧) := by
  intro h
  simp
  apply SLP.exists_intro_l
  intro a
  rw [←h _]
  apply SLP.entails_self

theorem singleton_star_congr {p} {r} {v₁ v₂ : AnyValue p} {R} : (v₁ = v₂) → ([r ↦ v₁] ⋆ R ⊢ [r ↦ v₂] ⋆ R) := by
  rintro rfl
  apply SLP.entails_self

theorem lmbSingleton_star_congr {p} {r} {v₁ v₂ : Lambda _} {R : SLP (State p)} :
  (v₁ = v₂) → ([λr ↦ v₁] ⋆ R ⊢ [λr ↦ v₂] ⋆ R) := by
  rintro rfl
  apply SLP.entails_self

theorem exi_singleton_star_congr {p r} {R : SLP (State p)} {v₁ : AnyValue p} {v₂ : α → AnyValue p} : (∀a, v₁ = v₂ a) →
    ((∃∃a, [r ↦ v₂ a]) ⋆ R ⊢ [r ↦ v₁] ⋆ R) := by
  intro h
  simp only [exists_star]
  apply SLP.exists_intro_l
  intro a
  rw [SLP.star_comm]
  apply SLP.star_mono_r
  rw [←h _]
  apply SLP.entails_self

partial def solvesSingleton (lhs : SLTerm) (rhsV : Expr): TacticM Bool :=
  match lhs with
  | SLTerm.singleton v _ => pure $ v == rhsV
  | SLTerm.exi (Lean.Expr.lam _ _ body _) => do solvesSingleton (←parseSLExpr body) rhsV
  | _ => pure false

partial def solveSingletonStarMV (goal : MVarId) (lhs : SLTerm) (rhs : Expr): TacticM (List MVarId) := do
  match lhs with
  | SLTerm.singleton v _ =>
    if v == rhs then
      let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``singleton_congr_mv)
      let newGoal ← liftOption newGoals[0]?
      let newGoal ← try newGoal.refl; pure []
        catch _ => pure [newGoal]
      pure $ newGoal ++ newGoals
    else throwError "not equal"
  | SLTerm.lmbSingleton v _ =>
    if v == rhs then
      let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``lmbSingleton_congr_mv)
      let newGoal ← liftOption newGoals[0]?
      let newGoal ← try newGoal.refl; pure []
        catch _ => pure [newGoal]
      pure $ newGoal ++ newGoals
    else throwError "not equal"
  | SLTerm.exi _ =>
    if (←solvesSingleton lhs rhs) then
      let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``exi_singleton_congr_mv)
      let newGoal ← liftOption newGoals[0]?
      let newGoal ← try newGoal.refl; pure []
        catch _ => pure [newGoal]
      pure $ newGoal ++ newGoals
    else
      throwError "existential cannot solve the singleton"
  | SLTerm.star _ l r =>
    match l with
    | SLTerm.singleton v _ => do
      if v == rhs then
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``singleton_star_congr)
        let newGoal ← liftOption newGoals[0]?
        let newGoal ← try newGoal.refl; pure []
          catch _ => pure [newGoal]
        pure $ newGoal ++ newGoals
      else
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``use_right)
        let newGoal ← liftOption newGoals[0]?
        let new' ← solveSingletonStarMV newGoal r rhs
        return new' ++ newGoals
    | SLTerm.lmbSingleton v _ => do
      if v == rhs then
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``lmbSingleton_star_congr)
        let newGoal ← liftOption newGoals[0]?
        let newGoal ← try newGoal.refl; pure []
          catch _ => pure [newGoal]
        pure $ newGoal ++ newGoals
      else
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``use_right)
        let newGoal ← liftOption newGoals[0]?
        let new' ← solveSingletonStarMV newGoal r rhs
        return new' ++ newGoals
    | SLTerm.lift _ =>
      let goals ← goal.apply (←mkConstWithFreshMVarLevels ``pure_star_H_ent_pure_star_mv)
      let g ← liftOption goals[0]?
      let (_, g) ← g.intro1
      let ng ← solveSingletonStarMV g r rhs
      return ng ++ goals
    | SLTerm.exi _ =>
      if (←solvesSingleton l rhs) then
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``exi_singleton_star_congr)
        let newGoal ← liftOption newGoals[0]?
        let (_, newGoal) ← newGoal.intro1
        let newGoal ← try newGoal.refl; pure []
          catch _ => pure [newGoal]
        pure $ newGoal ++ newGoals.drop 1
      else
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``use_right)
        let newGoal ← liftOption newGoals[0]?
        let new' ← solveSingletonStarMV newGoal r rhs
        return new' ++ newGoals

    | _ =>
      let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``use_right)
      let newGoal ← liftOption newGoals[0]?
      let new' ← solveSingletonStarMV newGoal r rhs
      return new' ++ newGoals
  | _ => throwError "not a singleton {lhs}"

partial def solvePureStarMV (goal : MVarId) (lhs : SLTerm): TacticM (List MVarId) := withTraceNode `Lampe.SL (fun e => return f!"solvePureStarMV {Lean.exceptEmoji e}") do
  match lhs with
  | .lift _ =>
    goal.apply (←mkConstWithFreshMVarLevels ``pure_ent_pure_star_mv)
  | .star _ l r => do
    match l with
    | .lift _ =>
      let goals ← goal.apply (←mkConstWithFreshMVarLevels ``pure_star_H_ent_pure_star_mv)
      let g ← liftOption goals[0]?
      let (_, g) ← g.intro1
      let ng ← solvePureStarMV g r
      return ng ++ goals
    | _ =>
      let goals ← goal.apply (←mkConstWithFreshMVarLevels ``skip_left_ent_star_mv)
      let g ← liftOption goals[0]?
      let ng ← solvePureStarMV g l
      return ng ++ goals
  | .singleton _ _ =>
      goal.apply (←mkConstWithFreshMVarLevels ``skip_evidence_pure)
  | .lmbSingleton _ _ =>
      goal.apply (←mkConstWithFreshMVarLevels ``skip_evidence_pure)
  | .exi _ =>
      goal.apply (←mkConstWithFreshMVarLevels ``skip_evidence_pure)
  | _ => throwError "not a lift {lhs}"

-- (H ⊢ P ⋆ ⊤) → (∀(p : P), H ⊢ Q p) → (H ⊢ ∃∃p, Q p)

lemma solve_exi_prop_star_mv {p} {P R : SLP (State p)} {Q : H → SLP (State p)} : (P ⊢ ⟦H⟧ ⋆ ⊤) → (∀(h : H), P ⊢ Q h ⋆ R) → (P ⊢ (∃∃h, Q h) ⋆ R) := by
  simp only [exists_star, star_exists]
  intros
  apply exi_prop
  assumption
  simp_all [SLP.star_comm]

mutual

partial def solveStarMV (goal : MVarId) (lhs : SLTerm) (rhsNonMv : SLTerm): TacticM (List MVarId) := do
  match rhsNonMv with
  | .singleton v _ => solveSingletonStarMV goal lhs v
  | .lmbSingleton v _ => solveSingletonStarMV goal lhs v
  | .lift _ => solvePureStarMV goal lhs
  | .exi _ =>
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``solve_exi_prop_star_mv)
    let newL ← solveEntailment (←liftOption new[0]?)
    let (_, newR) ← (←liftOption new[1]?).intro1
    let newR ← solveEntailment newR
    return newL ++ newR
  | _ => throwError "not a singleton srry {rhsNonMv}"

partial def solveEntailment (goal : MVarId): TacticM (List MVarId) := withTraceNode `Lampe.SL (tag := "solveEntailment") (fun e => return f!"solveEntailment {Lean.exceptEmoji e}") do
  let newGoal ← evalTacticAt (←`(tactic|h_norm)) goal
  let goal ← liftOption newGoal[0]?
  let target ← goal.instantiateMVarsInType
  let (pre, post) ← parseEntailment target

  trace[Lampe.SL] "Current goal: {pre.printShape} ⊢ {post.printShape}"
  trace[Lampe.SL] (←Lean.PrettyPrinter.ppExpr target)
  match pre with
  | SLTerm.exi _ => do
    let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``exi_prop_l)
    let newGoal ← liftOption newGoals[0]?
    let (_, newGoal) ← newGoal.intro1
    let gls ← solveEntailment newGoal
    return gls ++ newGoals
  | SLTerm.top => do
    let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``SLP.entails_top)
    return newGoals
  | _ => pure ()

  match post with
  | SLTerm.mvar _ => goal.apply (←mkConstWithFreshMVarLevels ``SLP.entails_self)
  | SLTerm.star _ l r =>
    -- [TODO] left can be mvar – should be rotated back
    if r.isMVar then
      let newGoals ← solveStarMV goal pre l
      return newGoals
    else if r.isTop then
      let g ← goal.apply (←mkConstWithFreshMVarLevels ``star_top_of_star_mvar)
      let g' ← liftOption g[0]?
      let ng ← solveEntailment g'
      pure $ ng ++ g
    else if r.isForAll then
      throwError "cannot solve forall"
    else throwError "todo {l} {r}"
  | SLTerm.singleton _ _ =>
    -- [TODO] handle pure on the left
    goal.apply (←mkConstWithFreshMVarLevels ``SLP.entails_self)
  | SLTerm.all _ => do
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``SLP.forall_right)
    let new' ← liftOption new[0]?
    let (_, g) ← new'.intro1
    solveEntailment g
  | SLTerm.wand _ _ =>
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``SLP.wand_intro)
    let new' ← liftOption new[0]?
    solveEntailment new'
  | SLTerm.exi _ =>
    -- [TODO] this only works for prop existential - make the others an error
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``exi_prop)
    let newL ← solveEntailment (←liftOption new[0]?)
    let (_, newR) ← (←liftOption new[1]?).intro1
    let newR ← solveEntailment newR
    return newL ++ newR
  | _ => throwError "unknown rhs {post}"

end

syntax "sl" : tactic
elab "sl" : tactic => do
  let target ← getMainGoal
  let newGoals ← solveEntailment target
  replaceMainGoal newGoals

def tryApplySyntaxes (goal : MVarId) (lemmas : List (TSyntax `term)): TacticM (List MVarId) := match lemmas with
| [] => throwError "no lemmas left"
| n::ns => do
  trace[Lampe.STHoare.Helpers] "trying {n}"
  try
    evalTacticAt (←`(tactic|apply $n)) goal
  catch e =>
    trace[Lampe.STHoare.Helpers] "failed {n} with {e.toMessageData}"
    tryApplySyntaxes goal ns

def tryApplyNames (goal : MVarId) (lemmas : List Name): TacticM (List MVarId) := match lemmas with
| [] => throwError "no lemmas left"
| n::ns => do
  try goal.apply (←mkConstWithFreshMVarLevels n)
  catch _ => tryApplyNames goal ns

def stepHelper1 (goal : MVarId) (names : List Name) (addLemmas : List (TSyntax `term)): TacticM (List MVarId) := withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"stepHelper1: {Lean.exceptEmoji e}") do
  try tryApplySyntaxes goal addLemmas
  catch _ =>
    trace[Lampe.STHoare.Helpers] "additional lemmas failed"
    tryApplyNames goal names


def stepHelper2 (goal : MVarId) (names : List Name) (addLemmas : List (TSyntax `term)): TacticM (List MVarId) := withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"stepHelper2 {Lean.exceptEmoji e}") do
  let hr :: ent :: r ← goal.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "consequence_frame_left failed"
  let furtherGoals ← stepHelper1 hr names addLemmas
  let entGoals ← try solveEntailment ent catch _ => pure [ent]
  return furtherGoals ++ entGoals ++ r

def stepHelper3 (goal : MVarId) (names : List Name) (addLemmas : List (TSyntax `term)): TacticM (List MVarId) := withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"stepHelper3 {Lean.exceptEmoji e}") do
  let hr :: ent :: r ← goal.apply (←mkConstWithFreshMVarLevels ``ramified_frame_top) | throwError "ramified_frame_top failed"
  let furtherGoals ← stepHelper1 hr names addLemmas
  let entGoals ← try solveEntailment ent catch _ => pure [ent]
  return furtherGoals ++ entGoals ++ r

macro "stephelper1" : tactic => `(tactic|(
  (first
    | apply Lampe.STHoare.litU_intro
    | apply Lampe.STHoare.litField_intro
    | apply Lampe.STHoare.litStr_intro
    | apply Lampe.STHoare.fmtStr_intro
    | apply Lampe.STHoare.litTrue_intro
    | apply Lampe.STHoare.litFalse_intro
    | apply Lampe.STHoare.litUnit_intro
    | apply fn_intro
    | apply fresh_intro
    | apply assert_intro
    | apply skip_intro
    | apply lam_intro
    | apply cast_intro
    -- memory
    | apply var_intro
    | apply ref_intro
    | apply readRef_intro
    | apply writeRef_intro
    -- array
    | apply mkArray_intro
    | apply arrayLen_intro
    | apply arrayIndex_intro
    | apply arrayAsSlice_intro
    -- slice
    | apply mkSlice_intro
    | apply sliceLen_intro
    | apply sliceIndex_intro
    | apply slicePushBack_intro
    -- equality
    | apply unitEq_intro
    | apply bEq_intro
    | apply fEq_intro
    | apply uEq_intro
    | apply iEq_intro
    | apply bigIntEq_intro
    | apply strEq_intro
    -- negation
    | apply fNeg_intro
    | apply iNeg_intro
    -- addition
    | apply fAdd_intro
    | apply uAdd_intro
    | apply iAdd_intro
    | apply bigIntAdd_intro
    -- subtraction
    | apply fSub_intro
    | apply uSub_intro
    | apply iSub_intro
    | apply bigIntSub_intro
    -- division
    | apply fDiv_intro
    | apply uDiv_intro
    | apply iDiv_intro
    | apply bigIntDiv_intro
    -- multiplication
    | apply fMul_intro
    | apply uMul_intro
    | apply iMul_intro
    | apply bigIntMul_intro
    -- remainder
    | apply uRem_intro
    | apply iRem_intro
    -- struct
    | apply mkTuple_intro
    | apply projectTuple_intro
    -- lens
    | apply modifyLens_intro
    | apply getLens_intro
  )
))

macro "stephelper2" : tactic => `(tactic|(
  (first
    | apply consequence_frame_left Lampe.STHoare.litU_intro
    | apply consequence_frame_left Lampe.STHoare.litField_intro
    | apply consequence_frame_left Lampe.STHoare.litStr_intro
    | apply consequence_frame_left Lampe.STHoare.fmtStr_intro
    | apply consequence_frame_left Lampe.STHoare.litTrue_intro
    | apply consequence_frame_left Lampe.STHoare.litFalse_intro
    | apply consequence_frame_left Lampe.STHoare.litUnit_intro
    | apply consequence_frame_left fn_intro
    | apply consequence_frame_left fresh_intro
    | apply consequence_frame_left assert_intro
    | apply consequence_frame_left lam_intro
    | apply consequence_frame_left cast_intro
    -- memory
    | apply consequence_frame_left var_intro
    | apply consequence_frame_left ref_intro
    | apply consequence_frame_left readRef_intro
    | apply consequence_frame_left writeRef_intro
    -- array
    | apply consequence_frame_left mkArray_intro
    | apply consequence_frame_left arrayLen_intro
    | apply consequence_frame_left arrayIndex_intro
    | apply consequence_frame_left arrayAsSlice_intro
    -- slice
    | apply consequence_frame_left mkSlice_intro
    | apply consequence_frame_left sliceLen_intro
    | apply consequence_frame_left sliceIndex_intro
    | apply consequence_frame_left slicePushBack_intro
    -- equality
    | apply consequence_frame_left unitEq_intro
    | apply consequence_frame_left bEq_intro
    | apply consequence_frame_left fEq_intro
    | apply consequence_frame_left uEq_intro
    | apply consequence_frame_left iEq_intro
    | apply consequence_frame_left bigIntEq_intro
    | apply consequence_frame_left strEq_intro
    -- negation
    | apply consequence_frame_left fNeg_intro
    | apply consequence_frame_left iNeg_intro
    -- addition
    | apply consequence_frame_left fAdd_intro
    | apply consequence_frame_left uAdd_intro
    | apply consequence_frame_left iAdd_intro
    | apply consequence_frame_left bigIntAdd_intro
    -- subtraction
    | apply consequence_frame_left fSub_intro
    | apply consequence_frame_left uSub_intro
    | apply consequence_frame_left iSub_intro
    | apply consequence_frame_left bigIntSub_intro
    -- division
    | apply consequence_frame_left fDiv_intro
    | apply consequence_frame_left uDiv_intro
    | apply consequence_frame_left iDiv_intro
    | apply consequence_frame_left bigIntDiv_intro
    -- multiplication
    | apply consequence_frame_left fMul_intro
    | apply consequence_frame_left uMul_intro
    | apply consequence_frame_left iMul_intro
    | apply consequence_frame_left bigIntMul_intro
    -- remainder
    | apply consequence_frame_left uRem_intro
    | apply consequence_frame_left iRem_intro
    -- struct
    | apply consequence_frame_left mkTuple_intro
    | apply consequence_frame_left projectTuple_intro
    -- lens
    | apply consequence_frame_left modifyLens_intro
    | apply consequence_frame_left getLens_intro
    -- bitwise
    | apply consequence_frame_left uShr_intro
    | apply consequence_frame_left uShl_intro
    | apply consequence_frame_left uOr_intro
    | apply consequence_frame_left uAnd_intro
    | apply consequence_frame_left uXor_intro
  )
  repeat sl
))

macro "stephelper3" : tactic => `(tactic|(
  (first
    | apply ramified_frame_top Lampe.STHoare.litU_intro
    | apply ramified_frame_top Lampe.STHoare.litField_intro
    | apply ramified_frame_top Lampe.STHoare.litStr_intro
    | apply ramified_frame_top Lampe.STHoare.fmtStr_intro
    | apply ramified_frame_top Lampe.STHoare.litTrue_intro
    | apply ramified_frame_top Lampe.STHoare.litFalse_intro
    | apply ramified_frame_top Lampe.STHoare.litUnit_intro
    | apply ramified_frame_top fn_intro
    | apply ramified_frame_top fresh_intro
    | apply ramified_frame_top assert_intro
    | apply ramified_frame_top skip_intro
    | apply ramified_frame_top lam_intro
    | apply ramified_frame_top cast_intro
    -- memory
    | apply ramified_frame_top var_intro
    | apply ramified_frame_top ref_intro
    | apply ramified_frame_top readRef_intro
    | apply ramified_frame_top writeRef_intro
    -- array
    | apply ramified_frame_top mkArray_intro
    | apply ramified_frame_top arrayLen_intro
    | apply ramified_frame_top arrayIndex_intro
    | apply ramified_frame_top arrayAsSlice_intro
    -- slice
    | apply ramified_frame_top mkSlice_intro
    | apply ramified_frame_top sliceLen_intro
    | apply ramified_frame_top sliceIndex_intro
    | apply ramified_frame_top slicePushBack_intro
    -- equality
    | apply ramified_frame_top unitEq_intro
    | apply ramified_frame_top bEq_intro
    | apply ramified_frame_top bEq_intro
    | apply ramified_frame_top fEq_intro
    | apply ramified_frame_top uEq_intro
    | apply ramified_frame_top iEq_intro
    | apply ramified_frame_top bigIntEq_intro
    | apply ramified_frame_top strEq_intro
    -- negation
    | apply ramified_frame_top fNeg_intro
    | apply ramified_frame_top iNeg_intro
    -- addition
    | apply ramified_frame_top fAdd_intro
    | apply ramified_frame_top uAdd_intro
    | apply ramified_frame_top iAdd_intro
    | apply ramified_frame_top bigIntAdd_intro
    -- subtraction
    | apply ramified_frame_top fSub_intro
    | apply ramified_frame_top uSub_intro
    | apply ramified_frame_top iSub_intro
    | apply ramified_frame_top bigIntSub_intro
    -- division
    | apply ramified_frame_top fDiv_intro
    | apply ramified_frame_top uDiv_intro
    | apply ramified_frame_top iDiv_intro
    | apply ramified_frame_top bigIntDiv_intro
    -- multiplication
    | apply ramified_frame_top fMul_intro
    | apply ramified_frame_top uMul_intro
    | apply ramified_frame_top iMul_intro
    | apply ramified_frame_top bigIntMul_intro
    -- remainder
    | apply ramified_frame_top uRem_intro
    | apply ramified_frame_top iRem_intro
    -- struct
    | apply ramified_frame_top mkTuple_intro
    | apply ramified_frame_top projectTuple_intro
    -- lens
    | apply ramified_frame_top modifyLens_intro
    | apply ramified_frame_top getLens_intro
    --- bitwise
    | apply ramified_frame_top uShr_intro
    | apply ramified_frame_top uShl_intro
    | apply ramified_frame_top uOr_intro
    | apply ramified_frame_top uAnd_intro
    | apply ramified_frame_top uXor_intro
  )
  repeat sl
))

lemma STHoare.pure_left_star {p tp} {E : Expr (Tp.denote p) tp} {Γ P₁ P₂ Q} : (P₁ → STHoare  p Γ P₂ E Q) → STHoare p Γ (⟦P₁⟧ ⋆ P₂) E Q := by
  intro h
  intro H st Hh
  unfold STHoare THoare at h
  apply h
  · simp [SLP.star, SLP.lift, SLP.entails] at Hh
    casesm* ∃_,_, _∧_
    assumption
  · simp only [SLP.star, SLP.lift, SLP.entails] at Hh
    rcases Hh with ⟨s₁, s₂, hdss, rfl, ⟨s₃, s₄, hdsss, rfl, ⟨⟨hp, rfl⟩⟩⟩, _⟩
    unfold SLP.star
    exists s₄
    exists s₂
    simp_all [LawfulHeap.union_empty, LawfulHeap.empty_union]


lemma STHoare.letIn_trivial_intro {p tp₁ tp₂} {P Q} {E : Expr (Tp.denote p) tp₁} {v'} {cont : Tp.denote p tp₁ → Expr (Tp.denote p) tp₂}
    (hE : STHoare p Γ ⟦True⟧ E (fun v => v = v'))
    (hCont : STHoare p Γ P (cont v') Q):
    STHoare p Γ P (E.letIn cont) Q := by
  apply STHoare.letIn_intro
  apply STHoare.ramified_frame_top hE (Q₂:= fun v => ⟦v = v'⟧ ⋆ P)
  · simp
    apply SLP.forall_right
    intro
    apply SLP.wand_intro
    rw [SLP.star_comm]
    apply SLP.pure_left
    rintro rfl
    simp
  · intro
    apply STHoare.pure_left_star
    rintro rfl
    assumption

syntax "inlined_var" : tactic
macro_rules
| `(tactic|inlined_var) => `(tactic |
  (first
    | apply STHoare.letIn_trivial_intro
      (first
      | apply STHoare.fn_intro
      | apply STHoare.litU_intro
      | apply STHoare.litField_intro
      | apply STHoare.mkArray_intro
      | apply genericTotalPureBuiltin_intro Builtin.uNot rfl
      | apply (STHoare.consequence (h_hoare := STHoare.fMul_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      )
  )
)

partial def steps (mvar : MVarId) (limit : Nat) (addLemmas : List $ TSyntax `term) : TacticM (List MVarId) := do
  if limit == 0 then return [mvar]
  let limit := limit - 1
  let target ← mvar.instantiateMVarsInType
  match ←extractTripleExpr target with
  | some body => do
    if isLetIn body then
      let closer ← getLetInHeadClosingTheorem body
      let vname ← getLetInVarName body
      let isInternal := vname.map (·.toString.startsWith "#") |>.getD true
      trace[Lampe.STHoare.Helpers] "letIn {closer} {vname} {isInternal}"
      match closer with
      | some (cl, true) =>
        if isInternal then
          let [nextGoal] ← evalTacticAt (←`(tactic|apply STHoare.letIn_trivial_intro; apply $cl)) mvar | throwError "bad application"
          try steps nextGoal limit addLemmas
          catch _ => return [nextGoal]
        else
          let hHead :: hTail :: rest₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
          let hHead :: hEnt :: rest₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
          let rest₃ ← evalTacticAt (←`(tactic|apply $cl)) hHead
          let rest₄ ← try solveEntailment hEnt catch _ => pure [hEnt]
          let (_, hTail) ← hTail.intro (vname.getD `v)
          let rest₅ ← try steps hTail limit addLemmas catch _ => pure [hTail]
          return rest₁ ++ rest₂ ++ rest₃ ++ rest₄ ++ rest₅
      | some (cl, false) =>
        let hHead :: hTail :: rest₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
        let hHead :: hEnt :: rest₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
        let rest₃ ← evalTacticAt (←`(tactic|apply $cl)) hHead
        let rest₄ ← try solveEntailment hEnt catch _ => pure [hEnt]
        let (_, hTail) ← hTail.intro (vname.getD `v)
        let rest₅ ← try steps hTail limit addLemmas catch _ => pure [hTail]
        return rest₃ ++ rest₅ ++ rest₁ ++ rest₂ ++ rest₄
      | none =>
        let hHead :: hTail :: rest₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
        let (_, hTail) ← hTail.intro (vname.getD `v)
        try
          let hHead :: hEnt :: rest₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
          let rest₃ ← tryApplySyntaxes hHead addLemmas
          let rest₄ ← try solveEntailment hEnt catch _ => pure [hEnt]
          let rest₅ ← try steps hTail limit addLemmas catch _ => pure [hTail]
          return rest₁ ++ rest₂ ++ rest₃ ++ rest₄ ++ rest₅
        catch _ => return (hHead :: hTail :: rest₁)

      -- let nextGoal ← if isInternal then
      --   try some <$> evalTacticAt (←`(tactic|inlined_var)) mvar
      --   catch _ => pure none
      -- else pure none
      -- match nextGoal with
      -- | some nxt => steps nxt[0]! limit addLemmas
      -- | none =>
      --     let vname := vname.getD `v
      --     if let [fst, snd, trd] ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro)
      --     then
      --       let (_, snd) ← snd.intro vname
      --       let fstGoals ← try steps fst limit addLemmas catch _ => return [fst, snd, trd]
      --       let sndGoals ← do
      --         try steps snd limit addLemmas
      --         catch _ => pure [snd]
      --       return fstGoals ++ sndGoals ++ [trd]
      --     else return [mvar]
    else if isIte body then
      if let [fGoal, tGoal] ← mvar.apply (← mkConstWithFreshMVarLevels ``ite_intro) then
        let fGoal ← if let [fGoal] ← evalTacticAt (←`(tactic|intro)) fGoal then pure fGoal
          else throwError "couldn't intro into false branch"
        let tGoal ← if let [tGoal] ← evalTacticAt (←`(tactic|intro)) tGoal then pure tGoal
          else throwError "couldn't intro into true branch"
        let fSubGoals ← try steps fGoal limit addLemmas catch _ => pure [fGoal]
        let tSubGoals ← try steps tGoal limit addLemmas catch _ => pure [tGoal]
        return fSubGoals ++ tSubGoals
      else return [mvar]
    else
      match (←getClosingTerm body) with
      | some (closer, _) => do
        let hHoare :: hEnt :: rest ← mvar.apply (←mkConstWithFreshMVarLevels ``STHoare.ramified_frame_top) | throwError "ramified_frame_top failed"
        let rest₂ ← evalTacticAt (←`(tactic|apply $closer)) hHoare
        let rest₃ ← try solveEntailment hEnt catch _ => pure [hEnt]
        return rest ++ rest₂ ++ rest₃
      | none => throwError "no closer"
  | _ => return [mvar]

syntax "steps" : tactic
elab "steps" : tactic => do
  let newGoals ← steps (← getMainGoal) 10000 []
  replaceMainGoal newGoals

syntax "steps'" (num)? ("[" term,* "]")?: tactic
elab "steps'" limit:optional(num) "[" ts:term,*  "]" : tactic => do
  let limit := limit.map (fun n => n.getNat) |>.getD 10000
  let addLemmas := ts.getElems.toList
  let newGoals ← steps (← getMainGoal) limit addLemmas
  replaceMainGoal newGoals
elab "steps'" limit:optional(num) : tactic => do
  let limit := limit.map (fun n => n.getNat) |>.getD 10000
  let newGoals ← steps (← getMainGoal) limit []
  replaceMainGoal newGoals

lemma SLP.pure_star_iff_and [LawfulHeap α] {H : SLP α} : (⟦P⟧ ⋆ H) st ↔ P ∧ H st := by
  simp [SLP.star, SLP.lift]
  apply Iff.intro
  · rintro ⟨st₁, st₂, hdis, hst, ⟨hp, rfl⟩, hH⟩
    simp only [LawfulHeap.empty_union] at hst
    cases hst
    simp_all
  · intro ⟨hP, hH⟩
    exists ∅, st
    simp_all

lemma STHoare.pluck_pures : (P → STHoare lp Γ H e Q) → (STHoare lp Γ (P ⋆ H) e (fun v => P ⋆ Q v)) := by
  intro h
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

syntax "loop_inv" term : tactic
macro "loop_inv" inv:term : tactic => `(tactic|(
  h_norm
  repeat
    apply STHoare.pluck_pures
    intro
  (first
    | apply loop_inv_intro $inv ?_
    | apply consequence_frame_left; apply loop_inv_intro $inv ?_
    | apply ramified_frame_top; apply loop_inv_intro $inv ?_
  )
  on_goal 2 => sl
))
