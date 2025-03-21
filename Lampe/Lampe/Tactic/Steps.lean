import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax
import Lampe.Tactic.SLNorm
import Lampe.Tactic.Traits
import Lampe.Tactic.SL

import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq Lampe.STHoare

initialize
  Lean.registerTraceClass `Lampe.STHoare.Helpers

def parseTriple (e : Expr) : TacticM (Option (Expr × Expr × Expr)) := do
  if e.isAppOf ``STHoare then
    let args := e.getAppArgsN 5
    return some (args[2]!, args[3]!, args[4]!)
  else return none

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

def getClosingTerm (val : Expr) : TacticM (Option (TSyntax `term × Bool)) := withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"getClosingTerm {Lean.exceptEmoji e}")  do
  let head := val.getAppFn
  match head with
  | Lean.Expr.const n _ =>
    match n with
    | ``Expr.skip => return some (←``(skip_intro), true)
    | ``Expr.var => return some (←``(var_intro), true)
    | ``Lampe.Expr.constU => return some (←``(constU_intro), true)
    | ``Lampe.Expr.constFp => return some (←``(constFp_intro), true)
    | ``Lampe.Expr.lam => return some (←``(lam_intro), false)
    | ``Expr.mkTuple => return some (←``(genericTotalPureBuiltin_intro (a := (_,_)) Builtin.mkTuple rfl), true)
    | ``Expr.mkArray =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := ($size, _)) rfl), true)
    | ``Expr.mkRepArray =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := ($size, _)) rfl), true)
    | ``Expr.mkSlice =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkSlice"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkSlice (a := ($size, _)) rfl), true)
    | ``Expr.mkRepSlice =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkSlice (a := ($size, _)) rfl), true)
    | ``Expr.getLens => return some (←``(getLens_intro), false)
    | ``Expr.modifyLens => return some (←``(modifyLens_intro), false)
    | ``Lampe.Expr.fn => return some (←``(fn_intro), true)
    | ``Lampe.Expr.callBuiltin =>
      let some builtin := val.getAppArgs[3]? | throwError "malformed builtin"
      let builtinName := builtin.getAppFn
      match builtinName with
      | Lean.Expr.const n _ =>
        match n with
        | ``Lampe.Builtin.fresh => return some (←``(fresh_intro), false)
        | ``Lampe.Builtin.assert => return some (←``(assert_intro), false)

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
        | ``Lampe.Builtin.fDiv => return some (←``(fDiv_intro), false)

        | ``Lampe.Builtin.fEq => return some (←``(genericTotalPureBuiltin_intro Builtin.fEq rfl (a := ())), true)
        | ``Lampe.Builtin.uEq => return some (←``(genericTotalPureBuiltin_intro Builtin.uEq rfl), true)

        | ``Lampe.Builtin.uAdd => return some (←``(uAdd_intro), false)
        | ``Lampe.Builtin.uMul => return some (←``(uMul_intro), false)

        | ``Lampe.Builtin.mkArray => return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray rfl), true)
        | ``Lampe.Builtin.arrayIndex => return some (←``(arrayIndex_intro), false)
        | ``Lampe.Builtin.arrayLen => return some (←``(genericTotalPureBuiltin_intro Builtin.arrayLen (a := (_,_)) rfl), true)
        | ``Lampe.Builtin.arrayAsSlice => return some (←``(genericTotalPureBuiltin_intro Builtin.arrayAsSlice (a := (_,_)) rfl), true)

        | ``Lampe.Builtin.slicePushBack => return some (←``(genericTotalPureBuiltin_intro Builtin.slicePushBack rfl), true)
        | ``Lampe.Builtin.slicePushFront => return some (←``(genericTotalPureBuiltin_intro Builtin.slicePushFront rfl), true)
        | ``Lampe.Builtin.sliceLen => return some (←``(sliceLen_intro), false)
        | ``Lampe.Builtin.sliceIndex => return some (←``(sliceIndex_intro), false)
        | ``Lampe.Builtin.ref => return some (←``(ref_intro), false)

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
      | ``Tp.bool =>
        let some (v : Expr) := val.getAppArgs[2]? | throwError "malformed litNum"
        let some (v : Expr) := v.getAppArgs[1]? | throwError "malformed litNum" -- `OfNat.ofNat _ n`
        trace[Lampe.STHoare.Helpers] "litNum bool {v}"
        match v.natLit! with
        | 0 => return some (←``(litFalse_intro), true)
        | 1 => return some (←``(litTrue_intro), true)
        | _ => return none
      | _ => return none
    | _ => return none

  | _ => pure none

def getLetInHeadClosingTheorem (e : Expr) : TacticM (Option (TSyntax `term × Bool)) := do
  let args := Expr.getAppArgs e
  let some val := args[3]? | throwError "malformed letIn"
  getClosingTerm val

def tryApplySyntaxes (goal : MVarId) (lemmas : List (TSyntax `term)): TacticM (List MVarId) := match lemmas with
| [] => throwError "no lemmas left"
| n::ns => do
  trace[Lampe.STHoare.Helpers] "trying {n}"
  try
    evalTacticAt (←`(tactic|with_unfolding_all apply $n)) goal
  catch e =>
    trace[Lampe.STHoare.Helpers] "failed {n} with {e.toMessageData}"
    tryApplySyntaxes goal ns

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

structure TripleGoals where
  triple : Option MVarId
  props : List MVarId
  implicits : List MVarId

instance : HAppend TripleGoals SLGoals TripleGoals where
  hAppend g₁ g₂ := ⟨g₁.triple, g₁.props ++ g₂.props, g₁.implicits ++ g₂.implicits⟩

instance : HAppend SLGoals TripleGoals TripleGoals where
  hAppend g₁ g₂ := ⟨g₂.triple, g₁.props ++ g₂.props, g₁.implicits ++ g₂.implicits⟩

instance : Coe SLGoals TripleGoals := ⟨fun g => ⟨none, g.props, g.implicits⟩⟩

def TripleGoals.flatten (g : TripleGoals) : List MVarId := g.props ++ g.implicits ++ g.triple.toList

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

lemma pluck_pures_destructively : (P → STHoare lp Γ H e Q) → (STHoare lp Γ (P ⋆ H) e Q) := by
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

lemma pluck_final_pure_destructively : (P → STHoare lp Γ ⟦True⟧ e Q) → (STHoare lp Γ P e Q) := by
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

partial def pluckPures (goal : MVarId) : TacticM TripleGoals := do
  let (goal, impls) ← try
    let goal :: impls ← goal.apply (←mkConstWithFreshMVarLevels ``pluck_pures_destructively) | throwError "pluck_pures_destructively failed"
    let (_, goal) ← goal.intro1
    pure $ (goal, impls)
  catch _ => return TripleGoals.mk goal [] []
  let goal ← pluckPures goal
  return TripleGoals.mk goal.triple (goal.props ++ impls) goal.implicits

def normalizeGoals (goals : TripleGoals) : TacticM TripleGoals := do
  match goals with
  | .mk (some trp) ps is =>
    let trp :: is₂ ← evalTacticAt (←`(tactic|sl_norm)) trp | throwError "sl_norm failed"
    let g ← pluckPures trp
    return TripleGoals.mk g.triple (g.props ++ ps) (g.implicits ++ is ++ is₂)
  | r => return r

syntax "triple_norm" : tactic
elab "triple_norm" : tactic => do
  let goals ← getMainGoal
  let goals ← normalizeGoals $ TripleGoals.mk goals [] []
  replaceMainGoal goals.flatten

/--
Takes a single "obvious" step – if the goal expression is a let, it will apply `letIn` and try to close the body.
If the goal is not a `letIn` it will try to close it with a closing theorem.
This takes care of solving any entailments as well.
Throws an exception if it cannot make progress or close any subsequent SL goals.
-/
partial def step (mvar : MVarId) (addLemmas : List $ TSyntax `term) : TacticM TripleGoals := do
  let target ← mvar.instantiateMVarsInType
  let some (_, body, _) ← parseTriple target | throwError "not a triple"
  if isLetIn body then
    let closer ← getLetInHeadClosingTheorem body
    let vname ← getLetInVarName body
    let isInternal := vname.map (·.toString.startsWith "#") |>.getD true
    trace[Lampe.STHoare.Helpers] "letIn {closer} {vname} {isInternal}"
    match closer, isInternal with
    | some (cl, true), true =>
      let nextTriple :: impls ← evalTacticAt (←`(tactic|apply STHoare.letIn_trivial_intro; apply $cl)) mvar | throwError "bad application"
      return TripleGoals.mk nextTriple [] impls
    | some (cl, _), _ =>
      let hHead :: hNext :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
      let (_, hNext) ← hNext.intro (vname.getD `v)
      let hHead :: hEnt :: impls₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
      let impls₃ ← evalTacticAt (←`(tactic|apply $cl)) hHead
      let rEnt ← solveEntailment hEnt
      return TripleGoals.mk hNext [] (impls₁ ++ impls₂ ++ impls₃) ++ rEnt
    | none, _ =>
      let hHead :: hNext :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
      let (_, hNext) ← hNext.intro (vname.getD `v)
      let hHead :: hEnt :: impls₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
      let impls₃ ← tryApplySyntaxes hHead addLemmas
      let rEnt ← solveEntailment hEnt
      return TripleGoals.mk hNext [] (impls₁ ++ impls₂ ++ impls₃) ++ rEnt
  else
    match (←getClosingTerm body) with
    | some (closer, _) => do
      let hHoare :: hEnt :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``STHoare.ramified_frame_top) | throwError "ramified_frame_top failed"
      let impls₂ ← evalTacticAt (←`(tactic|apply $closer)) hHoare
      let hEnt ← solveEntailment hEnt
      return hEnt ++ SLGoals.mk [] (impls₁ ++ impls₂)
    | none =>
      let hHead :: hEnt :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``STHoare.ramified_frame_top) | throwError "bad application"
      let impls₂ ← tryApplySyntaxes hHead addLemmas
      let hEnt ← solveEntailment hEnt
      return hEnt ++ SLGoals.mk [] (impls₁ ++ impls₂)

/--
Takes `limit` obvious steps. Behaves like `repeat step` – never throws exceptions.
-/
partial def stepsLoop (goals : TripleGoals) (addLemmas : List $ TSyntax `term) (limit : Nat) : TacticM TripleGoals := do
  let goals ← normalizeGoals goals
  if limit == 0 then return goals

  match goals.triple with
  | some mvar =>
    let nextTriple ← try some <$> step mvar addLemmas catch _ => pure none
    match nextTriple with
    | some nextTriple => do
      let nextGoals := nextTriple ++ SLGoals.mk goals.props goals.implicits
      stepsLoop nextGoals addLemmas (limit - 1)
    | none => return goals
  | none => return goals

partial def steps (mvar : MVarId) (limit : Nat) (addLemmas : List $ TSyntax `term) : TacticM (List MVarId) := do
  let goals ← stepsLoop (TripleGoals.mk mvar [] []) addLemmas limit
  return goals.flatten


syntax "steps" (num)? ("[" term,* "]")?: tactic
elab "steps" limit:optional(num) "[" ts:term,*  "]" : tactic => do
  let limit := limit.map (fun n => n.getNat) |>.getD 10000
  let addLemmas := ts.getElems.toList
  let newGoals ← steps (← getMainGoal) limit addLemmas
  replaceMainGoal newGoals
elab "steps" limit:optional(num) : tactic => do
  let limit := limit.map (fun n => n.getNat) |>.getD 10000
  let newGoals ← steps (← getMainGoal) limit []
  replaceMainGoal newGoals

lemma STHoare.pluck_pures : (P → STHoare lp Γ H e Q) → (STHoare lp Γ (P ⋆ H) e (fun v => P ⋆ Q v)) := by
  intro h
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

elab "loop_inv" p:optional("nat") inv:term : tactic => do
  let solver ← if p.isSome then ``(loop_inv_intro' _ $inv) else ``(loop_inv_intro $inv)
  let goals ← steps (← getMainGoal) 1 [solver]
  replaceMainGoal goals

theorem callDecl_direct_intro {p} {Γ : Env} {func} {args} {Q H}
    (h_found : (Γ.functions.find? (fun ⟨n, _⟩ => n = fnName)) = some ⟨fnName, func⟩)
    (hkc : func.generics = kinds)
    (htci : (func.body _ (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (func.body _ (hkc ▸ generics) |>.outTp) = outTp)
    (h_hoare: STHoare p Γ H (htco ▸ (func.body _ (hkc ▸ generics) |>.body (htci ▸ args))) (htco ▸ Q)) :
    STHoare p Γ H (Expr.call argTps outTp (.decl fnName kinds generics) args) Q := by
  apply STHoare.callDecl_intro (fnName := fnName) (outTp := outTp) (generics := generics)
  · exact func
  · simp [SLP.entails_top]
  · simp only [Option.eq_some_iff_get_eq] at h_found
    cases h_found
    rename_i h
    rw [←h]
    simp [List.get_find?_mem]
  · assumption
  · assumption
  · assumption
  · convert h_hoare
    cases hkc
    cases htco
    cases htci
    rfl

syntax "enter_decl" : tactic
macro_rules | `(tactic|enter_decl) => `(tactic|apply callDecl_direct_intro (by rfl) (by rfl) (by rfl) (by rfl))

theorem callTrait_direct_intro {impls : List $ Lampe.Ident × Function}
    (h_trait : TraitResolution Γ ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls)
    (h_fn : impls.find? (fun (n, _) => n = fnName) = some (fnName, func))
    (hkc : func.generics = kinds)
    (htci : (func.body _ (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (func.body _ (hkc ▸ generics) |>.outTp) = outTp)
    (h_hoare: STHoare p Γ H (htco ▸ (func.body _ (hkc ▸ generics) |>.body (htci ▸ args))) Q) :
    STHoare p Γ H (Expr.call argTps outTp (.trait (some selfTp) traitName traitKinds traitGenerics fnName kinds generics) args) Q := by
  apply STHoare.callTrait_intro (selfTp := selfTp) (traitName := traitName) (traitKinds := traitKinds) (traitGenerics := traitGenerics) (fnName := fnName) (outTp := outTp) (generics := generics)
  · simp [SLP.entails_top]
  · exact h_trait
  · simp only [Option.eq_some_iff_get_eq] at h_fn
    cases h_fn
    rename_i h
    rw [←h]
    simp [List.get_find?_mem]
  · assumption
  · assumption
  · assumption

syntax "enter_trait" "[" term,* "]" term  : tactic
macro_rules | `(tactic|enter_trait [$generics,*] $envSyn) => `(tactic|apply callTrait_direct_intro (by try_impls_all [$generics,*] $envSyn) (by rfl) (by rfl) (by rfl) (by rfl))

theorem bindVar {v : α} { P : α → Prop } (hp: ∀v, P v) : P v := by
  apply hp v
theorem enter_block H Q : STHoare p Γ H e Q → STHoare p Γ H e Q := by simp

elab "enter_block_as" n:optional(ident) ("=>")? "(" pre:term ")" "(" post:term ")" : tactic => do
  let goal ← getMainGoal
  trace[Lampe.STHoare.Helpers] "enter_block_as {n}"
  let enterer ← match n with
  | some n => ``(bindVar (fun $n => enter_block $pre $post))
  | none => ``(enter_block $pre $post)
  let newGoals ← steps goal 1 [enterer]
  replaceMainGoal newGoals
