import Lampe.Hoare.Builtins
import Lampe.Hoare.SepTotal
import Lampe.SeparationLogic.State
import Lampe.Syntax
import Lampe.Tactic.EnvSubsetSolver
import Lampe.Tactic.SL
import Lampe.Tactic.SLNorm
import Lampe.Tactic.Traits

import Lean.Meta.Tactic.Simp.Main

open Lampe
open Lampe.SL

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq Lampe.STHoare

initialize
  Lean.registerTraceClass `Lampe.STHoare.Helpers

def parseTriple (e : Expr) : TacticM (Option (Expr × Expr × Expr)) := do
  if e.isAppOf' ``STHoare then
    let args := e.getAppArgs'
    return some (args[3]!, args[4]!, args[5]!)
  else return none

def isLetIn (e : Expr) : Bool := e.isAppOf' ``Lampe.Expr.letIn

def getLetInVarName (e : Expr) : TacticM (Option Name) := do
  let args := Expr.getAppArgs' e
  let body := args[4]!
  match body with
  | Lean.Expr.lam n _ _ _ => return some n
  | _ => return none

/--
Attempts to get a term that can close the goal, returning the result and whether the resultant
variable should be substituted (akin to `subst_vars`).

This function matches the simple things that can be automated while keeping the automation sane. In
particular, it should never turn a solvable goal into an unsolvable goal, and should always avoid
polluting the proof state or blowing up the number of goals.
-/
def getClosingTerm (val : Expr) : TacticM (Option (TSyntax `term × Bool)) := withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"getClosingTerm {Lean.exceptEmoji e}")  do
  let head := val.getAppFn'
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
    | ``Expr.getMember => return some (← ``(genericTotalPureBuiltin_intro (Builtin.getMember _) rfl), true)
    | ``Lampe.Expr.fn => return some (←``(fn_intro), true)
    | ``Lampe.Expr.callBuiltin =>
      let some builtin := val.getAppArgs[3]? | throwError "malformed builtin"
      let builtinName := builtin.getAppFn
      match builtinName with
      | Lean.Expr.const n _ =>
        match n with
        | ``Lampe.Builtin.fresh => return some (←``(fresh_intro), false)
        | ``Lampe.Builtin.assert => return some (←``(assert_intro), false)

        | ``Lampe.Builtin.bNot => return some (←``(genericTotalPureBuiltin_intro Builtin.bNot rfl), true)

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

        -- Array builtins
        | ``Lampe.Builtin.mkArray =>
          let some argTypes := val.getAppArgs[1]? | throwError "malformed mkSlice"
          let argTypes ← argTypes.toSyntax
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := (List.length $argTypes, _)) rfl), true)
        | ``Lampe.Builtin.mkRepeatedArray =>
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkRepeatedArray (a := (_, _)) rfl), true)
        | ``Lampe.Builtin.arrayIndex => return some (←``(arrayIndex_intro), false)
        | ``Lampe.Builtin.arrayLen =>
          let some argTps :=  val.getAppArgs[1]? | throwError "malformed arrayLen"
          let some (_, argTps) := argTps.listLit? | throwError "malformed arrayLen"
          let some argTp := argTps.head? | throwError "malformed arrayLen"
          match_expr argTp with
          | Tp.slice _ => return some (←``(slice_arrayLen_intro), false)
          | Tp.array _ _ => return some (←``(array_arrayLen_intro), false)
          | _ => return none
        | ``Lampe.Builtin.asSlice => return some (←``(genericTotalPureBuiltin_intro Builtin.asSlice (a := (_,_)) rfl), true)

        -- Slice builtins
        | ``Lampe.Builtin.mkSlice =>
          let some argTypes := val.getAppArgs[1]? | throwError "malformed mkSlice"
          let argTypes ← argTypes.toSyntax
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkSlice (a := (List.length $argTypes, _)) rfl), true)
        | ``Lampe.Builtin.mkRepeatedSlice =>
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkRepeatedSlice (a := _) rfl), true)
        | ``Lampe.Builtin.slicePushBack => return some (←``(genericTotalPureBuiltin_intro Builtin.slicePushBack rfl), true)
        | ``Lampe.Builtin.slicePushFront => return some (←``(genericTotalPureBuiltin_intro Builtin.slicePushFront rfl), true)
        | ``Lampe.Builtin.sliceIndex => return some (←``(sliceIndex_intro), false)
        | ``Lampe.Builtin.ref => return some (←``(ref_intro), false)
        | ``Lampe.Builtin.readRef => return some (←``(readRef_intro), false)

        | ``Lampe.Builtin.fApplyRangeConstraint => return some (←``(fApplyRangeConstraint_intro), false)
        | ``Lampe.Builtin.fModBeBits => return some (←``(genericTotalPureBuiltin_intro Builtin.fModBeBits rfl), true)
        | ``Lampe.Builtin.fModBeBytes => return some (←``(genericTotalPureBuiltin_intro Builtin.fModBeBytes rfl), true)
        | ``Lampe.Builtin.fModLeBits => return some (←``(genericTotalPureBuiltin_intro Builtin.fModLeBits rfl), true)
        | ``Lampe.Builtin.fModLeBytes => return some (←``(genericTotalPureBuiltin_intro Builtin.fModLeBytes rfl), true)
        | ``Lampe.Builtin.fModNumBits => return some (←``(fModNumBits_intro), false)
        | ``Lampe.Builtin.iAsField => return some (←``(genericTotalPureBuiltin_intro Builtin.iAsField rfl), true)
        | ``Lampe.Builtin.iFromField => return some (←``(genericTotalPureBuiltin_intro Builtin.iFromField rfl), true)
        | ``Lampe.Builtin.uAsField => return some (←``(genericTotalPureBuiltin_intro Builtin.uAsField rfl), true)
        | ``Lampe.Builtin.uFromField => return some (←``(genericTotalPureBuiltin_intro Builtin.uFromField rfl), true)

        -- Tuple/struct builtins
        | ``Lampe.Builtin.makeData => return some (← ``(genericTotalPureBuiltin_intro (a := (_, _)) Builtin.makeData rfl), true)
        | ``Lampe.Builtin.getMember => return some (← ``(genericTotalPureBuiltin_intro (Builtin.getMember _) rfl), true)

        | ``Lampe.Builtin.zeroed => return some (←``(genericTotalPureBuiltin_intro Builtin.zeroed rfl), true)


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
    | ``Lampe.Expr.litStr => return some (←``(litStr_intro), false)
    | _ => return none

  | _ => pure none

def getLetInHeadClosingTheorem (e : Expr) : TacticM (Option (TSyntax `term × Bool)) := do
  let args := Expr.getAppArgs e
  let some val := args[3]? | throwError "malformed letIn"
  getClosingTerm val

structure AddLemma where
  term : TSyntax `term
  /--
  Controls whether the environment is generalized before applying the lemma.
  If `true`, the theorem will be applied with `apply Lampe.STHoare.is_mono` first.
  Set to `false` for lemmas that are env-agnostic.
  -/
  generalizeEnv : Bool := false

def tryApplySyntaxes (goal : MVarId) (lemmas : List AddLemma): TacticM (List MVarId) := match lemmas with
| [] => throwError "no lemmas left"
| n::ns => goal.withContext do
  trace[Lampe.STHoare.Helpers] "trying {n.term} with generalizeEnv: {n.generalizeEnv}"
  try
    let (subset, goal, others) ← if n.generalizeEnv
      then
        let subset :: main :: others ← evalTacticAt (←`(tactic|apply Lampe.STHoare.is_mono)) goal
          | throwError "apply Lampe.STHoare.is_mono gave unexpected result"
        pure ([subset], main, others)
      else pure ([], goal, [])
    let main ← evalTacticAt (←`(tactic|with_unfolding_all apply $(n.term))) goal
    for s in subset do
      trace[Lampe.STHoare.Helpers] "Solving env subset goal {s}"
      Env.SubsetSolver.solveSubset s
    pure $ main ++ others
  catch e =>
    trace[Lampe.STHoare.Helpers] "failed {n.term} with {e.toMessageData}"
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
  entailments : List MVarId
  props : List MVarId
  implicits : List MVarId

instance : HAppend TripleGoals SLGoals TripleGoals where
  hAppend g₁ g₂ := ⟨g₁.triple, g₁.entailments ++ g₂.entailments, g₁.props ++ g₂.props, g₁.implicits ++ g₂.implicits⟩

instance : HAppend SLGoals TripleGoals TripleGoals where
  hAppend g₁ g₂ := ⟨g₂.triple, g₁.entailments ++ g₂.entailments, g₁.props ++ g₂.props, g₁.implicits ++ g₂.implicits⟩

instance : Coe SLGoals TripleGoals := ⟨fun g => ⟨none, g.entailments, g.props, g.implicits⟩⟩

def TripleGoals.flatten (g : TripleGoals) : List MVarId :=  g.entailments ++ g.props ++ g.implicits ++ g.triple.toList

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
  catch _ => return TripleGoals.mk goal [] [] []
  let goal ← pluckPures goal
  return TripleGoals.mk goal.triple goal.entailments (goal.props ++ impls) goal.implicits

def normalizeGoals (goals : TripleGoals) : TacticM TripleGoals := do
  match goals with
  | .mk (some trp) ents ps is =>
    let trp :: is₂ ← evalTacticAt (←`(tactic|sl_norm)) trp | throwError "sl_norm failed"
    let g ← pluckPures trp
    return TripleGoals.mk g.triple g.entailments (g.props ++ ps) (g.implicits ++ is ++ is₂)
  | r => return r

syntax "triple_norm" : tactic
elab "triple_norm" : tactic => do
  let goals ← getMainGoal
  let goals ← normalizeGoals $ TripleGoals.mk goals [] [] []
  replaceMainGoal goals.flatten

/--
Takes a single "obvious" step to attempt to advance the proof state by simplifying the goal.

If the goal expression is a let, it will apply `letIn` and try to close the body. If it is not a let
it will try to close it using a closing theorem. It also takes care of solving any Sepratation Logic
entailments found in the goal.

It throws an exception if it cannot make progress or close any subsequent SL goal(s).
-/
partial def step (mvar : MVarId) (addLemmas : List AddLemma) : TacticM TripleGoals := mvar.withContext $ withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"step {Lean.exceptEmoji e}") $ do
  let target ← mvar.instantiateMVarsInType
  let some (_, body, _) ← parseTriple target | throwError "not a triple"
  trace[Lampe.STHoare.Helpers] "body: {body.getAppFn'}"
  if isLetIn body then
    let closer ← getLetInHeadClosingTheorem body
    let vname ← getLetInVarName body
    let isInternal := vname.map (·.toString.startsWith "#") |>.getD true
    trace[Lampe.STHoare.Helpers] "letIn {closer} {vname} {isInternal}"
    match closer, isInternal with
    | some (cl, true), true =>
      let nextTriple :: impls ← evalTacticAt (←`(tactic|apply STHoare.letIn_trivial_intro; apply $cl)) mvar | throwError "bad application"
      return TripleGoals.mk nextTriple [] [] impls
    | some (cl, _), _ =>
      let hHead :: hNext :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
      let (_, hNext) ← hNext.intro (vname.getD `v)
      let hHead :: hEnt :: impls₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
      let impls₃ ← evalTacticAt (←`(tactic|apply $cl)) hHead
      let rEnt ← solveEntailment hEnt
      return TripleGoals.mk hNext [] [] (impls₁ ++ impls₂ ++ impls₃) ++ rEnt
    | none, _ =>
      let hHead :: hNext :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
      let (_, hNext) ← hNext.intro (vname.getD `v)
      let hHead :: hEnt :: impls₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
      let impls₃ ← tryApplySyntaxes hHead addLemmas
      let rEnt ← solveEntailment hEnt
      return TripleGoals.mk hNext [] [] (impls₁ ++ impls₂ ++ impls₃) ++ rEnt
  else
    trace[Lampe.STHoare.Helpers] "not a letIn"
    match (←getClosingTerm body) with
    | some (closer, _) => do
      let hHoare :: hEnt :: qEnt :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``STHoare.consequence_frame) | throwError "ramified_frame_top failed"
      let impls₂ ← evalTacticAt (←`(tactic|apply $closer)) hHoare
      let rEnt ← solveEntailment hEnt
      let (_, qEnt) ← qEnt.intro1
      let qEnt ← if rEnt.entailments.isEmpty then
        solveEntailment qEnt
      else
        pure $ SLGoals.mk [qEnt] [] []
      return TripleGoals.mk none [] [] (impls₁ ++ impls₂) ++ rEnt ++ qEnt
      -- let hEnt ← solveEntailment hEnt
      -- return hEnt ++ SLGoals.mk [] (impls₁ ++ impls₂)
    | none =>
      let hHead :: hEnt :: qEnt :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``STHoare.consequence_frame) | throwError "bad application"
      let impls₂ ← tryApplySyntaxes hHead addLemmas
      let rEnt ← solveEntailment hEnt
      let (_, qEnt) ← qEnt.intro1
      let qEnt ← if rEnt.entailments.isEmpty then
        solveEntailment qEnt
      else
        pure $ SLGoals.mk [qEnt] [] []
      return TripleGoals.mk none [] [] (impls₁ ++ impls₂) ++ rEnt ++ qEnt
      -- let hEnt ← solveEntailment hEnt
      -- return hEnt ++ SLGoals.mk [] (impls₁ ++ impls₂)

/--
Takes `limit` obvious steps, behaving like `repeat step`.

It will never throw exceptions.
-/
partial def stepsLoop (goals : TripleGoals) (addLemmas : List AddLemma) (limit : Nat) : TacticM TripleGoals := withTraceNode `Lampe.STHoare.Helpers (fun e => return f!"stepsLoop {Lean.exceptEmoji e}") $ do
  let goals ← normalizeGoals goals
  if limit == 0 then return goals

  match goals.triple with
  | some mvar =>
    let nextTriple ← try some <$> step mvar addLemmas catch e =>
      trace[Lampe.STHoare.Helpers] "step failed with: {←e.toMessageData.toString}"
      pure none
    match nextTriple with
    | some nextTriple => do
      if !nextTriple.entailments.isEmpty then
       return nextTriple ++ SLGoals.mk goals.entailments goals.props goals.implicits
      else
        let nextGoals := nextTriple ++ SLGoals.mk goals.entailments goals.props goals.implicits
        stepsLoop nextGoals addLemmas (limit - 1)
    | none => return goals
  | none => return goals


/--
Takes a sequence of at most `limit` steps to attempt to advance the proof state by continually
simplifying the goal.
-/
partial def steps (mvar : MVarId) (limit : Nat) (addLemmas : List AddLemma): TacticM (List MVarId) := do
  let goals ← stepsLoop (TripleGoals.mk mvar [] [] []) addLemmas limit
  return goals.flatten

lemma STHoare.pluck_pures : (P → STHoare lp Γ H e Q) → (STHoare lp Γ (P ⋆ H) e (fun v => P ⋆ Q v)) := by
  intro h
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

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

theorem bindVar {v : α} { P : α → Prop } (hp: ∀v, P v) : P v := by
  apply hp v
theorem step_as H Q : STHoare p Γ H e Q → STHoare p Γ H e Q := by simp

/--
Takes a sequence of steps to attempt to advance the proof state by continually simplifying the goal.

It aims to make progress on the goal by applying small and well-reasoned operations that are
intended to always make the goal smaller and to not pollute the proof state. If it cannot discharge
a simple goal it will always roll back so as to not mess up the proof.

If the goal expression is a let, it will apply `letIn` and try to close the body. If it is not a let
it will try to close it using a closing theorem. It also takes care of solving any Sepratation Logic
entailments found in the goal.

It can be called in three main ways:

- `steps`: A bare call to the tactic will simply try to advance the goal by performing as many steps
  as it can without blowing up the proof state or failing. This version can take a maximum of 10000
  steps before failing.
- `steps n`: As above, except that it will take at most n : ℕ steps before terminating.
- `steps [lemmas,*]`: As for `steps`, except that it will specifically use the provided lemmas in
  addition to its inbuilt rules to advance the goal state. This version can be combined with the
  explicit limit case to combine the behaviors in the obvious way `steps n [lemmas,*]`.
-/
elab "steps" limit:optional(num) "[" ts:term,*  "]" : tactic => do
  let limit := limit.map (fun n => n.getNat) |>.getD 10000
  let addLemmas := ts.getElems.toList
  let newGoals ← steps (← getMainGoal) limit ((AddLemma.mk (generalizeEnv := true)) <$> addLemmas)
  replaceMainGoal newGoals
elab "steps" limit:optional(num) : tactic => do
  let limit := limit.map (fun n => n.getNat) |>.getD 10000
  let newGoals ← steps (← getMainGoal) limit []
  replaceMainGoal newGoals

/--
Performs the next step of a program proof, manually providing the pre- and post-conditions.

It is intended to be used in cases where `steps` cannot automatically perform the next step, as it
allows the user to provide a precise description of how they expect the next step to change the
program state.

It can be called in two main ways:

- `step_as (precondition) (postcondition)`: Performs the next step of the program logic, generating
  proof goals based on the explicitly-provided pre- and post-conditions.
- `step_as name => (precondition) (postcondition)`: The provided `name` acts like a metavariable,
  binding to a term in the precondition such that it is available under that name in the
  postcondition. In all other ways it operates as the previous form.
-/
elab "step_as" n:optional(ident) ("=>")? "(" pre:term ")" "(" post:term ")" : tactic => do
  let goal ← getMainGoal
  trace[Lampe.STHoare.Helpers] "step_as {n}"
  let enterer ← match n with
  | some n => ``(bindVar (fun $n => step_as $pre $post))
  | none => ``(step_as $pre $post)
  let newGoals ← steps goal 1 [AddLemma.mk enterer (generalizeEnv := false)]
  replaceMainGoal newGoals

/--
States the invariants that hold for a loop, and then creates goals that need to be proved to prove
that the loop operates according to this specification.

It can be called in two main ways:

- `loop_inv invariant`: States the invariant that holds for the loop using the iteration variable as
   existing in scope.
- `loop_inv nat invariant`: States the invariant that holds for the loop using an iteration variable
   that is a natural number ℕ. This variant can sometimes produce fewer proof goals that will need
   to be manually discharged.
-/
elab "loop_inv" p:optional("nat") inv:term : tactic => do
  let solver ← if p.isSome then ``(loop_inv_intro' $inv) else ``(loop_inv_intro $inv)
  let goals ← steps (← getMainGoal) 1 [AddLemma.mk solver (generalizeEnv := false)]
  replaceMainGoal goals

/--
Enters the declaration of a function as given by the theorem statement and unfolds the body of the
function to enable reasoning.

It is almost always the first tactic that should be run when aiming to prove a theorem about the
semantics of a piece of code.
-/
syntax "enter_decl" : tactic
macro_rules | `(tactic|enter_decl) => `(tactic|
  apply callDecl_direct_intro (by rfl) (by rfl) (by rfl) (by rfl); simp only)

/--
Enters the body of a locally-defined lambda, allowing the proof to reason about its behavior using
the manually-provided pre- and post-conditions.

It can be called in two main ways:

- `step_as (precondition) (postcondition)`: Generates proof goals to verify the behavior of the
  lambda function based on the provided pre- and post-conditions.
- `step_as name => (precondition) (postcondition)`: The provided `name` acts like a metavariable,
  binding to a term in the precondition such that it is available under that name in the
  postcondition. In all other ways it operates as the previous form.
-/
elab "enter_lambda_as" n:optional(ident) ("=>")? "(" pre:term ")" "(" post:term ")" : tactic => do
  let goal ← getMainGoal
  trace[Lampe.STHoare.Helpers] "enter_lambda_as {n}"
  let enterer ← match n with
  | some n => ``(bindVar (fun $n => STHoare.callLambda_intro (P := $pre) (Q := $post)))
  | none => ``(STHoare.callLambda_intro (P := $pre) (Q := $post))
  let newGoals ← steps goal 1 [AddLemma.mk enterer (generalizeEnv := false)]
  replaceMainGoal newGoals
