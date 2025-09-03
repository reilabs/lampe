import Lampe.Syntax.Utils
import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

initialize
  registerTraceClass `Lampe.Traits

namespace Lampe

theorem STHoare.callTrait_direct_intro {impls : List $ Lampe.Ident × Function}
    (h_trait : TraitResolution Γ ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls)
    (h_find_fn : impls.find? (fun (n, _) => n = fnName) = some (fnName, func))
    (h_kinds_eq : func.generics = kinds)
    (h_args_eq : (func.body _ (h_kinds_eq ▸ generics) |>.argTps) = argTps)
    (h_out_eq : (func.body _ (h_kinds_eq ▸ generics) |>.outTp) = outTp)
    (h_pre_hoare: STHoare p Γ H (h_out_eq ▸ (func.body _ (h_kinds_eq ▸ generics) |>.body (h_args_eq ▸ args))) Q) :
    STHoare p Γ H (Expr.call argTps outTp (.trait selfTp traitName traitKinds traitGenerics fnName kinds generics) args) Q := by
  apply STHoare.callTrait_intro (selfTp := selfTp) (traitName := traitName) (traitKinds := traitKinds) (traitGenerics := traitGenerics) (fnName := fnName) (outTp := outTp) (generics := generics)
  · simp [SLP.entails_top]
  · exact h_trait
  · simp only [Option.eq_some_iff_get_eq] at h_find_fn
    cases h_find_fn
    rename_i h
    rw [←h]
    simp [List.get_find?_mem]
  · assumption
  · assumption
  · assumption

structure ResolutionGoal where
  goal : MVarId
  env : Lean.Expr
  traitName : Lean.Expr
  genericKinds : Lean.Expr
  generics : Lean.Expr
  self : Lean.Expr
  impl : Lean.Expr

def ResolutionGoal.traitRef (r : ResolutionGoal): Lean.Expr :=
  cons.app r.traitName |>.app r.genericKinds |>.app r.generics where
  cons := Lean.Expr.const ``Lampe.TraitRef.mk []

def ResolutionGoal.traitImplRef (r : ResolutionGoal): Lean.Expr :=
  cons.app r.traitRef |>.app r.self where
  cons := Lean.Expr.const ``Lampe.TraitImplRef.mk []

def ResolutionGoal.traitResolution (r: ResolutionGoal): Lean.Expr :=
  cons.app r.env |>.app r.traitImplRef |>.app r.impl where
  cons := Lean.Expr.const ``Lampe.TraitResolution []

def ResolutionGoal.instantiateMVars (r : ResolutionGoal): TacticM ResolutionGoal := do
  return {
    goal := r.goal
    env := ←Lean.instantiateMVars r.env
    traitName := ←Lean.instantiateMVars r.traitName
    genericKinds := ←Lean.instantiateMVars r.genericKinds
    generics := ←Lean.instantiateMVars r.generics
    self := ←Lean.instantiateMVars r.self
    impl := ←Lean.instantiateMVars r.impl
  }

def ResolutionGoal.ofGoal (goal : MVarId) : TacticM ResolutionGoal := goal.withContext $ withNewMCtxDepth do
  let goal := ResolutionGoal.mk
    (goal := goal)
    (env := ←mkFreshExprMVar none)
    (traitName := ←mkFreshExprMVar none)
    (genericKinds := ←mkFreshExprMVar none)
    (generics := ←mkFreshExprMVar none)
    (self := ←mkFreshExprMVar none)
    (impl := ←mkFreshExprMVar none)
  let target ← goal.goal.instantiateMVarsInType
  if !(←isDefEq goal.traitResolution target) then
    throwError "cannot parse a trait resolution goal {←ppExpr target}"
  goal.instantiateMVars

def peekFirstTrait (goal : MVarId) (env: Lean.Expr): TacticM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) :=
  goal.withContext $ withNewMCtxDepth do
    let fns ← mkFreshExprMVar none
    let firstName ← mkFreshExprMVar none
    let firstImpl ← mkFreshExprMVar none
    let prodα ← mkFreshExprMVar none
    let prodβ ← mkFreshExprMVar none
    let mkProd ← mkConstWithFreshMVarLevels ``Prod.mk
    let first := mkProd.app prodα |>.app prodβ |>.app firstName |>.app firstImpl
    let rest ← mkFreshExprMVar none
    let cons ← mkConstWithFreshMVarLevels ``List.cons
    let consα ← mkFreshExprMVar none
    let cons := cons.app consα |>.app first |>.app rest
    let cons := (Lean.Expr.const ``Env.mk []).app fns |>.app cons
    if ←withTransparency .all $ isDefEq cons env then
      let firstName ← Lean.instantiateExprMVars firstName
      let firstImpl ← Lean.instantiateExprMVars firstImpl
      let nextEnv ← Lean.instantiateExprMVars $ (Lean.Expr.const ``Env.mk []).app fns |>.app rest
      return some (firstName, firstImpl, nextEnv)
    else return none

partial def destructCons (xs : Lean.Expr): TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let tp ← mkFreshExprMVar none
  let head ← mkFreshExprMVar none
  let tail ← mkFreshExprMVar none
  let cons ← mkConstWithFreshMVarLevels ``List.cons
  if ←withTransparency .all $ isDefEq xs (cons.app tp |>.app head |>.app tail) then
    return some (head, tail)
  else
    return none

partial def isNil (xs : Lean.Expr): TacticM Bool := do
  let nil ← mkConstWithFreshMVarLevels ``List.nil
  let tp ← mkFreshExprMVar none
  withTransparency .all $ isDefEq xs (nil.app tp)

/-
The universe levels here need to be shared, otherwise we run into a weird
situation, where we end up with things like `HList.cons{1,1} _ HList.nil{?_, ?_}`
with the universe mvars in tail not being assigned, even though logically they
should?
-/
partial def mkFreeHListForListLoop (xs : Lean.Expr) (uα uβ : Level) (α β : Lean.Expr): TacticM Lean.Expr := do
  match ←destructCons xs with
  | some (h, t) =>
    let hCons := .const ``HList.cons [uα, uβ]
    let hh ← mkFreshExprMVar none
    let ht ← mkFreeHListForListLoop t uα uβ α β
    let r := mkAppN hCons #[α, β, h, t, hh, ht]
    return r
  | none =>
    if ←isNil xs then
      let hnil := Expr.const ``HList.nil [uα, uβ]
      return hnil.app α |>.app β
    else
      throwError "cannot construct HList"

partial def mkFreeHListForList (xs : Lean.Expr): TacticM Lean.Expr := do
  let uα ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  let uβ ← mkFreshLevelMVar
  let β ← mkFreshExprMVar none
  mkFreeHListForListLoop xs uα uβ α β

lemma resolution_mem_cons_of_mem (env: Env) (a : TraitImplRef) (l : List TraitImplRef) (ha: TraitResolvable env a) (hl : ∀x ∈ l, TraitResolvable env x):
    ∀x ∈ (a :: l), TraitResolvable env x := by
  simp_all

lemma resolution_mem_nil (env: Env): ∀x ∈ [], TraitResolvable env x := by
  simp_all

lemma resolvable_of_resolution {ref impl} (hp : TraitResolution Γ ref impl): TraitResolvable Γ ref := by
  cases hp
  apply TraitResolvable.ok <;> assumption

mutual

partial def proveConstraint (goal : MVarId): TacticM Unit := do
  try
    goal.assumption
  catch _ =>
    try
      let traitGoal :: _ ← goal.apply (mkConst ``resolvable_of_resolution []) | throwError "unexpected goals in resolvable_of_resolution"
      let goal ← ResolutionGoal.ofGoal traitGoal
      trace[Lampe.Traits] "resolving trait {← ppExpr goal.traitResolution}"
      let _ ← doResolve goal goal.env
    catch _ => pure ()

partial def proveConstraints (env : Lean.Expr) (constraintsExpr : Lean.Expr): TacticM (Option Lean.Expr) := do
  match ←destructCons constraintsExpr with
  | some (h, t) =>
    let some next ← proveConstraints env t | return none
    let fstGoalType := (Lean.Expr.const ``TraitResolvable []).app env |>.app h
    let fstGoalExpr ← mkFreshExprMVar fstGoalType
    proveConstraint fstGoalExpr.mvarId!
    if !(←fstGoalExpr.mvarId!.isAssigned) then
      trace[Lampe.Traits] "could not resolve {←ppExpr fstGoalType}"
      return none
    return mkAppN (mkConst ``resolution_mem_cons_of_mem []) #[env, h, t, fstGoalExpr, next]
  | none =>
    if ←isNil constraintsExpr then
      return mkAppN (mkConst ``resolution_mem_nil []) #[env]
    else
      return none

partial def matchTraitSignature (resolutionGoal : ResolutionGoal) (traitDef : Lean.Expr): TacticM (Option (Lean.Expr × Lean.Expr)) :=
  withTraceNode `Lampe.Traits (fun e => return f!"matchTraitSignature {Lean.exceptEmoji e}") $ do
    let defTraitGenericKinds ← mkFreshExprMVar none
    let defImplGenericKinds ← mkFreshExprMVar none
    let defTraitGenerics ← mkFreshExprMVar none
    let defConstraints ← mkFreshExprMVar none
    let defSelf ← mkFreshExprMVar none
    let defImpl ← mkFreshExprMVar none
    let defExpr := (Lean.Expr.const ``TraitImpl.mk [])
      |>.app defTraitGenericKinds
      |>.app defImplGenericKinds
      |>.app defTraitGenerics
      |>.app defConstraints
      |>.app defSelf
      |>.app defImpl

    if !(←isDefEq defExpr traitDef) then
      trace[Lampe.Traits] "Could not destructure the definition, skipping"
      return none

    if !(←isDefEq defTraitGenericKinds resolutionGoal.genericKinds) then
      trace[Lampe.Traits] "Trait generic kinds do not match, skipping"
      return none

    let implGenerics ← mkFreeHListForList defImplGenericKinds

    let traitGenerics := defTraitGenerics.app implGenerics

    if !(←withTransparency .all $ isDefEq traitGenerics resolutionGoal.generics) then
      trace[Lampe.Traits] "Trait generics do not match, skipping"
      return none

    let self := defSelf.app implGenerics
    if !(←withTransparency .all $ isDefEq self resolutionGoal.self) then
      trace[Lampe.Traits] "Trait self ({←ppExpr self}) does not match the goal, skipping"
      return none

    let constraints := defConstraints.app implGenerics
    let some constraintsProof ← withTraceNode `Lampe.Traits (fun e => return f!"solveConstraints {Lean.exceptEmoji e}") $
        proveConstraints resolutionGoal.env constraints
      | trace[Lampe.Traits] "Trait signature matched, but couldn't resolve constraints"
        return none

    pure $ some (implGenerics, constraintsProof)

partial def resolutionLoop (resolutionGoal : ResolutionGoal) (env : Lean.Expr) (depth : Nat): TacticM (List MVarId) := resolutionGoal.goal.withContext do
  let first ← peekFirstTrait resolutionGoal.goal env
  match first with
  | some (name, impl, nextEnv) =>
    if ←isDefEq name resolutionGoal.traitName then
      trace[Lampe.Traits] "Candidate name matches, trying to match signature"
      let result ← matchTraitSignature resolutionGoal impl
      match result with
      | some (assignments, constraints) =>
        trace[Lampe.Traits] "Successfully matched trait signature"

        let ok ← mkConstWithFreshMVarLevels ``TraitResolution.ok
        let ok := ok.app resolutionGoal.env |>.app resolutionGoal.traitImplRef |>.app impl
        let okTp ← inferType ok
        let (mvars, _, closer) ← forallMetaTelescopeReducing okTp
        let target ← resolutionGoal.goal.instantiateMVarsInType

        if !(←isDefEq target closer) then
          throwError "Couldn't close goal {←ppExpr target} {←ppExpr closer}"
        resolutionGoal.goal.assign (mkAppN ok mvars)

        let some implsGoal := mvars[2]? | throwError "unexpected goal in trait resolution"
        if !(←withTransparency .all $ isDefEq implsGoal assignments) then
          throwError "Couldn't close impl generics goal"

        let some ktcGoal := mvars[1]? | throwError "unexpected goal in trait resolution"
        ktcGoal.mvarId!.refl

        let some gensEqGoal := mvars[3]? | throwError "unexpected goal in trait resolution"
        withTransparency .all $ gensEqGoal.mvarId!.refl

        let some selfEqGoal := mvars[4]? | throwError "unexpected goal in trait resolution"
        withTransparency .all $ selfEqGoal.mvarId!.refl

        let mut moreGoals : List MVarId := []

        let some constraintsGoal := mvars[5]? | throwError "unexpected goal in trait resolution"
        if !(←isDefEq constraintsGoal constraints) then
          throwError "Couldn't close constraints goal"

        let some h_memG := mvars[0]? | throwError "unexpected goal in trait resolution"
        let mut h_memG := h_memG.mvarId!
        for _ in [0:depth] do
          let newH_memG :: mg ← h_memG.apply (←mkConstWithFreshMVarLevels ``List.mem_of_mem_tail)
            | throwError "unexpected goal in trait resolution"
          moreGoals := mg ++ moreGoals
          h_memG := newH_memG
        let mg := ← h_memG.apply (←mkConstWithFreshMVarLevels ``List.Mem.head)
        moreGoals := mg ++ moreGoals

        pure $ mvars.toList.map (·.mvarId!) ++ moreGoals
      | none =>
        trace[Lampe.Traits] "Failed to match trait signature"
        resolutionLoop resolutionGoal nextEnv (depth + 1)
    else
      trace[Lampe.Traits] "Candidate name ({←ppExpr name}) does not match, skipping"
      resolutionLoop resolutionGoal nextEnv (depth + 1)
  | none => throwError "trait not found"

partial def doResolve (resolutionGoal : ResolutionGoal) (env : Lean.Expr): TacticM (List MVarId) :=
  withTraceNode `Lampe.Traits (fun e => return f!"doResolve {Lean.exceptEmoji e}") $ do
    resolutionLoop resolutionGoal env 0

end

elab "resolve_trait" : tactic => do
  let mainGoal ← getMainGoal
  let target ← mainGoal.instantiateMVarsInType

  let ng ← mainGoal.withContext $ do

    let intro ← mkConstWithFreshMVarLevels ``STHoare.callTrait_direct_intro
    let introTp ← inferType intro
    let (mvars, _, closer) ← forallMetaTelescope introTp
    if !(←withTransparency .all $ isDefEq target closer) then
      throwError "Couldn't close STHoare goal ({← ppExpr target}) ({← ppExpr closer})"
    mainGoal.assign (mkAppN intro mvars)

    let some traitGoal := mvars[16]? | throwError "unexpected goal in STHoare application (resolution)"
    let traitGoal := traitGoal.mvarId!
    let goal ← ResolutionGoal.ofGoal traitGoal
    trace[Lampe.Traits] "resolving trait {← ppExpr goal.traitResolution}"
    let r ← doResolve goal goal.env

    let some findFnGoal := mvars[17]? | throwError "unexpected goal in STHoare application (find fn)"
    let findFnGoal := findFnGoal.mvarId!
    withTransparency .all $ findFnGoal.refl

    let some h_kinds_eq := mvars[18]? | throwError "unexpected goal in STHoare application (h_kinds_eq)"
    let h_kinds_eq := h_kinds_eq.mvarId!
    withTransparency .all $ h_kinds_eq.refl

    let some h_args_eq := mvars[19]? | throwError "unexpected goal in STHoare application (h_args_eq)"
    let h_args_eq := h_args_eq.mvarId!
    withTransparency .all $ h_args_eq.refl

    let some h_out_eq := mvars[20]? | throwError "unexpected goal in STHoare application (h_out_eq)"
    let h_out_eq := h_out_eq.mvarId!
    withTransparency .all $ h_out_eq.refl
    pure $ r ++ (mvars.toList.map (·.mvarId!))

  let mgAss ← instantiateMVars (.mvar mainGoal)
  trace[Lampe.Traits] "Main mvars: {←Lean.Meta.getMVars mgAss}"

  replaceMainGoal ng
