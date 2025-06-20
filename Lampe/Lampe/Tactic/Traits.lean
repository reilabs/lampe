import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

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

/-- Extract all the `TraitImpl`s from a `Lampe.Env` -/
partial def extractAllImpls (envExpr : Lean.Expr) : TacticM $ List (Lean.Expr × Lean.Expr) := do
  let traitsListExpr ← mkAppM `Lampe.Env.traits #[envExpr]
  let reducedTraitsListExpr ← withAtLeastTransparency .all (whnf traitsListExpr)

  let rec go (listExpr : Lean.Expr) : TacticM $ List (Lean.Expr × Lean.Expr) := do
    let currentExpr ← withAtLeastTransparency .all <| whnf listExpr

    if currentExpr.isAppOfArity ``List.cons 3 then
      let args := currentExpr.getAppArgs
      let headExpr ← whnf args[1]!
      let tailExpr := args[2]!
      let_expr Prod.mk _ _ name impl := headExpr
        | throwError m!"unable to extract {← ppExpr headExpr} from environment {← ppExpr envExpr}"
      let restImpls ← go tailExpr
      return (name, impl) :: restImpls

    else if currentExpr.isAppOfArity ``List.nil 1 then
      return []

    else if currentExpr.isAppOfArity ``List.append 3 then
      let args := currentExpr.getAppArgs
      let list1Expr := args[1]!
      let list2Expr := args[2]!
      let impls1 ← go list1Expr
      let impls2 ← go list2Expr
      return impls1 ++ impls2

    else
      throwError m!"unable to match on {← ppExpr currentExpr} in environment {← ppExpr envExpr}"

  go reducedTraitsListExpr

/-- Make a list literal of type `List Kind` from a list of generic kinds -/
def mkListExpr (elems : List Lean.Expr) : MetaM Lean.Expr :=
  match elems with
  | [] => return ← mkAppOptM `List.nil #[← mkAppM `Lampe.Kind #[] ]
  | head :: tail => return ← mkAppM `List.cons #[head, ← mkListExpr tail]

/-- Make an HList of of type `Hlist {rep : Kind → Type} Kind`. This is used to construct the HList
of generics to match on in the `TraitImpl`.
-/
def mkHListExpr (repExpr : Lean.Expr) (elems listExprs : List Lean.Expr) : MetaM Lean.Expr := do
  match elems with
  | [] =>
    return ← mkAppOptM `HList.nil #[(← mkAppM `Lampe.Kind #[]), some repExpr]
  | head :: tail =>
    return ← mkAppOptM `HList.cons
      #[← mkAppM `Lampe.Kind #[], repExpr, listExprs.head!, ← mkListExpr listExprs.tail, head,
        ← mkHListExpr repExpr tail listExprs.tail]

/--
Tactic to make progress on goals of the form `Expr.call (FuncRef.trait ...)` by trying all of the
trait implementations in a given environment

Usage: `try_all_traits <generics> <environment>`
* generics: A list of values to instantiate the generic type parameters
* environment: The environment to search the trait implementation

Implementation: The tactic tries to apply the lemma `STHoare.callTrait_direct_intro` with every
trait in the environment until the first trait that matches the requirement. The order of the traits
is determined by the order they are defined in the environment.

The trait resolution will succeed when:
    * The trait has the right name
    * The trait function has the right name
    * The trait function has the right generic kinds
    * The trait function has the right type
-/
-- NOTE: The order that all these metavariables get instantiated needs to happen in a fairly precise
-- sequence for unification to work, that is why this function looks somewhat complicated
elab "try_all_traits" "[" generics:term,* "]" env:term : tactic => do
  let envExpr ← elabTerm env none
  let impls ← extractAllImpls envExpr
  let genericsHList ← Lampe.mkHListLit generics.getElems.toList
  let oldState ← saveState
  let mainGoal ← getMainGoal

  for (name, impl) in impls do
    trace[Lampe.Traits] m!"attempting trait {← ppExpr name}"

    let implExprImpls ← mkAppM `Lampe.TraitImpl.impl #[impl]

    -- Need to construct the HList of generic bindings from scratch with no metavariables
    let repExpr ← mkAppM `Lampe.Kind.denote #[]
    let listExpr ← whnf (← mkAppM `Lampe.TraitImpl.implGenericKinds #[impl])
    let some (_, listExprs) := listExpr.listLit? | failure
    let elems ← generics.getElems.toList.mapM (elabTerm · none)
    let hlistExpr ← mkHListExpr repExpr elems listExprs

    let funcList ← (withAtLeastTransparency .all (whnf (.app implExprImpls hlistExpr)))

    let some (_, funcs) := funcList.listLit? |
      throwError m!"unable to match on {← ppExpr funcList} in trait implementation {← ppExpr impl}"

    for func in funcs do
      let funcArgs := func.getAppArgs
      let funcFunc := funcArgs.reverse[0]!
      let funcName := funcArgs.reverse[1]!

      trace[Lampe.Traits] m!"  attempting function {← ppExpr funcName}"
      -- In order for the metavariables to unify in the right way, we need to run these
      -- tactics in this order as otherwise `tauto` is overly eager to fill in data
      -- incorrectly
      -- In particular: `tauto` is happy to fill in a goal of type `List α` with `[]` when
      -- this particular goal needs to be filled in by hand.
      try
        -- `callTrait_direct_intro` on the main goal
        let callDirectGoals ← evalTacticAt (←`(tactic|
          apply Lampe.STHoare.callTrait_direct_intro (func := $(←funcFunc.toSyntax))
        )) mainGoal

        let traitResGoal := callDirectGoals[0]!
         -- start filling in the `TraitResolution` goal
        let traitResGoals ← evalTacticAt (←`(tactic|
          apply Lampe.TraitResolution.ok (impl := $(← impl.toSyntax)) (implGenerics := $genericsHList) (h_mem := by tauto)
        )) traitResGoal

        -- solve the `callTrait_direct_intro` goals first
        for goal in callDirectGoals.drop 1 do
          let newGoals ← evalTacticAt (← `(tactic|
            first | try tauto | try with_unfolding_all rfl
          )) goal
          pushGoals newGoals

        -- finally solve the `TraitResolution` goals
        for goal in traitResGoals do
          let goals ← evalTacticAt (←`(tactic| first | try tauto | with_unfolding_all rfl)) goal
          pushGoals goals

        if (← getUnsolvedGoals).length == 1 then
          -- one last `simp only` call to clean up the goal state
          evalTactic (← `(tactic| simp only))
          return
        else
          oldState.restore
      catch _ =>
        oldState.restore

  oldState.restore
  throwError m!"no matching trait implementation found in environment {← ppExpr envExpr}"

