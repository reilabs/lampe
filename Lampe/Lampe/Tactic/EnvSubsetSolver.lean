import Lampe.SeparationLogic.State
import Lampe.SeparationLogic.SLP
import Lampe.Semantics.Env
import Lampe.Tactic.SLNorm
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

initialize
  Lean.registerTraceClass `Lampe.Env.SubsetSolver

namespace Lampe.Env.SubsetSolver

inductive EnvDef where
| Const (name : Lean.Name) -- the Env is a simple constant
| Other                    -- we don't parse this env any further, doesn't seem usable for solving the goal
| Concat (l r : EnvDef)    -- the Env is a concatenation of two other envs (++)

def toMsgDataEnv :  EnvDef → MessageData
  | .Const n => m!"{n}"
  | .Other => "_"
  | .Concat l r => m!"Concat({toMsgDataEnv l}, {toMsgDataEnv r})"

instance instToMessageDataEnvDef : ToMessageData EnvDef where
  toMessageData := toMsgDataEnv

partial def parseEnvDef (env : Lean.Expr): TacticM EnvDef := do
  let func := env.getAppFn
  let args := env.getAppArgs.toList
  match func with
  | Expr.const ``HAppend.hAppend _ => do
    let l ← parseEnvDef args[4]!
    let r ← parseEnvDef args[5]!
    pure $ .Concat l r
  | Expr.const n _ => do
    if args.isEmpty then
      pure (EnvDef.Const n)
    else
      pure $ .Other
  | _ => pure $ .Other

partial def parseGoal (goal : MVarId) : TacticM (EnvDef × EnvDef × Lean.Expr × Lean.Expr) := withTraceNode `Lampe.Env.SubsetSolver (tag := "parseGoal") (fun e => return f!"parseGoal {Lean.exceptEmoji e}") do
  let goalExpr ← goal.instantiateMVarsInType
  let func := goalExpr.getAppFn
  match func with
  | Expr.const ``Subset _ => pure ()
  | _ => throwError "Expected goal to be of the form `l ⊆ r`"
  let [tp, _, l, r] := goalExpr.getAppArgs.toList | throwError "Unexpected goal shape"
  let tp := tp.getAppFn
  match tp with
  | Expr.const ``Lampe.Env _ => pure ()
  | _ => throwError "Expected goal to be of the form `l ⊆ r` where `l` and `r` are envs"
  let lEnvDef ← parseEnvDef l
  let rEnvDef ← parseEnvDef r
  trace[Lampe.Env.SubsetSolver] "Parsed env defs: {lEnvDef}, {rEnvDef}"

  return (lEnvDef, rEnvDef, l, r)

inductive SolutionAnalysis where
| found (path : List Bool)
| notFound (names : NameSet)

def canSolve (goal : Lean.Name) (r : EnvDef): Option (List Bool) := match r with
| .Const n => if n == goal then
    .some []
  else
    .none
| .Other => .none
| .Concat l r => match canSolve goal l with
  | .some path => .some (false :: path)
  | .none => match canSolve goal r with
    | .some path => .some (true :: path)
    | .none => .none

partial def applySolution (path : List Bool) (tgt: MVarId): TacticM Unit := withTraceNode `Lampe.Env.SubsetSolver (tag := "applySolution") (fun e => return f!"applySolution {Lean.exceptEmoji e}") do
  match path with
  | [] => do
    _ ← tgt.apply (mkConst ``subset_refl)
    pure ()
  | false :: pathTail => do
    let nextGoal :: _ ← tgt.apply (mkConst ``subset_append_of_subset_left)
      | throwError "Expected to apply `subset_append_of_subset_left` but got no goals"
    applySolution pathTail nextGoal
  | true :: pathTail => do
    let nextGoal :: _ ← tgt.apply (mkConst ``subset_append_of_subset_right)
      | throwError "Expected to apply `subset_append_of_subset_right` but got no goals"
    applySolution pathTail nextGoal

partial def unfoldNames (r: EnvDef): TacticM (Option EnvDef) := do
  match r with
  | .Const n => do
    let expr := mkConst n
    let r ← unfold expr n
    if r.expr == expr then pure none else
      let r ← parseEnvDef r.expr
      pure $ some r
  | .Other => pure none
  | .Concat l r => do
    let l' ← unfoldNames l
    let r' ← unfoldNames r
    match (l', r') with
    | (.some l', .some r') => pure $ some (.Concat l' r')
    | (.some l', .none) => pure $ some (.Concat l' r)
    | (.none, .some r') => pure $ some (.Concat l r')
    | (.none, .none) => pure none

partial def solve (l r : EnvDef) (tgt: MVarId): TacticM Unit := withTraceNode `Lampe.Env.SubsetSolver (tag := "solve") (fun e => return f!"solve {Lean.exceptEmoji e}") do
  match l with
  | .Const n => do
    let solution := canSolve n r
    match solution with
    | .some path =>
      applySolution path tgt
    | .none => do
      trace[Lampe.Env.SubsetSolver] "Can't find LHS in the RHS, unfolding one layer of constant names"
      let r ← unfoldNames r
      match r with
      | .some r' => solve l r' tgt
      | .none => throwError "Cannot solve LHS, unfolding didn't do anything."
  | _ => throwError "Cannot solve LHS: {l}"

partial def solveSubset (goal : MVarId): TacticM Unit := withTraceNode `Lampe.Env.SubsetSolver (tag := "solveSubset") (fun e => return f!"solveSubset {Lean.exceptEmoji e}") do
  let (l, r, _, _) ← parseGoal goal
  solve l r goal

end Lampe.Env.SubsetSolver

syntax "solve_env_subset" : tactic
elab "solve_env_subset" : tactic => do
  let target ← getMainGoal
  Lampe.Env.SubsetSolver.solveSubset target
  replaceMainGoal []
