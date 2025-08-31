import Lampe.SeparationLogic.State
import Lampe.SeparationLogic.SLP
import Lampe.Tactic.SLNorm
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

namespace Lampe.SL

inductive SLTerm where
| top : Lean.Expr → SLTerm
| star : Lean.Expr → SLTerm → SLTerm → SLTerm
| lift : Lean.Expr → SLTerm
| singleton : Lean.Expr → Lean.Expr → Lean.Expr → SLTerm
| lmbSingleton : Lean.Expr → Lean.Expr → Lean.Expr → SLTerm
| mvar : Lean.Expr → SLTerm
| all : Lean.Expr → Lean.Expr → SLTerm
| exi : Lean.Expr → Lean.Expr → SLTerm
| wand : Lean.Expr → SLTerm → SLTerm → SLTerm
| unrecognized : Lean.Expr → SLTerm

def SLTerm.toString : SLTerm → String
| top _ => "⊤"
| wand _ a b => s!"{a.toString} -⋆ {b.toString}"
| exi _ e => s!"∃∃ {e}"
| all _ e => s!"∀∀ {e}"
| star _ a b => s!"({a.toString} ⋆ {b.toString})"
| lift e => s!"{e.dbgToString}"
| singleton _ e₁ _ => s!"[{e₁.dbgToString} ↦ _]"
| lmbSingleton _ e₁ _ => s!"[λ {e₁.dbgToString} ↦ _]"
| mvar e => s!"MV{e.dbgToString}"
| unrecognized e => s!"<unrecognized: {e.dbgToString}>"

def SLTerm.printShape : SLTerm → String
| SLTerm.top _ => "⊤"
| wand _ a b => s!"({a.printShape} -⋆ {b.printShape})"
| exi _ _ => s!"(∃∃)"
| all _ _ => s!"(∀∀)"
| star _ a b => s!"({a.printShape} ⋆ {b.printShape})"
| lift _ => s!"⟦⟧"
| singleton _ _ _ => s!"[_ ↦ _]"
| lmbSingleton _ _ _ => s!"[λ _ ↦ _]"
| mvar _ => s!"MV"
| unrecognized _ => s!"<unrecognized>"

def SLTerm.expr : SLTerm → Lean.Expr
| SLTerm.top e => e
| SLTerm.star e _ _ => e
| SLTerm.lift e => e
| SLTerm.singleton e _ _ => e
| SLTerm.lmbSingleton e _ _ => e
| SLTerm.mvar e => e
| SLTerm.unrecognized e => e
| SLTerm.wand e _ _ => e
| SLTerm.exi e _ => e
| SLTerm.all e _ => e

def SLTerm.isMVar : SLTerm → Bool
| SLTerm.mvar _ => true
| _ => false

def SLTerm.isTop : SLTerm → Bool
| SLTerm.top _ => true
| _ => false

def SLTerm.isForAll : SLTerm → Bool
| SLTerm.all _ _ => true
| _ => false

instance : ToString SLTerm := ⟨SLTerm.toString⟩

instance : Inhabited SLTerm := ⟨SLTerm.top (panic! "empty top")⟩

partial def parseSLExpr (e: Lean.Expr): TacticM SLTerm := do
  if e.isAppOf' ``SLP.star then
    let args := e.getAppArgs'
    let fst ← parseSLExpr (←liftOption args[2]?)
    let snd ← parseSLExpr (←liftOption args[3]?)
    return SLTerm.star e fst snd
  if e.isAppOf' ``State.valSingleton then
    let args := e.getAppArgs'
    let fst ← liftOption args[1]?
    let snd ← liftOption args[2]?
    return SLTerm.singleton e fst snd
  else if e.isAppOf' ``State.lmbSingleton then
    let args := e.getAppArgs'
    let fst ← liftOption args[1]?
    let snd ← liftOption args[2]?
    return SLTerm.lmbSingleton e fst snd
  else if e.isAppOf' ``SLP.top then
    return SLTerm.top e
  else if e.isAppOf' ``SLP.lift then
    return SLTerm.lift e
  else if e.getAppFn'.isMVar then
    return SLTerm.mvar e
  else if e.isAppOf' ``SLP.forall' then
    let args := e.getAppArgs'
    return SLTerm.all e (←liftOption args[3]?)
  else if e.isAppOf' ``SLP.exists' then
    let args := e.getAppArgs'
    return SLTerm.exi e (←liftOption args[3]?)
  else if e.isAppOf' ``SLP.wand then
    let args := e.getAppArgs'
    let lhs ← parseSLExpr (←liftOption args[2]?)
    let rhs ← parseSLExpr (←liftOption args[3]?)
    return SLTerm.wand e lhs rhs
  else pure $ .unrecognized e

partial def parseEntailment (e: Lean.Expr): TacticM (SLTerm × SLTerm) := do
  if e.isAppOf' ``SLP.entails then
    let args := e.getAppArgs'
    let pre ← parseSLExpr (←liftOption args[2]?)
    let post ← parseSLExpr (←liftOption args[3]?)
    return (pre, post)
  else throwError "not an entailment {e}"

partial def solvesSingleton (lhs : SLTerm) (rhsV : Lean.Expr): TacticM Bool :=
  match lhs with
  | SLTerm.singleton _ v _ => pure $ v == rhsV
  | SLTerm.exi _ (Lean.Expr.lam _ _ body _) => do solvesSingleton (←parseSLExpr body) rhsV
  | _ => pure false

theorem do_star_assoc {p} (a b c : SLP (State p)) : ((a ⋆ b) ⋆ c) = (a ⋆ (b ⋆ c)) := by
  rw [SLP.star_assoc]

theorem congr_star_r {p} (a b c : SLP (State p)) (eq : b = c) : (a ⋆ b) = (a ⋆ c) := by
  cases eq
  rfl

theorem do_star_comm {p} (a b : SLP (State p)) : (a ⋆ b) = (b ⋆ a) := by
  rw [SLP.star_comm]

theorem do_star_swap {p} (a b c : SLP (State p)) : (a ⋆ b ⋆ c) = (b ⋆ a ⋆ c) := by
  rw [←SLP.star_assoc]
  conv => lhs; arg 1; rw [SLP.star_comm]
  rw [SLP.star_assoc]

partial def linearize (term : SLTerm): TacticM (SLTerm × Lean.Expr) := do
  match term with
  | SLTerm.star _ (SLTerm.star _ l r) rr =>
    let eq ← mkAppM ``do_star_assoc #[l.expr, r.expr, rr.expr]
    let inner ← mkAppM ``SLP.star #[r.expr, rr.expr]
    let outer ← mkAppM ``SLP.star #[l.expr, inner]
    let newTerm := SLTerm.star outer l (SLTerm.star inner r rr)
    return (newTerm, eq)
  | SLTerm.star _ l r =>
    let (r_norm, r_norm_eq) ← linearize r
    let newExpr ← mkAppM ``SLP.star #[l.expr, r_norm.expr]
    let eq ← mkAppM ``congr_star_r #[l.expr, r.expr, r_norm.expr, r_norm_eq]
    return (SLTerm.star newExpr l r_norm, eq)
  | other => do
    let eq ← mkAppM ``Eq.refl #[other.expr]
    return (other, eq)

partial def needs_swap (l r : SLTerm): TacticM Bool := do
  match l, r with
  | SLTerm.lift _, SLTerm.lift _ => return false
  | _, SLTerm.lift _ => return true
  | _, _ => return false

partial def insert (term : SLTerm): TacticM (SLTerm × Lean.Expr) := do
  match term with
  | SLTerm.star e l (SLTerm.star _ ll r) =>
    if ←needs_swap l ll then
      let swapEq ← mkAppM ``do_star_swap #[l.expr, ll.expr, r.expr] -- l ⋆ ll ⋆ r = ll ⋆ l ⋆ r
      let swappedRExpr ← mkAppM ``SLP.star #[l.expr, r.expr]
      let (insertedR, insertedREq) ← insert (SLTerm.star swappedRExpr l r) -- l ⋆ r = inserted(l ⋆ r)
      let finalExpr ← mkAppM ``SLP.star #[ll.expr, insertedR.expr]
      let insertedEq ← mkAppM ``congr_star_r #[ll.expr, swappedRExpr, insertedR.expr, insertedREq] -- ll ⋆ l ⋆ r = ll ⋆ inserted(l ⋆ r)
      let totalEq ← mkAppM ``Eq.trans #[swapEq, insertedEq]
      return (SLTerm.star finalExpr l insertedR, totalEq)
    else
      let eq ← mkAppM ``Eq.refl #[e]
      return (term, eq)
  | SLTerm.star _ l r =>
    if ←needs_swap l r then
      let swapEq ← mkAppM ``do_star_comm #[l.expr, r.expr]
      let swappedExpr ← mkAppM ``SLP.star #[r.expr, l.expr]
      return (SLTerm.star swappedExpr r l, swapEq)
    else
      let eq ← mkAppM ``Eq.refl #[term.expr]
      return (term, eq)
  | _ => throwError "shouldn't get here"

partial def sort (term : SLTerm): TacticM (SLTerm × Lean.Expr) := do
  match term with
  | SLTerm.star _ l r =>
    let (r_sorted, r_sorted_eq) ← sort r
    let newExpr ← mkAppM ``SLP.star #[l.expr, r_sorted.expr]
    let eq ← mkAppM ``congr_star_r #[l.expr, r.expr, r_sorted.expr, r_sorted_eq]
    let newTerm := SLTerm.star newExpr l r_sorted
    let (inserted, inserted_eq) ← insert newTerm
    let eq ← mkAppM ``Eq.trans #[eq, inserted_eq]
    return (inserted, eq)
  | other => do
    let eq ← mkAppM ``Eq.refl #[other.expr]
    return (other, eq)

partial def norm (term : SLTerm): TacticM (SLTerm × Lean.Expr) := do
  let simpResult ← simpOnlyNames [``SLP.star_true, ``SLP.true_star, ``SLP.exists_star, ``SLP.star_exists, ``SLP.exists_pure] term.expr
  let simped ← parseSLExpr simpResult.expr
  let (lin, linEq) ← linearize simped
  let eq ← match simpResult.proof? with
  | some proof => mkAppM ``Eq.trans #[proof, linEq]
  | none => pure linEq
  let (sorted, sortedEq) ← sort lin
  return (sorted, ←mkAppM ``Eq.trans #[eq, sortedEq])

end Lampe.SL
