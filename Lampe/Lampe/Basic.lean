import Mathlib
import Lean
import Lean.Meta.Tactic.Simp.Main
import Lampe.Value

namespace Lampe

section Syntax

open Lean Elab Meta

declare_syntax_cat expr3
syntax num : expr3
syntax ident : expr3
syntax expr3 " + " expr3 : expr3
syntax expr3 " - " expr3 : expr3
syntax ident "(" sepBy(expr3, ",") ")" : expr3
syntax "(" expr3 ")" : expr3
syntax ident " := " expr3 : expr3
syntax expr3 ";" expr3 : expr3
syntax "assert" expr3 : expr3
syntax "fresh" : expr3
syntax "if" expr3 "then" expr3 "else" expr3 : expr3
syntax expr3 " = " expr3 : expr3

partial def elabExpr3 : Syntax → MetaM Lean.Expr
| `(expr3|$n:num) => mkAppM ``E3.lit #[mkNatLit n.getNat]
| `(expr3|$x:ident) => mkAppM ``E3.var #[mkStrLit x.getId.toString]
| `(expr3|$e1 = $e2) => do
  let e1 ← elabExpr3 e1
  let e2 ← elabExpr3 e2
  let fn ← mkAppM ``FunctionIdent.builtin #[mkConst ``Builtin.eq]
  let args ← mkListLit (mkConst ``E3) [e1, e2]
  mkAppM ``E3.call #[fn, args]
| `(expr3|assert $e) => do
  let e ← elabExpr3 e
  mkAppM ``E3.assert #[e]
| `(expr3|($e)) => elabExpr3 e
| `(expr3|$e1 + $e2) => do
  let e1 ← elabExpr3 e1
  let e2 ← elabExpr3 e2
  let fn ← mkAppM ``FunctionIdent.builtin #[mkConst ``Builtin.add]
  let args ← mkListLit (mkConst ``E3) [e1, e2]
  mkAppM ``E3.call #[fn, args]
| `(expr3|$e1 - $e2) => do
  let e1 ← elabExpr3 e1
  let e2 ← elabExpr3 e2
  let fn ← mkAppM ``FunctionIdent.builtin #[mkConst ``Builtin.sub]
  let args ← mkListLit (mkConst ``E3) [e1, e2]
  mkAppM ``E3.call #[fn, args]
| `(expr3|$x:ident := $e) => do
  let x := mkStrLit x.getId.toString
  let e ← elabExpr3 e
  mkAppM ``E3.assign #[x, e]
| `(expr3|fresh) => mkAppM ``E3.fresh #[]
| `(expr3|$e1 ; $e2) => do
  let e1 ← elabExpr3 e1
  let e2 ← elabExpr3 e2
  mkAppM ``E3.seq #[e1, e2]
| `(expr3|$i:ident($args,*)) => do
  let args ← args.getElems.mapM elabExpr3
  let argsList ← mkListLit (mkConst ``E3) args.toList
  let fn ← mkAppM ``FunctionIdent.decl #[mkStrLit i.getId.toString]
  mkAppM ``E3.call #[fn, argsList]
| `(expr3|if $c then $t else $e) => do
  let c ← elabExpr3 c
  let t ← elabExpr3 t
  let e ← elabExpr3 e
  mkAppM ``E3.ite #[c, t, e]
| _ => throwUnsupportedSyntax

elab "e3 {" s:expr3 "}" : term => elabExpr3 s

end Syntax

def ex3_simple : E3 := e3 {
  assert (x = 1)
}

def ex3_with_assign_and_fresh : E3 := e3 {
  (x := fresh);
  (assert (x = y));
  assert (x = z)
}

def recursive_e3 : E3 := e3 {
  if (n = 0) then
    0
  else
    (n := n - 1);
    k + recursive_e3(n, k)
}


#print ex3_simple
#print ex3_with_assign_and_fresh

def Function := List Ident × E3
def Env := Ident → Option Function
def Assignment := Nat → Value
def Scope := Ident → Option Value

def testEnv : Env := fun x => match x with
| "recursive_e3" => some (["n", "k"], recursive_e3)
| _ => none

-- inductive E3BS : Env → E3 → Nat → Scope → Nat → Scope → Value Nat Nat → (Assignment ℕ → Prop) → Prop where

inductive BuiltinBS : Builtin → List Value → Value → Prop where
| eq : BuiltinBS .eq [a, b] ⟨.bool, a == b⟩
| add : BuiltinBS .add [.int a, .int b] (.int $ Nat.add a b)
| sub : BuiltinBS .sub [⟨.int, a⟩, ⟨.int, b⟩] (.int $ Nat.sub a b)

@[simp]
theorem BuiltinBS.eq_iff {a b v}:
    BuiltinBS .eq [a, b] v ↔ v = ⟨.bool, a == b⟩ := by
  apply Iff.intro
  · rintro ⟨_⟩
    rfl
  · rintro ⟨_⟩
    apply BuiltinBS.eq

@[simp]
theorem BuiltinBS.sub_iff {a b v}:
    BuiltinBS .sub [Value.mk .int a , Value.mk .int b] v ↔ v = Value.mk .int (Nat.sub a b) := by
  apply Iff.intro
  · rintro ⟨_⟩
    rfl
  · rintro ⟨_⟩
    apply BuiltinBS.sub

@[simp]
theorem BuiltinBS.add_iff {a b v}:
    BuiltinBS .add [Value.mk .int a, Value.mk .int b] v ↔ v = Value.mk .int (Nat.add a b) := by
  apply Iff.intro
  · rintro ⟨_⟩
    rfl
  · rintro ⟨_⟩
    apply BuiltinBS.add

inductive E3BS2 : Assignment → Env → E3 → Nat → Scope → Nat → Scope → Value → Prop where
| lit : E3BS2 ε Γ (E3.lit n) pc σ pc σ (.int n)
| var :
  σ x = some v →
  E3BS2 ε Γ (E3.var x) pc σ pc σ v
| assert':
  E3BS2 ε Γ e pc₀ σ₀ pc₁ σ₁ (.bool true) →
  E3BS2 ε Γ (E3.assert e) pc₀ σ₀ pc₁ σ₁ (.int 0)
| seq:
  E3BS2 ε Γ e₁ pc₀ σ₀ pc₁ σ₁ _ →
  E3BS2 ε Γ e₂ pc₁ σ₁ pc₂ σ₂ n →
  E3BS2 ε Γ (E3.seq e₁ e₂) pc₀ σ₀ pc₂ σ₂ n
| fresh':
  E3BS2 ε Γ E3.fresh pc σ (pc + 1) σ (ε pc)
| callArgPrepDoneDecl:
  (Γ fname = some (params, body)) →
  E3BS2 ε Γ body pc (fun x => some (args.get! (params.indexOf x))) pc' σ' n →
  E3BS2 ε Γ (E3.callArgPrep (.decl fname) args []) pc σ pc' σ n
| callArgPrepDoneBuiltin:
  BuiltinBS b args v →
  E3BS2 ε Γ (E3.callArgPrep (.builtin b) args []) pc σ pc σ v
| callArgPrepNext:
  E3BS2 ε Γ a pc σ pc' σ' ra →
  E3BS2 ε Γ (E3.callArgPrep fname (args ++ [ra]) rest) pc' σ' pc'' σ'' rc →
  E3BS2 ε Γ (E3.callArgPrep fname args (a :: rest)) pc σ pc'' σ'' rc
| call:
  E3BS2 ε Γ (E3.callArgPrep fname [] args) pc σ pc' σ' n →
  E3BS2 ε Γ (E3.call fname args) pc σ pc' σ' n
| ite {cond}:
  E3BS2 ε Γ cond pc σ pc' σ' condVal →
  E3BS2 ε Γ (E3.iteCondEval condVal ifT ifF) pc' σ' pc'' σ'' n →
  E3BS2 ε Γ (E3.ite cond ifT ifF) pc σ pc'' σ'' n
| ite_true:
  E3BS2 ε Γ ifT pc σ pc' σ' n →
  E3BS2 ε Γ (E3.iteCondEval (.bool true) ifT ifF) pc σ pc' σ' n
| ite_false:
  E3BS2 ε Γ ifF pc σ pc' σ' n →
  E3BS2 ε Γ (E3.iteCondEval (.bool false) ifT ifF) pc σ pc' σ' n
| assign:
  E3BS2 ε Γ e pc₀ σ₀ pc₁ σ₁ n →
  E3BS2 ε Γ (.assign i e) pc₀ σ₀ pc₁ (fun x => if x = i then n else σ₁ x) (.int 0)

theorem E3BS2.result_congr {ε Γ e pc σ pc' σ' n n'} (h : E3BS2 ε Γ e pc σ pc' σ' n) (h' : n = n') : E3BS2 ε Γ e pc σ pc' σ' n' := by
  subst h'; assumption

@[simp]
theorem E3BS2.var_iff {ε Γ x v pc σ pc' σ'} : E3BS2 ε Γ (E3.var x) pc σ pc' σ' v ↔ σ x = some v ∧ pc = pc' ∧ σ = σ' := by
  apply Iff.intro
  · rintro ⟨rfl⟩
    simp [*]
  · rintro ⟨hp, rfl, rfl⟩
    apply E3BS2.var hp

@[simp]
theorem E3BS2.lit_iff {ε Γ n pc σ pc' σ' v} : E3BS2 ε Γ (E3.lit n) pc σ pc' σ' v ↔ v = (.int n) ∧ pc = pc' ∧ σ = σ' := by
  apply Iff.intro
  · rintro ⟨rfl⟩
    simp [*]
  · rintro ⟨rfl, rfl, rfl⟩
    apply E3BS2.lit

@[simp]
theorem E3BS2.assert_iff {ε Γ e pc σ pc' σ' v} : E3BS2 ε Γ (E3.assert e) pc σ pc' σ' v ↔ E3BS2 ε Γ e pc σ pc' σ' ⟨.bool, true⟩ ∧ v = default := by
  apply Iff.intro
  · rintro ⟨rfl⟩
    simp_all
    rfl
  · rintro ⟨hp, rfl⟩
    apply E3BS2.assert' hp

@[simp]
theorem E3BS2.seq_iff {ε Γ e₁ e₂ pc σ pc' σ' v} :
  E3BS2 ε Γ (E3.seq e₁ e₂) pc σ pc' σ' v ↔
  ∃ pc'' σ'' n₁ n₂, E3BS2 ε Γ e₁ pc σ pc'' σ'' n₁ ∧ E3BS2 ε Γ e₂ pc'' σ'' pc' σ' n₂ ∧ v = n₂ := by
  apply Iff.intro
  · intro hp
    cases hp with | seq hpl hpr =>
    repeat apply Exists.intro
    exact ⟨hpl, hpr, rfl⟩
  · intro
    casesm* Exists _, _ ∧ _
    apply E3BS2.result_congr
    apply E3BS2.seq
    assumption
    assumption
    subst_vars
    rfl

@[simp]
theorem E3BS2.fresh_iff {ε Γ pc σ pc' σ' v} : E3BS2 ε Γ E3.fresh pc σ pc' σ' v ↔ pc' = pc + 1 ∧ σ = σ' ∧ v = ε pc := by
  apply Iff.intro
  · intro hp
    cases hp with | fresh' =>
    simp
  · intro
    casesm* _ ∧ _
    subst_vars
    apply E3BS2.fresh'

@[simp]
theorem E3BS2.assign_iff {ε Γ i e pc σ pc' σ'' v} :
  E3BS2 ε Γ (.assign i e) pc σ pc' σ'' v ↔
  ∃ n σ', E3BS2 ε Γ e pc σ pc' σ' n ∧ v = default ∧ σ'' = (fun x => if x = i then some n else σ' x) := by
  apply Iff.intro
  · intro hp
    cases hp with | assign hp =>
    repeat apply Exists.intro
    refine ⟨hp, rfl, rfl⟩
  · intro
    casesm* Exists _, _ ∧ _
    subst_vars
    apply E3BS2.assign
    assumption

@[simp]
theorem ite_eq_1_iff_cond [Decidable p] : (1 = if p then 1 else 0) ↔ p := by
  split <;> tauto

@[simp]
theorem E3BS2.call_iff {ε Γ f args pc σ pc' σ' v}:
  E3BS2 ε Γ (E3.call f args) pc σ pc' σ' v ↔
  E3BS2 ε Γ (E3.callArgPrep f [] args) pc σ pc' σ' v := by
  apply Iff.intro
  · intro h; cases h; assumption
  · intro h; apply E3BS2.call; assumption

@[simp]
theorem E3BS2.callArgPrepNext_iff {ε Γ f a args avals pc σ pc' σ' v}:
  E3BS2 ε Γ (E3.callArgPrep f avals (a :: args)) pc σ pc' σ' v ↔
  ∃ pc'' σ'' av,
    E3BS2 ε Γ a pc σ pc'' σ'' av ∧
    E3BS2 ε Γ (E3.callArgPrep f (avals ++ [av]) args) pc'' σ'' pc' σ' v := by
  apply Iff.intro
  · intro h
    cases h
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · intro
    casesm* _ ∧ _, ∃_,_
    apply E3BS2.callArgPrepNext <;> assumption

@[simp low]
theorem E3BS2.callArgPrepDoneDecl_iff {ε Γ fname args pc σ pc' σ' v} :
  E3BS2 ε Γ (E3.callArgPrep (.decl fname) args []) pc σ pc' σ' v ↔
  ∃ (hp : (Γ fname).isSome), ∃ σ'',
    E3BS2 ε Γ ((Γ fname).get hp).2 pc (fun x => some (args.get! (((Γ fname).get hp).1.indexOf x))) pc' σ'' v ∧
    σ = σ' := by
  apply Iff.intro
  · intro hp
    cases hp with | callArgPrepDoneDecl hpl hpr =>
    repeat apply Exists.intro
    simp [hpl]
    simp at hpr
    exact hpr
    simp [hpl]
  · intro
    casesm* Exists _, _ ∧ _
    subst_vars
    apply E3BS2.callArgPrepDoneDecl (params := ((Γ fname).get (by assumption)).1) (body := ((Γ fname).get (by assumption)).2)
    simp
    assumption

@[simp]
theorem E3BS2.callArgPrepDoneBuiltin_iff {ε Γ b args pc σ pc' σ' v}:
  E3BS2 ε Γ (E3.callArgPrep (.builtin b) args []) pc σ pc' σ' v ↔
  pc = pc' ∧ σ = σ' ∧ BuiltinBS b args v := by
  apply Iff.intro
  . intro hp
    cases hp
    tauto
  . intro
    casesm* _∧_
    subst_vars
    apply E3BS2.callArgPrepDoneBuiltin
    assumption

theorem E3BS2.deterministic
  (hp₁ : E3BS2 ε Γ e pc σ pc₀ σ₀ n₀)
  (hp₂ : E3BS2 ε Γ e pc σ pc₁ σ₁ n₁) : pc₀ = pc₁ ∧ σ₀ = σ₁ ∧ n₀ = n₁ := by
  induction hp₁ generalizing n₁ pc₁ σ₁ with
  | lit =>
    cases hp₂; simp
  | var h₁ =>
    cases hp₂; simp
    simp [h₁] at *
    assumption
  | eq hl1 hr1 ihl ihr =>
    cases hp₂ with | eq hl2 hr2 =>
    rcases ihl hl2 with ⟨rfl, rfl, rfl⟩
    rcases ihr hr2 with ⟨rfl, rfl, rfl⟩
    simp
  | assert' h₁ ih =>
    cases hp₂ with | assert' h₂ =>
    rcases ih h₂ with ⟨rfl, rfl, _⟩
    simp
  | seq h₁ h₂ ih₁ ih₂ =>
    cases hp₂ with | seq h₁' h₂' =>
    rcases ih₁ h₁' with ⟨rfl, rfl, rfl⟩
    rcases ih₂ h₂' with ⟨rfl, rfl, rfl⟩
    simp
  | fresh' =>
    cases hp₂ with | fresh' =>
    simp
  | add h₁ h₂ ih₁ ih₂ =>
    cases hp₂ with | add h₁' h₂' =>
    rcases ih₁ h₁' with ⟨rfl, rfl, rfl⟩
    rcases ih₂ h₂' with ⟨rfl, rfl, rfl⟩
    simp
  | sub h₁ h₂ ih₁ ih₂ =>
    cases hp₂ with | sub h₁' h₂' =>
    rcases ih₁ h₁' with ⟨rfl, rfl, rfl⟩
    rcases ih₂ h₂' with ⟨rfl, rfl, rfl⟩
    simp
  | callArgPrepDone hpl hpr ih =>
    cases hp₂ with | callArgPrepDone hpl' hpr' =>
    rw [hpl] at hpl'
    cases hpl'
    rcases ih hpr' with ⟨rfl, rfl, rfl⟩
    simp
  | callArgPrepNext h₁ h₂ ih₁ ih₂ =>
    cases hp₂ with | callArgPrepNext h₁' h₂' =>
    rcases ih₁ h₁' with ⟨rfl, rfl, rfl⟩
    rcases ih₂ h₂' with ⟨rfl, rfl, rfl⟩
    simp
  | call h₁ ih =>
    cases hp₂ with | call h₁' =>
    rcases ih h₁' with ⟨rfl, rfl, rfl⟩
    simp
  | ite_true hpc hpb ihc ihb =>
    cases hp₂ with
    | ite_true hpc' hpb' =>
      rcases ihc hpc' with ⟨rfl, rfl, _⟩
      rcases ihb hpb' with ⟨rfl, rfl, rfl⟩
      simp
    | ite_false hpc' hpb' =>
      rcases ihc hpc' with ⟨_, _, h⟩
      cases h
  | ite_false hpc hpb ihc ihb =>
    cases hp₂ with
    | ite_true hpc' hpb' =>
      rcases ihc hpc' with ⟨_, _, h⟩
      cases h
    | ite_false hpc' hpb' =>
      rcases ihc hpc' with ⟨rfl, rfl, _⟩
      rcases ihb hpb' with ⟨rfl, rfl, rfl⟩
      simp
  | assign h₁ ih =>
    cases hp₂ with | assign h₁' =>
    rcases ih h₁' with ⟨rfl, rfl, rfl⟩
    simp

@[simp]
theorem E3BS2.ite_iff {cond}:
  E3BS2 ε Γ (E3.ite cond ifT ifF) pc σ pc' σ' n ↔
  ∃ pc'' σ'' v, E3BS2 ε Γ cond pc σ pc'' σ'' v ∧ E3BS2 ε Γ (E3.iteCondEval v ifT ifF) pc'' σ'' pc' σ' n := by
  apply Iff.intro
  · intro hp
    cases hp with | ite hpc hpb =>
    repeat apply Exists.intro
    apply And.intro <;> assumption
  . rintro ⟨_, _, _, _, _⟩
    apply E3BS2.ite <;> assumption

@[simp]
theorem E3BS2.iteCondEval_false_iff {ifT ifF}:
  E3BS2 ε Γ (E3.iteCondEval ⟨.bool, false⟩ ifT ifF) pc σ pc' σ' n ↔ E3BS2 ε Γ ifF pc σ pc' σ' n := by
  apply Iff.intro
  · intro hp
    cases hp
    assumption
  · exact E3BS2.ite_false

@[simp]
theorem E3BS2.iteCondEval_true_iff {ifT ifF}:
  E3BS2 ε Γ (E3.iteCondEval ⟨.bool, true⟩ ifT ifF) pc σ pc' σ' n ↔ E3BS2 ε Γ ifT pc σ pc' σ' n := by
  apply Iff.intro
  · intro hp
    cases hp
    assumption
  · exact E3BS2.ite_true

-- theorem E3BS2.ite_true_iff (hp : E3BS2 ε Γ c pc σ pc' σ' 1):
--   E3BS2 ε Γ (E3.ite c ifT ifF) pc σ pc'' σ'' n ↔ E3BS2 ε Γ ifT pc' σ' pc'' σ'' n := by
--   apply Iff.intro
--   · intro hp
--     cases hp with
--     | ite_true hpc hpb =>
--       have := E3BS2.deterministic hp hpc
--       rcases this with ⟨rfl, rfl, _⟩
--       exact hpb
--     | ite_false hpc hpb =>
--       have := E3BS2.deterministic hp hpc
--       rcases this with ⟨_, _, h⟩
--       cases h
--   · exact fun hp' => E3BS2.ite_true hp hp'

-- theorem E3BS2.ite_false_iff (hp : E3BS2 ε Γ c pc σ pc' σ' 0):
--   E3BS2 ε Γ (E3.ite c ifT ifF) pc σ pc'' σ'' n ↔ E3BS2 ε Γ ifF pc' σ' pc'' σ'' n := by
--   apply Iff.intro
--   · intro hp
--     cases hp with
--     | ite_false hpc hpb =>
--       have := E3BS2.deterministic hp hpc
--       rcases this with ⟨rfl, rfl, _⟩
--       exact hpb
--     | ite_true hpc hpb =>
--       have := E3BS2.deterministic hp hpc
--       rcases this with ⟨_, _, h⟩
--       cases h
--   · exact fun hp' => E3BS2.ite_false hp hp'

syntax "introB": tactic
macro_rules | `(tactic|introB) => `(tactic | (intros ; try casesm* _ ∧ _, ∃_, _))

syntax "crush" : tactic
macro_rules | `(tactic|crush) => `(tactic | (repeat any_goals (first | apply Iff.intro | apply Exists.intro | apply And.intro | rfl)))


theorem simplify_binder {p : α → Prop} (hp : ∀x, p x → y = x) : (∃x, p x) ↔ p y := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rw [hp x hp']
    assumption
  · intro hp'
    apply Exists.intro y
    assumption

syntax "ex_dsch" :tactic
macro_rules | `(tactic|ex_dsch) => `(tactic | (introB; (first | assumption | (symm; assumption))))

open Lean.Parser.Tactic

syntax "binder_simp" : tactic
macro_rules
| `(tactic | binder_simp) =>
  `(tactic | simp (disch := ex_dsch) only [and_assoc, simplify_binder, ←exists_and_left, ←exists_and_right, true_and, and_true, ite_true])

example : (∃m σ₁ v, E3BS2 ε Γ ex3_simple n σ m σ₁ v) ↔ (σ "x" = some (.int 1)) := by
  simp [ex3_simple]
  binder_simp

example : (∃ m σ₁ v, E3BS2 ε Γ ex3_with_assign_and_fresh n σ m σ₁ v) ↔ (σ "y" = σ "z" ∧ ε n = σ "y") := by
  simp [ex3_with_assign_and_fresh]
  binder_simp
  simp
  apply Iff.intro <;> simp_all


example : E3BS2 ε testEnv (.callArgPrep (.decl "recursive_e3") [.int n, .int k] []) pc σ pc' σ' v ↔ σ = σ' ∧ pc = pc' ∧ v = .int (n * k) := by
  induction n generalizing σ σ' pc pc' v with
  | zero =>
    simp [testEnv, recursive_e3]
    binder_simp
    simp
    tauto
  | succ n ih =>
    simp only [E3BS2.callArgPrepDoneDecl_iff]
    simp [testEnv, recursive_e3, and_assoc,  -E3BS2.callArgPrepDoneDecl_iff, ih, InstanceOf]
    apply Iff.intro <;> {introB; simp [*, Nat.add_mul, Nat.add_comm]}

end Lampe
