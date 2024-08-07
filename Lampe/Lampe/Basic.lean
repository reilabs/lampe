import Mathlib
import Lean


abbrev Ident := String
/--
variable (P : Nat)

inductive Value : Type where
| Field : ZMod P → Value
| String : String → Value
| Bool : Bool → Value
| Unit : Value
| Nil : Value
deriving DecidableEq

instance : Inhabited (Value P) := ⟨.Nil⟩

def Scope : Type := Ident → Value P

instance : Inhabited (Scope P) := ⟨fun _ => default⟩

inductive Builtin where
| add
| eq
| assert

inductive Callable where
| global : Ident → Callable
| builtin : Builtin → Callable

inductive Expr : Type where
| numLiteral : Int → Expr
| var : Ident → Expr
| call : Callable → List Expr → Expr
| block : List Expr → Expr → Expr
| fresh : Expr
| assign : Ident → Expr → Expr

inductive ExprAux : Type where
| expr : Expr → ExprAux
| callArgPrep : Callable → List (Value P) → List Expr → ExprAux

def Function : Type := List Ident × Expr

def Env : Type := Ident → Function

-- variable [Monad m]

-- class EvalMonad (m) extends Monad m where
--   assert : Prop → m Unit

inductive Result α where
| ok : Prop × α → Result α
| err : String → Result α

def Result₂ α := (α → String ⊕ Prop) → String ⊕ Prop

def evalBuiltin (b : Builtin) (args : List (Value P)) : Result (Value P) :=
  match b with
  | Builtin.add => match args with
    | [Value.Field a, Value.Field b] => .ok (True, Value.Field (a + b))
    | _ => .err "add expects two field arguments"
  | Builtin.eq => match args with
    | [a, b] => .ok (True, Value.Bool (a == b))
    | _ => .err "eq expects two field arguments"
  | Builtin.assert => match args with
    | [Value.Bool b] => .ok (b = True, Value.Unit)
    | _ => .err "assert expects a single boolean argument"

def NoirM (α : Type) := (α -> Prop) → (String → Prop) → Prop

def NoirM.fail {α} (msg : String) : NoirM α := fun _ kerr => kerr msg

def NoirM.assert (b : Prop) : NoirM Unit := fun kok _ => kok () ∧ b

def NoirM.unconstrained {α}: NoirM α := fun kok _ => ∃ x, kok x

instance : Monad NoirM where
  pure a := fun kok _ => kok a
  bind x f := fun kok kerr => x (fun a => f a kok kerr) kerr

def evalBuiltin' (b: Builtin) (args : List (Value P)): NoirM (Value P) := match b with
  | Builtin.add => match args with
    | [Value.Field a, Value.Field b] => pure (Value.Field (a + b))
    | _ => NoirM.fail "add expects two field arguments"
  | Builtin.eq => match args with
    | [a, b] => pure (Value.Bool (a = b))
    | _ => NoirM.fail "eq expects two field arguments"
  | Builtin.assert => match args with
    | [Value.Bool b] => do
      NoirM.assert b
      pure Value.Unit
    | _ => NoirM.fail "assert expects a single boolean argument"


mutual

def evalArgs (d : ℕ) (Γ : Env) (σ : Scope P) (es : List Expr): NoirM (List (Value P)) := match es with
| [] => pure []
| e :: es => do
  let v ← evalExpr d Γ σ e
  let vs ← evalArgs d Γ σ es
  pure (v :: vs)
termination_by d + sizeOf es

def evalExpr (d : ℕ) (Γ : Env) (σ : Scope P) (e : Expr): NoirM (Value P) := match e with
| Expr.numLiteral n => pure (Value.Field n)
| Expr.var x => pure $ σ x
| Expr.call callable args => do
  let args' ← evalArgs d Γ σ args
  match callable with
  | Callable.global fname => do
    let (args, body) := Γ fname
    match d with
    | 0 => NoirM.fail "recursion depth exceeded"
    | d + 1 => evalExpr d Γ (fun x => args'.get! (args.indexOf x)) body
  | Callable.builtin b => evalBuiltin' P b args'
| Expr.block es e => do
  let mut σ' := σ
  for e in es do
    match e with
    | Expr.assign x e => do
      let res ← evalExpr d Γ σ' e
      σ' := fun i => if i = x then res else σ' i
    | _ => do
      _ ← evalExpr d Γ σ' e
  evalExpr d Γ σ' e
| Expr.fresh => NoirM.unconstrained
| Expr.assign _ _ => NoirM.fail "assign not allowed here"
termination_by d + sizeOf e
decreasing_by
  all_goals simp_wf
  . simp [Expr.size]

end

inductive BigStepExprAux : Env → Scope P → ExprAux P → Result (Value P) → Prop where
| numLiteral {Γ σ} : BigStepExprAux Γ σ (.expr $ .numLiteral n) (.ok (True, .Field n))
| var {Γ σ x v} : σ x = v → BigStepExprAux Γ σ (.expr $ .var x) (.ok (True, v))
| call {Γ σ fname args res} :
    BigStepExprAux Γ σ (.callArgPrep fname [] args) res →
    BigStepExprAux Γ σ (.expr $ .call fname args) res
| callArgPrepDoneGlobal {Γ σ fname args res} :
    BigStepExprAux Γ (fun x => args.get! ((Γ fname).1.indexOf x)) (.expr (Γ fname).2) res →
    BigStepExprAux Γ σ (.callArgPrep (.global fname) args []) res
| callArgPrepDoneBuiltin {Γ σ fname args} :
    BigStepExprAux Γ σ (.callArgPrep (.builtin fname) args []) (evalBuiltin P fname args)
| callArgPrepNext {Γ σ fname args arg rest res p₁ p₂} :
    BigStepExprAux Γ σ (.expr arg) (.ok (p₁, a)) →
    BigStepExprAux Γ σ (.callArgPrep fname (args ++ [a]) rest) (.ok (p₂, res)) →
    BigStepExprAux Γ σ (.callArgPrep fname args (arg :: rest)) (.ok (p₁ ∧ p₂, res))
| blockNext {Γ σ e₁ es e₂ v₁ v₂}:
    BigStepExprAux Γ σ (.expr e₁) (.ok (p₁, v₁)) →
    BigStepExprAux Γ σ (.expr $ .block es e₂) (.ok (p₂, v₂)) →
    BigStepExprAux Γ σ (.expr $ .block (e₁ :: es) e₂) (.ok (p₁ ∧ p₂, v₂))
| blockDone {Γ σ e r} :
    BigStepExprAux Γ σ (.expr e) r →
    BigStepExprAux Γ σ (.expr $ .block [] e) r
| fresh {Γ σ r} : BigStepExprAux Γ σ (.expr .fresh) (.ok (True, r))

def BigStepExpr : Env →  Scope P → Expr → Result (Value P) → Prop :=
  fun Γ σ e r => BigStepExprAux P Γ σ (.expr e) r

abbrev Evaled : Type :=  Scope P → NoirM (Value P × Scope P)

inductive ExprAux' : Type where
| expr : Expr → ExprAux'
| callArgPrep : Callable → List (Evaled P) → List Expr → ExprAux'

inductive BS2Aux : Env → ExprAux' P → (Scope P → NoirM (Value P × Scope P)) → Prop where
| numLiteral {n} : BS2Aux Γ (.expr $ .numLiteral n) (fun σ => pure (.Field n, σ))
| var {x} : BS2Aux Γ (.expr $ .var x) (fun σ => pure (σ x, σ))
| callPrepDoneGlob :
  BS2Aux Γ (.expr (Γ fname).2) body →
  BS2Aux Γ (.callArgPrep (.global fname) args []) (fun σ => do
    let (argNames, _) := Γ fname
    let args' ← args.mapM fun x => do
      let (v, _) ← x σ
      pure v
    body (fun x => args'.get! (argNames.indexOf x))
  )
| callPrepDoneBuiltin :
  BS2Aux Γ (.callArgPrep (.builtin fname) args []) (fun σ => do
    let as ← args.mapA fun x => do
      let (v, _) ← x σ
      pure v
    let r ← evalBuiltin' P fname as
    pure (r, σ)
  )
| callPrepNext {fname args arg rest} :
  BS2Aux Γ (.expr arg) a →
  BS2Aux Γ (.callArgPrep fname (args ++ [a]) rest) b →
  BS2Aux Γ (.callArgPrep fname args (arg :: rest)) b
| call {fname args res} :
  BS2Aux Γ (.callArgPrep fname [] args) res →
  BS2Aux Γ (.expr $ .call fname args) res

theorem congrRes' (h : BS2Aux P Γ e r₁) (h' : r₁ = r₂) : BS2Aux P Γ e r₂ := by
  subst h'; assumption

theorem congrRes {Γ σ e r₁ r₂} (h : BigStepExprAux P Γ σ e r₁) (h' : r₁ = r₂) : BigStepExprAux P Γ σ e r₂ := by
  subst h'; assumption

def ex1 : Expr :=
  .call (.builtin .assert) [
    .call (.builtin .eq) [
      .var "x",
      .numLiteral 1
    ]
  ]

lemma ex1_BS_sem : BS2Aux P Γ (.expr ex1) (fun σ => do
  NoirM.assert (σ "x" = .Field 1)
  pure (Value.Unit, σ)
) := by
  apply BS2Aux.call
  apply BS2Aux.callPrepNext
  · apply BS2Aux.call
    apply BS2Aux.callPrepNext
    apply BS2Aux.var
    apply BS2Aux.callPrepNext
    apply BS2Aux.numLiteral
    apply BS2Aux.callPrepDoneBuiltin
  · apply congrRes'
    apply BS2Aux.callPrepDoneBuiltin
    ext σ
    simp [evalBuiltin', Seq.seq, Bind.bind, Functor.map, Pure.pure]


theorem ex1_eval {Γ σ} (hp : σ "x" = .Field x) : evalExpr 13 10 Γ σ ex1 = (do
  NoirM.assert (x = 1)
  pure Value.Unit
) := by
  simp [evalExpr, ex1, evalArgs, evalBuiltin', hp, Bind.bind, Pure.pure, NoirM.assert]

lemma ex1_sem {Γ σ} (hp : σ "x" = .Field x) : BigStepExpr P Γ σ ex1 (.ok (x = 1, Value.Unit)) := by
  apply BigStepExprAux.call
  apply congrRes
  apply BigStepExprAux.callArgPrepNext
  apply BigStepExprAux.call
  apply BigStepExprAux.callArgPrepNext
  apply BigStepExprAux.var
  rfl
  apply BigStepExprAux.callArgPrepNext
  apply BigStepExprAux.numLiteral
  apply congrRes
  apply BigStepExprAux.callArgPrepDoneBuiltin
  rw [hp]
  rfl
  apply BigStepExprAux.callArgPrepDoneBuiltin
  simp

def Assignment := Int → Value P

inductive HM : Prop → Prop where
| hm : HM True
| hm₂ : HM p

inductive Expr2 : Type where
| numLiteral : Int → Expr2
| var : Ident → Expr2
| add : Expr2 → Expr2 → Expr2
| eq : Expr2 → Expr2 → Expr2
| assign : Ident → Expr2 → Expr2
| assert : Expr2 → Expr2
| fresh : Expr2

inductive BS3 : Expr2 → Assignment P → Prop → Scope P → Scope P → Value P → Prop → Prop where
| numLiteral {n σ} : BS3 (.numLiteral n) ε p σ σ (Value.Field n) p
| var {x σ} : BS3 (.var x) ε p σ σ (σ x) p
| add {e₁ e₂ σ σ' p₁ p₂ p₃} :
  BS3 e₁ ε p₁ σ σ' (Value.Field n₁) p₂ →
  BS3 e₂ ε p₂ σ' σ' (Value.Field n₂) p₃ →
  BS3 (.add e₁ e₂) ε p₁ σ σ' (Value.Field (n₁ + n₂)) p₃
| eq {e₁ e₂ σ σ' p₁ p₂ p₃} :
  BS3 e₁ ε p₁ σ σ' n₁ p₂ →
  BS3 e₂ ε p₂ σ' σ'' n₂ p₃ →
  BS3 (.eq e₁ e₂) ε p₁ σ σ'' (Value.Bool (n₁ = n₂)) p₃
| assign {x e σ σ' p₁ p₂} :
  BS3 e ε p₁ σ σ' v p₂ →
  BS3 (.assign x e) ε p₁ σ (fun y => if y = x then v else σ y) v p₂
| assert {e σ σ' p₁ p₂} :
  BS3 e ε p₁ σ σ' (Value.Bool b) p₂ →
  BS3 (.assert e) ε p₁ σ σ' Value.Unit (p₁ ∧ b)

lemma congrRProp (h2 : BS3 P e ε p σ σ' v p') (h₁ : p' = p'') : BS3 P e ε p σ σ' v p'' := by
  subst h₁; assumption

lemma congrRVal (h2 : BS3 P e ε p σ σ' v p') (h₁ : v = v') : BS3 P e ε p σ σ' v' p' := by
  subst h₁; assumption

def ex2 : Expr2 :=
  .assert (
    .eq (.var "x") (.numLiteral 1)
  )

theorem ex2_sem : BS3 P ex2 ε p σ σ Value.Unit (p ∧ σ "x" = .Field 1) := by
  apply congrRProp
  apply BS3.assert
  apply BS3.eq
  apply BS3.var
  apply BS3.numLiteral
  simp

--/

abbrev Value := Nat

inductive Builtin where
| add
| sub
| eq

inductive FunctionIdent where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent

inductive E3 : Type where
| lit : Nat → E3
| var : Ident → E3
| add : E3 → E3 → E3
| sub : E3 → E3 → E3
| eq : E3 → E3 → E3
| assign : Ident → E3 → E3
| assert : E3 → E3
| fresh : E3
| seq : E3 → E3 → E3
| call : FunctionIdent → List E3 → E3
| callArgPrep : FunctionIdent → List Value → List E3 → E3
| ite : E3 → E3 → E3 → E3

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
  mkAppM ``E3.eq #[e1, e2]
| `(expr3|assert $e) => do
  let e ← elabExpr3 e
  mkAppM ``E3.assert #[e]
| `(expr3|($e)) => elabExpr3 e
| `(expr3|$e1 + $e2) => do
  let e1 ← elabExpr3 e1
  let e2 ← elabExpr3 e2
  mkAppM ``E3.add #[e1, e2]
| `(expr3|$e1 - $e2) => do
  let e1 ← elabExpr3 e1
  let e2 ← elabExpr3 e2
  mkAppM ``E3.sub #[e1, e2]
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
def Assignment := Nat → Nat
def Scope := Ident → Option Nat

def testEnv : Env := fun x => match x with
| "recursive_e3" => some (["n", "k"], recursive_e3)
| _ => none

-- inductive E3BS : Env → E3 → Nat → Scope → Nat → Scope → Value Nat Nat → (Assignment ℕ → Prop) → Prop where

inductive E3BS2 : Assignment → Env → E3 → Nat → Scope → Nat → Scope → Nat → Prop where
| lit : E3BS2 ε Γ (E3.lit n) pc σ pc σ n
| var :
  σ x = some v →
  E3BS2 ε Γ (E3.var x) pc σ pc σ v
| eq:
  E3BS2 ε Γ e₁ pc₀ σ₀ pc₁ σ₁ n₁ →
  E3BS2 ε Γ e₂ pc₁ σ₁ pc₂ σ₂ n₂ →
  E3BS2 ε Γ (E3.eq e₁ e₂) pc₀ σ₀ pc₂ σ₂ (if n₁ = n₂ then 1 else 0)
| assert':
  E3BS2 ε Γ e pc₀ σ₀ pc₁ σ₁ 1 →
  E3BS2 ε Γ (E3.assert e) pc₀ σ₀ pc₁ σ₁ 0
| seq:
  E3BS2 ε Γ e₁ pc₀ σ₀ pc₁ σ₁ _ →
  E3BS2 ε Γ e₂ pc₁ σ₁ pc₂ σ₂ n →
  E3BS2 ε Γ (E3.seq e₁ e₂) pc₀ σ₀ pc₂ σ₂ n
| fresh':
  E3BS2 ε Γ E3.fresh pc σ (pc + 1) σ (ε pc)
| add:
  E3BS2 ε Γ e₁ pc₀ σ₀ pc₁ σ₁ n₁ →
  E3BS2 ε Γ e₂ pc₁ σ₁ pc₂ σ₂ n₂ →
  E3BS2 ε Γ (E3.add e₁ e₂) pc₀ σ₀ pc₂ σ₂ (n₁ + n₂)
| sub:
  E3BS2 ε Γ e₁ pc₀ σ₀ pc₁ σ₁ n₁ →
  E3BS2 ε Γ e₂ pc₁ σ₁ pc₂ σ₂ n₂ →
  E3BS2 ε Γ (E3.sub e₁ e₂) pc₀ σ₀ pc₂ σ₂ (n₁ - n₂)
| callArgPrepDone:
  (Γ fname = some (params, body)) →
  E3BS2 ε Γ body pc (fun x => some (args.get! (params.indexOf x))) pc' σ' n →
  E3BS2 ε Γ (E3.callArgPrep fname args []) pc σ pc' σ n
| callArgPrepNext:
  E3BS2 ε Γ a pc σ pc' σ' ra →
  E3BS2 ε Γ (E3.callArgPrep fname (args ++ [ra]) rest) pc' σ' pc'' σ'' rc →
  E3BS2 ε Γ (E3.callArgPrep fname args (a :: rest)) pc σ pc'' σ'' rc
| call:
  E3BS2 ε Γ (E3.callArgPrep fname [] args) pc σ pc' σ' n →
  E3BS2 ε Γ (E3.call fname args) pc σ pc' σ' n
| ite_true {cond}:
  E3BS2 ε Γ cond pc σ pc' σ' 1 →
  E3BS2 ε Γ ifT pc' σ' pc'' σ'' n →
  E3BS2 ε Γ (E3.ite cond ifT ifF) pc σ pc'' σ'' n
| ite_false {cond}:
  E3BS2 ε Γ cond pc σ pc' σ' 0 →
  E3BS2 ε Γ ifF pc' σ' pc'' σ'' n →
  E3BS2 ε Γ (E3.ite cond ifT ifF) pc σ pc'' σ'' n
| assign:
  E3BS2 ε Γ e pc₀ σ₀ pc₁ σ₁ n →
  E3BS2 ε Γ (.assign i e) pc₀ σ₀ pc₁ (fun x => if x = i then n else σ₁ x) 0

theorem E3BS2.result_congr {ε Γ e pc σ pc' σ' n n'} (h : E3BS2 ε Γ e pc σ pc' σ' n) (h' : n = n') : E3BS2 ε Γ e pc σ pc' σ' n' := by
  subst h'; assumption

theorem E3BS2.lit_value : E3BS2 ε Γ (E3.lit n) pc σ pc' σ' m → m = n ∧ pc = pc' ∧ σ = σ' := by
  rintro ⟨_⟩
  tauto

@[simp]
theorem E3BS2.var_iff {ε Γ x v pc σ pc' σ'} : E3BS2 ε Γ (E3.var x) pc σ pc' σ' v ↔ σ x = some v ∧ pc = pc' ∧ σ = σ' := by
  apply Iff.intro
  · rintro ⟨rfl⟩
    simp [*]
  · rintro ⟨hp, rfl, rfl⟩
    apply E3BS2.var hp

@[simp]
theorem E3BS2.lit_iff {ε Γ n pc σ pc' σ' v} : E3BS2 ε Γ (E3.lit n) pc σ pc' σ' v ↔ v = n ∧ pc = pc' ∧ σ = σ' := by
  apply Iff.intro
  · rintro ⟨rfl⟩
    simp [*]
  · rintro ⟨rfl, rfl, rfl⟩
    apply E3BS2.lit

@[simp]
theorem E3BS2.assert_iff {ε Γ e pc σ pc' σ' v} : E3BS2 ε Γ (E3.assert e) pc σ pc' σ' v ↔ E3BS2 ε Γ e pc σ pc' σ' 1 ∧ v = 0 := by
  apply Iff.intro
  · rintro ⟨rfl⟩
    simp [*]
  · rintro ⟨hp, rfl⟩
    apply E3BS2.assert' hp

@[simp]
theorem E2BS2.eq_iff {ε Γ e₁ e₂ pc σ pc' σ' v} :
  E3BS2 ε Γ (E3.eq e₁ e₂) pc σ pc' σ' v ↔
  ∃ pc'' σ'' n₁ n₂, E3BS2 ε Γ e₁ pc σ pc'' σ'' n₁ ∧ E3BS2 ε Γ e₂ pc'' σ'' pc' σ' n₂ ∧ v = if n₁ = n₂ then 1 else 0 := by
  apply Iff.intro
  · intro hp
    cases hp with | eq hpl hpr =>
    repeat apply Exists.intro
    exact ⟨hpl, hpr, rfl⟩
  · intro
    casesm* Exists _, _ ∧ _
    apply E3BS2.result_congr
    apply E3BS2.eq
    assumption
    assumption
    subst_vars
    rfl

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
  ∃ n σ', E3BS2 ε Γ e pc σ pc' σ' n ∧ v = 0 ∧ σ'' = (fun x => if x = i then some n else σ' x) := by
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

@[simp low]
theorem E3BS2.callArgPrepDone_iff {ε Γ fname args pc σ pc' σ' v} :
  E3BS2 ε Γ (E3.callArgPrep fname args []) pc σ pc' σ' v ↔
  ∃ σ'', ∃ (hp : (Γ fname).isSome),
    E3BS2 ε Γ ((Γ fname).get hp).2 pc (fun x => some (args.get! (((Γ fname).get hp).1.indexOf x))) pc' σ'' v ∧
    σ = σ' := by
  apply Iff.intro
  · intro hp
    cases hp with | callArgPrepDone hpl hpr =>
    repeat apply Exists.intro
    simp [hpl]
    simp at hpr
    exact hpr
    simp [hpl]
  · intro
    casesm* Exists _, _ ∧ _
    subst_vars
    apply E3BS2.callArgPrepDone (params := ((Γ fname).get (by assumption)).1) (body := ((Γ fname).get (by assumption)).2)
    simp
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

theorem E3BS2.ite_true_iff (hp : E3BS2 ε Γ c pc σ pc' σ' 1):
  E3BS2 ε Γ (E3.ite c ifT ifF) pc σ pc'' σ'' n ↔ E3BS2 ε Γ ifT pc' σ' pc'' σ'' n := by
  apply Iff.intro
  · intro hp
    cases hp with
    | ite_true hpc hpb =>
      have := E3BS2.deterministic hp hpc
      rcases this with ⟨rfl, rfl, _⟩
      exact hpb
    | ite_false hpc hpb =>
      have := E3BS2.deterministic hp hpc
      rcases this with ⟨_, _, h⟩
      cases h
  · exact fun hp' => E3BS2.ite_true hp hp'

theorem E3BS2.ite_false_iff (hp : E3BS2 ε Γ c pc σ pc' σ' 0):
  E3BS2 ε Γ (E3.ite c ifT ifF) pc σ pc'' σ'' n ↔ E3BS2 ε Γ ifF pc' σ' pc'' σ'' n := by
  apply Iff.intro
  · intro hp
    cases hp with
    | ite_false hpc hpb =>
      have := E3BS2.deterministic hp hpc
      rcases this with ⟨rfl, rfl, _⟩
      exact hpb
    | ite_true hpc hpb =>
      have := E3BS2.deterministic hp hpc
      rcases this with ⟨_, _, h⟩
      cases h
  · exact fun hp' => E3BS2.ite_false hp hp'

syntax "introB": tactic
macro_rules | `(tactic|introB) => `(tactic | (intro ; try casesm* _ ∧ _, ∃_, _))

syntax "crush" : tactic
macro_rules | `(tactic|crush) => `(tactic | (repeat any_goals (first | apply Iff.intro | apply Exists.intro | apply And.intro | rfl)))

example : (∃ m σ₁ v, E3BS2 ε Γ ex3_simple n σ m σ₁ v) ↔ (σ "x" = some 1) := by
  simp [ex3_simple]
  crush
  . introB
    subst_vars
    assumption
  . introB
    crush
    assumption

example : (∃ m σ₁ v, E3BS2 ε Γ ex3_with_assign_and_fresh n σ m σ₁ v) ↔ (σ "y" = σ "z" ∧ ε n = σ "y") := by
  simp [ex3_with_assign_and_fresh]
  crush
  . introB
    subst_eqs
    simp at *
    crush <;> simp [*]
  . introB
    crush <;> simp [*]


example : E3BS2 ε testEnv (.callArgPrep "recursive_e3" [n, k] []) pc σ pc' σ' v ↔ σ = σ' ∧ pc = pc' ∧ v = n * k := by
  induction n generalizing σ σ' pc pc' v with
  | zero =>
    simp [testEnv, recursive_e3]
    conv in (E3BS2 _ _ _ _ _ _ _ _) =>
      rw [E3BS2.ite_true_iff (by simp; crush)]
    simp
    crush <;> {introB; subst_vars; crush}
  | succ n ih =>
    simp [testEnv, recursive_e3]
    conv in (E3BS2 _ _ _ _ _ _ _ _) => rw [E3BS2.ite_false_iff (by simp; crush)]
    simp
    crush
    introB
































/-
abbrev Assignment r := Nat → r

inductive Value r α where
| Comptime : α → Value r α
| Witness : ((Nat → r) → α) → Value r α

def Value.eval : Value r α → Assignment r → α := fun v σ => match v with
| Value.Comptime n => n
| Value.Witness f => f σ

instance {r : Type} : Pure (Value r) := ⟨Value.Comptime⟩

instance {r : Type} : Functor (Value r) where
  map f
  | Value.Comptime x => Value.Comptime (f x)
  | Value.Witness g => Value.Witness (fun n => f (g n))

instance {r: Type} : Applicative (Value r) where
  pure := Value.Comptime
  seq f x := match f, (x ()) with
  | Value.Comptime f, Value.Comptime x => Value.Comptime (f x)
  | f, x => Value.Witness fun ε => f.eval ε (x.eval ε)

instance {r: Type} : LawfulApplicative (Value r) where
  map_const := by
    intros; rfl
  id_map := by
    intro _ x
    cases x <;> rfl
  seqLeft_eq := by
    intro _ _ x y
    cases x <;> cases y <;> rfl
  seqRight_eq := by
    intro _ _ x y
    cases x <;> cases y <;> rfl
  pure_seq := by
    intro _ _ _ x
    cases x <;> rfl
  map_pure := by
    intros; rfl
  seq_pure := by
    intro _ _ f _
    cases f <;> rfl
  seq_assoc := by
    intro _ _ _ x y z
    cases x <;> cases y <;> cases z <;> rfl

@[simp]
lemma Value.eval_pure {r α} (x : α) (σ : Assignment r) : (pure x : Value r α).eval σ = x := rfl

@[simp]
lemma Value.eval_seq {r α β} (f : Value r (α → β)) (x : Value r α) (σ : Assignment r) : (f <*> x).eval σ = (f.eval σ) (x.eval σ) := by
  cases f <;> cases x <;> rfl

@[simp]
lemma Value.eval_map {r α β} (f : α → β) (x : Value r α) (σ : Assignment r) : (f <$> x).eval σ = f (x.eval σ) := by
  cases x <;> rfl

@[simp]
lemma Value.eval_witness_def {r α} (f : (Nat → r) → α) (σ : Assignment r) : (Value.Witness f).eval σ = f σ := rfl

def Scope := Ident → Value ℕ ℕ

def Env := Ident → Option E3

inductive E3BS : Env → E3 → Nat → Scope → Nat → Scope → Value Nat Nat → (Assignment ℕ → Prop) → Prop where
| lit {pc n σ} : E3BS Γ (E3.lit n) pc σ pc σ (pure n) (fun _ => True)
| var {pc x σ} : E3BS Γ (E3.var x) pc σ pc σ (σ x) (fun _ => True)
| eq:
  E3BS Γ e₁ pc₀ σ₀ pc₁ σ₁ v₁ p₁ →
  E3BS Γ e₂ pc₁ σ₁ pc₂ σ₂ v₂ p₂ →
  E3BS Γ (E3.eq e₁ e₂) pc₀ σ₀ pc₂ σ₂ ((fun x y => if x = y then 1 else 0) <$> v₁ <*> v₂) (fun ε => p₁ ε ∧ p₂ ε)
| assert:
  E3BS Γ e pc₀ σ₀ pc₁ σ₁ v p →
  E3BS Γ (E3.assert e) pc₀ σ₀ pc₁ σ₁ (pure 0) (fun ε => p ε ∧ v.eval ε = 1)
| seq:
  E3BS Γ e₁ pc₀ σ₀ pc₁ σ₁ v₁ p₁ →
  E3BS Γ e₂ pc₁ σ₁ pc₂ σ₂ v₂ p₂ →
  E3BS Γ (E3.seq e₁ e₂) pc₀ σ₀ pc₂ σ₂ v₂ (fun ε => p₁ ε ∧ p₂ ε)
| fresh:
  E3BS Γ E3.fresh pc σ (pc + 1) σ (Value.Witness fun ε => ε pc) (fun _ => True)
| assign:
  E3BS Γ e pc₀ σ₀ pc₁ σ₁ v p →
  E3BS Γ (.assign i e) pc₀ σ₀ pc₁ (fun x => if x = i then v else σ₁ x) v p
| ite_comp_true {cond}:
  E3BS Γ cond pc σ pc' σ' (pure 1) p →
  E3BS Γ ifT pc' σ' pc'' σ'' v' p' →
  E3BS Γ (E3.ite cond ifT ifF) pc σ pc'' σ'' v' (fun ε => p ε ∧ p' ε)
| ite_comp_false {cond}:
  E3BS Γ cond pc σ pc' σ' (pure 0) p →
  E3BS Γ ifF pc' σ' pc'' σ'' v' p' →
  E3BS Γ (E3.ite cond ifT ifF) pc σ pc'' σ'' v' (fun ε => p ε ∧ p' ε)
| sub:
  E3BS Γ e₁ pc₀ σ₀ pc₁ σ₁ v₁ p₁ →
  E3BS Γ e₂ pc₁ σ₁ pc₂ σ₂ v₂ p₂ →
  E3BS Γ (E3.sub e₁ e₂) pc₀ σ₀ pc₂ σ₂ ((·-·) <$> v₁ <*> v₂) (fun ε => p₁ ε ∧ p₂ ε)
| add:
  E3BS Γ e₁ pc₀ σ₀ pc₁ σ₁ v₁ p₁ →
  E3BS Γ e₂ pc₁ σ₁ pc₂ σ₂ v₂ p₂ →
  E3BS Γ (E3.add e₁ e₂) pc₀ σ₀ pc₂ σ₂ ((·+·) <$> v₁ <*> v₂) (fun ε => p₁ ε ∧ p₂ ε)
| call {fname}:
  (h : (Γ fname).isSome) →
  E3BS Γ ((Γ fname).get h) pc₀ σ₀ pc₁ σ₁ v p →
  E3BS Γ (E3.call fname) pc₀ σ₀ pc₁ σ₁ v p

lemma E3BS.conclusion_congr {e pc σ pc' σ' v p p'} (h : E3BS Γ e pc σ pc' σ' v p) (h' : p = p') : E3BS Γ e pc σ pc' σ' v p' := by
  subst h'; assumption

lemma E3BS.result_congr {e pc σ pc' σ' v v' p} (h : E3BS Γ e pc σ pc' σ' v p) (h' : v = v') : E3BS Γ e pc σ pc' σ' v' p := by
  subst h'; assumption

lemma E3BS.result_scope_congr {e pc σ pc' σ₀ σ₁ v p} (h : E3BS Γ e pc σ pc' σ₀ v p) (h' : σ₀ = σ₁) : E3BS Γ e pc σ pc' σ₁ v p := by
  subst h'; assumption

example : E3BS Γ ex3_simple n σ n σ (pure 0) (fun ε => (σ "x").eval ε = 1) := by
  apply E3BS.conclusion_congr
  apply E3BS.assert
  apply E3BS.eq
  apply E3BS.var
  apply E3BS.lit
  unfold Value.eval
  cases (σ "x") <;> simp [Value.eval]

example : ∃σ₁ v, E3BS Γ ex3_with_assign_and_fresh n σ (n+1) σ₁ v (fun ε => (σ "y").eval ε = (σ "z").eval ε ∧ ε n = (σ "y").eval ε) := by
  apply Exists.intro
  apply Exists.intro
  unfold ex3_with_assign_and_fresh
  apply E3BS.conclusion_congr
  apply E3BS.seq
  apply E3BS.assign
  apply E3BS.fresh
  apply E3BS.seq
  apply E3BS.assert
  apply E3BS.eq
  apply E3BS.var
  apply E3BS.var
  apply E3BS.assert
  apply E3BS.eq
  apply E3BS.var
  apply E3BS.var
  ext ε
  simp
  apply Iff.intro <;> tauto



example (hpn : σ "n" = pure n):
  E3BS (fun _ => some recursive_e3) recursive_e3 m σ m (fun i => if i = "n" then pure 0 else σ i) (if n = 0 then pure 0 else (n*·) <$> σ "k") (fun _ => True) := by
  induction n generalizing σ with
  | zero =>
    apply E3BS.conclusion_congr
    apply E3BS.ite_comp_true
    apply E3BS.result_congr
    apply E3BS.eq
    apply E3BS.var
    apply E3BS.lit
    rw [hpn]
    rfl
    apply E3BS.result_scope_congr
    apply E3BS.lit
    apply funext
    intro
    split <;> simp [*]
    simp
  | succ n ih =>
    apply E3BS.conclusion_congr
    apply E3BS.ite_comp_false
    apply E3BS.result_congr
    apply E3BS.eq
    apply E3BS.var
    apply E3BS.lit
    simp [hpn]
    apply E3BS.seq
    apply E3BS.assign
    apply E3BS.sub
    apply E3BS.var
    apply E3BS.lit
    apply E3BS.result_congr
    apply E3BS.add
    apply E3BS.call (by rfl)
    apply ih
    simp [hpn]
    apply E3BS.result_scope_congr
    apply E3BS.var
    simp [hpn]
    apply funext
    intro i
    split <;> simp
    simp [Nat.succ_mul]
    split <;> cases σ "k" <;> simp [*, Seq.seq, Value.eval, Functor.map]
    simp

#print recursive_e3
-/
