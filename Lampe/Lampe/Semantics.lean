import Lampe.Ast
import Lampe.Value
import Lampe.Syntax -- TODO remove - testing

theorem simplify_binder {p : α → Prop} (hp : ∀x, p x → y = x) : (∃x, p x) ↔ p y := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rw [hp x hp']
    assumption
  · intro hp'
    apply Exists.intro y
    assumption

syntax "introB": tactic
macro_rules | `(tactic|introB) => `(tactic | (intros ; try casesm* _ ∧ _, ∃_, _))

syntax "ex_dsch" :tactic
macro_rules | `(tactic|ex_dsch) => `(tactic | (introB; (first | assumption | (symm; assumption))))

syntax "binder_simp" : tactic
macro_rules
| `(tactic | binder_simp) =>
  `(tactic | repeat (first | simp (disch := ex_dsch) only [and_assoc, simplify_binder, ←exists_and_left, ←exists_and_right, true_and, and_true, ite_true] | simp [-exists_and_left, -exists_and_right]))

namespace Lampe

variable (P : Nat)

def Assignment := Nat → Value P

def Env := Ident → Option Function

structure State where
memory : Nat → Option (Value P)
nextFreeMemory : Nat

def Env.ofModule (m : Module): Env := fun i => (m.decls.find? fun d => d.name == i).map (·.fn)

@[simp]
theorem Env.ofModule_def (m : Module) (i : Ident) : Env.ofModule m i = (m.decls.find? fun d => d.name == i).map (·.fn) := by
  rfl

inductive LocalVal where
| value : Value P → LocalVal
| autoDeref : Nat → LocalVal

def Scope := Ident → Option (LocalVal P)

def Scope.update {P:Nat} (sc : Scope P) (x : Ident) (v : LocalVal P) : Scope P := fun y => if x = y then some v else sc y

@[simp]
theorem Scope.update_get_eq {P:Nat} {sc : Scope P} {x : Ident} {v : LocalVal P} : sc.update x v x = some v := by
  simp [Scope.update]

@[simp]
theorem Scope.update_get_of_neq {P:Nat} {sc : Scope P} {x y: Ident} {v : LocalVal P} (h : x ≠ y) : sc.update x v y = sc y := by
  simp [Scope.update]
  intro
  tauto

inductive ExprAux where
| expr : Expr → ExprAux
| callArgPrep : FunctionIdent → List (Value P) → List Expr → ExprAux

def ExprAux.inductionOn
  {motive : ExprAux P → Prop}
  (lit : ∀a, motive (.expr (.lit a)))
  (var : ∀x, motive (.expr (.var x)))
  (declareVar : ∀x e, motive (.expr e) → motive (.expr (.declareVar x e)))
  (declareMutVar : ∀x e, motive (.expr e) → motive (.expr (.declareMutVar x e)))
  (assignMut : ∀x e, motive (.expr e) → motive (.expr (.assignMut x e)))
  (require : ∀e, motive (.expr e) → motive (.expr (.assert e)))
  (unconstrained : motive (.expr .fresh))
  (block_nil : ∀e, motive (.expr e) → motive (.expr (.block []  e)))
  (block_cons : ∀hd e es, motive (.expr hd) → motive (.expr (.block es e)) → motive (.expr (.block (hd :: es) e)))
  (call_nil : ∀f, motive (.expr (.call f [])))
  (call_cons : ∀f a as, motive (.expr a) → motive (.expr (.call f as)) → motive (.expr (.call f (a::as))))
  (ite : ∀c t e, motive (.expr c) → motive (.expr t) → motive (.expr e) → motive (.expr (.ite c t e)))
  (skip : motive (.expr .skip))
  (loop : ∀i c b e, motive (.expr c) → motive (.expr b) → motive (.expr e) → motive (.expr (.loop i c b e)))
  (callArgPrep_nil : ∀f vs, motive (.callArgPrep f vs []))
  (callArgPrep_cons : ∀f a as vs, motive (.expr a) → motive (.callArgPrep f vs as) → motive (.callArgPrep f vs (a::as))):
  ∀e, motive e := by
  intro e
  cases e with
  | callArgPrep f vs es =>
    induction es with
    | nil => apply callArgPrep_nil
    | cons e es ih =>
      apply callArgPrep_cons _ _ _ _ ?_ ih
      induction e using Expr.inductionOn <;> tauto
  | expr e => induction e using Expr.inductionOn <;> tauto

inductive BigStepBuiltin : Builtin → List (Value P) → Value P → Prop where
| eq : BigStepBuiltin .eq [v1, v2] ⟨.bool, (v1 == v2)⟩
| assert : BigStepBuiltin .assert [⟨.bool, true⟩] ⟨.unit, ()⟩
| add : BigStepBuiltin .add [⟨.field, n1⟩, ⟨.field, n2⟩] ⟨.field, n1 + n2⟩
| sub : BigStepBuiltin .sub [⟨.field, n1⟩, ⟨.field, n2⟩] ⟨.field, n1 - n2⟩

@[simp]
theorem BigStepBuiltin.sub_field_iff : BigStepBuiltin P .sub [⟨.field, n1⟩, ⟨.field, n2⟩] v ↔ v = ⟨.field, n1 - n2⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.sub

@[simp]
theorem BigStepBuiltin.add_field_iff : BigStepBuiltin P .add [⟨.field, n1⟩, ⟨.field, n2⟩] v ↔ v = ⟨.field, n1 + n2⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.add

@[simp]
theorem BigStepBuiltin.eq_iff : BigStepBuiltin P .eq [v1, v2] v ↔ v = ⟨.bool, (v1 == v2)⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.eq

@[simp]
theorem BigStepBuiltin.assert_iff : BigStepBuiltin P .assert [v] r ↔ v = ⟨.bool, true⟩ ∧ r = .unit P := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.assert

inductive BigStepAux : Env → State P → Scope P → ExprAux P → State P → Scope P → Value P → Prop where
| lit : BigStepAux Γ st sc (.expr (.lit n)) st sc ⟨.field, n⟩
| varValue : sc x = some (LocalVal.value v) → BigStepAux Γ st sc (.expr (.var x)) st sc v
| varDeref : sc x = some  (LocalVal.autoDeref ptr) → st.memory ptr = some v → BigStepAux Γ st sc (.expr (.var x)) st sc v
| declareVar :
  BigStepAux Γ st sc (.expr e) st' sc v →
  BigStepAux Γ st sc (.expr (.declareVar x e)) st' (sc.update x (.value v)) (.unit P)
| callArgPrepBuiltinDone :
  BigStepBuiltin P b vs v →
  BigStepAux Γ st sc (.callArgPrep (.builtin b) vs []) st sc v
| callArgPrepDeclDone:
    (Γ fname = some ⟨params, body⟩) →
    BigStepAux Γ st (fun x => some (.value $ args.get! (params.indexOf x))) (.expr body) st' sc' v →
    BigStepAux Γ st sc (.callArgPrep (.decl fname) args []) st' sc v
| callArgPrepNext:
    BigStepAux Γ st sc (.expr e) st' sc a →
    BigStepAux Γ st' sc (.callArgPrep f (args ++ [a]) es) st'' sc'' v →
    BigStepAux Γ st sc (.callArgPrep f args (e::es)) st'' sc'' v
| call:
    BigStepAux Γ st sc (.callArgPrep f [] args) st' sc' v →
    BigStepAux Γ st sc (.expr (.call f args)) st' sc' v
| fresh:
    ∀v, BigStepAux Γ st sc (.expr .fresh) st sc v
| blockNext:
    BigStepAux Γ st sc (.expr e) st' sc' a →
    BigStepAux Γ st' sc' (.expr (.block es r)) st'' sc' v →
    BigStepAux Γ st sc (.expr (.block (e::es) r)) st'' sc v
| blockDone:
    BigStepAux Γ st sc (.expr r) st' sc' v →
    BigStepAux Γ st sc (.expr (.block [] r)) st' sc v
| iteTrue:
    BigStepAux Γ st sc (.expr c) st' sc ⟨.bool, true⟩ →
    BigStepAux Γ st' sc (.expr t) st'' sc v →
    BigStepAux Γ st sc (.expr (.ite c t e)) st'' sc v
| iteFalse:
    BigStepAux Γ st sc (.expr c) st' sc ⟨.bool, false⟩ →
    BigStepAux Γ st' sc (.expr e) st'' sc v →
    BigStepAux Γ st sc (.expr (.ite c t e)) st'' sc v


@[simp]
theorem BigStepAux.lit_iff: BigStepAux P Γ st sc (.expr (.lit n)) st' sc' v ↔ st = st' ∧ sc = sc' ∧ v = ⟨.field, n⟩ := by
  apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.lit])

@[simp]
theorem BigStepAux.var_iff: BigStepAux P Γ st sc (.expr (.var x)) st' sc' v ↔ (sc x = some (.value v) ∨ (∃ptr, sc x = some (.autoDeref ptr) ∧ st.memory ptr = some v)) ∧ st = st' ∧ sc = sc' := by
  apply Iff.intro
  · rintro ⟨_|_⟩ <;> simp_all
  · rintro ⟨(_|⟨ptr, _, _⟩), _, _, _⟩
    · simp_all [BigStepAux.varValue]
    · subst_vars
      apply BigStepAux.varDeref <;> assumption

@[simp]
theorem BigStepAux.call_iff:
  BigStepAux P Γ st sc (.expr (.call f args)) st' sc' v ↔
  BigStepAux P Γ st sc (.callArgPrep f [] args) st' sc' v := by
  apply Iff.intro
  · intro hp; cases hp
    assumption
  · introB
    apply BigStepAux.call; assumption

@[simp]
theorem BigStepAux.callArgPrepNext_iff:
  BigStepAux P Γ st sc (.callArgPrep f args (e::es)) st' sc' v ↔
  ∃a st'', BigStepAux P Γ st sc (.expr e) st'' sc a ∧ BigStepAux P Γ st'' sc (.callArgPrep f (args++[a]) es) st' sc' v := by
  apply Iff.intro
  · intro hp; cases hp
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · introB
    apply BigStepAux.callArgPrepNext <;> assumption

theorem BigStepAux.callArgPrepDeclDone_iff:
  BigStepAux P Γ st sc (.callArgPrep (.decl fname) args []) st' sc' v ↔
  ∃params body sc'', Γ fname = some ⟨params, body⟩ ∧ BigStepAux P Γ st (fun x => some (.value $ args.get! (params.indexOf x))) (.expr body) st' sc'' v ∧ sc' = sc := by
  apply Iff.intro
  · intro hp; cases hp
    repeat apply Exists.intro
    apply And.intro <;> try assumption
    apply And.intro <;> try assumption
    rfl
  · introB
    subst_vars
    apply BigStepAux.callArgPrepDeclDone <;> assumption

@[simp]
theorem BigStepAux.callArgPrepBultinDone_iff:
  BigStepAux P Γ st sc (.callArgPrep (.builtin b) vs []) st' sc' v ↔ BigStepBuiltin P b vs v ∧ st = st' ∧ sc = sc' := by
  apply Iff.intro
  · intro hp; cases hp; simp_all
  · intro hp
    simp_all [BigStepAux.callArgPrepBuiltinDone]

@[simp]
theorem BigStepAux.blockNext_iff:
  BigStepAux P Γ st sc (.expr (.block (e::es) r)) st' sc' v ↔
  sc' = sc ∧ ∃a st'' sc'', BigStepAux P Γ st sc (.expr e) st'' sc'' a ∧ BigStepAux P Γ st'' sc'' (.expr (.block es r)) st' sc'' v := by
  apply Iff.intro
  · intro hp; cases hp
    simp
    repeat apply Exists.intro
    apply And.intro <;> assumption
  · introB
    simp_all
    apply BigStepAux.blockNext <;> assumption

@[simp]
theorem BigStepAux.blockDone_iff:
  BigStepAux P Γ st sc (.expr (.block [] r)) st' sc' v ↔ sc' = sc ∧ ∃ sc'', BigStepAux P Γ st sc (.expr r) st' sc'' v := by
  apply Iff.intro
  · intro hp; cases hp;
    simp
    apply Exists.intro
    assumption
  · introB
    simp_all
    apply BigStepAux.blockDone; assumption

@[simp]
theorem BigStepAux.declareVar_iff:
  BigStepAux P Γ st sc (.expr (.declareVar x e)) st' sc' v ↔
  ∃a, BigStepAux P Γ st sc (.expr e) st' sc a ∧ v = .unit P ∧ sc' = sc.update x (.value a) := by
  apply Iff.intro
  · intro hp; cases hp
    repeat apply Exists.intro
    apply And.intro <;> try assumption
    apply And.intro <;> try rfl
  · introB
    subst_vars
    apply BigStepAux.declareVar
    assumption

@[simp]
theorem BigStepAux.unconstrained_iff:
  BigStepAux P Γ st sc (.expr .fresh) st' sc' v ↔ st = st' ∧ sc = sc' := by
  apply Iff.intro
  · intro hp; cases hp; simp_all
  · rintro ⟨⟨_⟩, ⟨_⟩⟩
    apply BigStepAux.fresh

@[simp]
theorem BigStepAux.ite_iff:
  BigStepAux P Γ st sc (.expr (.ite c t e)) st' sc' v ↔
  sc = sc' ∧ ∃v' st'', BigStepAux P Γ st sc (.expr c) st'' sc v' ∧
    ((v' = ⟨.bool, true⟩ ∧ BigStepAux P Γ st'' sc (.expr t) st' sc v) ∨
     (v' = ⟨.bool, false⟩ ∧ BigStepAux P Γ st'' sc (.expr e) st' sc v)) := by
  apply Iff.intro
  · intro hp
    cases hp
    · simp
      repeat apply Exists.intro
      apply And.intro
      · assumption
      apply Or.inl
      tauto
    · simp
      repeat apply Exists.intro
      apply And.intro
      · assumption
      apply Or.inr
      tauto
  · introB
    casesm* _ ∨ _
    · simp_all
      apply BigStepAux.iteTrue <;> tauto
    · simp_all
      apply BigStepAux.iteFalse <;> tauto


end Lampe



abbrev testMod := noir! {
  fn recursiveMul(n,k) {
    if n == 0 then 0 else {
      let n = n - 1;
      k + recursiveMul(n, k)
    }
  }

  fn assertEq(a,b) {
    let x = fresh;
    assert(x == a);
    assert(x == b);
  }

  fn lt_fallback(x, y) {
    let num_bytes = ((as_u32(field::modulus_num_bits()) + 7) / 8);
    let x_bytes = field::Field::to_le_bytes(x, num_bytes);
    let y_bytes = field::Field::to_le_bytes(y, num_bytes);
    let mut x_is_lt = false;
    let mut done = false;
    for i in 0 .. num_bytes {
        if (!done) then {
            let x_byte = as_u8(x_bytes[((num_bytes - 1) - i)]);
            let y_byte = as_u8(y_bytes[((num_bytes - 1) - i)]);
            let bytes_match = (x_byte == y_byte);
            if (!bytes_match) then {
                x_is_lt = (x_byte < y_byte);
                done = true;
            }
        }
    };
    x_is_lt
  }
}

open Lampe

theorem assignableEq:
  BigStepAux P (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "assertEq") [a, b] []) st' sc' v ↔
  a = b ∧ v = .unit P ∧ st = st' ∧ sc = sc' := by
  simp only [BigStepAux.callArgPrepDeclDone_iff]
  binder_simp
  apply Iff.intro
  · introB
    simp_all
  · introB
    subst_vars

    repeat apply Exists.intro
    simp
    repeat apply (And.intro rfl)
    simp
    repeat apply (And.intro rfl)
    rfl

abbrev P := 17

theorem assignableRecursiveMul:
  BigStepAux P (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "recursiveMul") [⟨.field, a⟩, ⟨.field, b⟩] []) st' sc' v ↔
  v = ⟨.field, a * b⟩ ∧ st = st' ∧ sc = sc' := by
  rcases a with ⟨a, ha⟩
  induction a generalizing sc sc' v with
  | zero =>
    simp only [BigStepAux.callArgPrepDeclDone_iff]
    binder_simp
    tauto
  | succ a ih =>
    have ap1_def : (⟨a + 1, ha⟩ : ZMod P) = (⟨a, by linarith⟩:ZMod P) + 1 := by
      congr
      repeat (rw [Nat.mod_eq_of_lt] <;> try linarith)

    have : (⟨a, by linarith⟩: ZMod P) + 1 ≠ 0 := by
      intro h
      injection h with h
      repeat rw [Nat.mod_eq_of_lt] at h
      any_goals linarith
      rw [Nat.mod_eq_of_lt]
      any_goals linarith

    simp only [BigStepAux.callArgPrepDeclDone_iff]
    binder_simp
    simp only [this, ap1_def, ih]
    binder_simp
    simp only [this, ap1_def, ih]
    binder_simp
    ring_nf
    tauto
