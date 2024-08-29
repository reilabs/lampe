import Lampe.Ast
import Lampe.Value
import Lampe.Data.Field
import Lampe.Syntax -- TODO remove - testing
import Lean.Meta.Tactic.Simp.Main
import Mathlib

theorem simplify_binder {p : α → Prop} (hp : ∀x, p x → y = x) : (∃x, p x) ↔ p y := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rw [hp x hp']
    assumption
  · intro hp'
    apply Exists.intro y
    assumption

theorem simplify_binder_under_ex {p : α → Prop} {q : β → α} (hp : ∀x, p x → ∃y, x = q y) : (∃x, p x) ↔ ∃y, p (q y) := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rcases hp x hp' with ⟨_, ⟨_⟩⟩
    apply Exists.intro
    assumption
  · intro ⟨y, hp'⟩
    apply Exists.intro
    assumption

syntax "introB": tactic
macro_rules | `(tactic|introB) => `(tactic | (intros ; try casesm* _ ∧ _, ∃_, _))

syntax "ex_dsch" :tactic
macro_rules | `(tactic|ex_dsch) => `(tactic | (introB; (first | assumption | (symm; assumption))))

syntax "binder_simp" : tactic
macro_rules
| `(tactic | binder_simp) =>
  `(tactic | (first | simp (disch := ex_dsch) only [simplify_binder]))

namespace Lampe

variable (P : Nat)

def Assignment := Nat → Value P

def Env := Ident → Option Function

structure State where
memory : Nat → Option (Value P)
nextFreeMemory : Nat

namespace State

instance : Inhabited (State P) := ⟨⟨fun _ => none, 0⟩⟩

def nextPtr : State P → Nat := nextFreeMemory

def alloc {P} : State P → Value P → State P := fun st v =>
  ⟨(fun i => if i = st.nextFreeMemory then some v else st.memory i), st.nextFreeMemory + 1⟩

def set {P} : State P → Nat → Value P → State P := fun st i v =>
  ⟨(fun j => if j = i then some v else st.memory j), st.nextFreeMemory⟩

@[simp]
theorem alloc_inj {st : State P} {v v' : Value P} : st.alloc v = st.alloc v' ↔ v = v' := by
  apply Iff.intro
  · intro h
    simp [alloc] at h
    apply_fun (fun f => f st.nextFreeMemory) at h
    simp at h
    simp [h]
  · rintro ⟨rfl⟩
    rfl

@[simp]
theorem set_inj {st : State P} {i : Nat} {v v' : Value P} : st.set i v = st.set i v' ↔ v = v' := by
  apply Iff.intro
  · intro h
    simp [set] at h
    apply_fun (fun f => f i) at h
    simp at h
    simp [h]
  · rintro ⟨rfl⟩
    rfl

@[simp]
theorem alloc_nextPtr {st : State P} {v : Value P} : (st.alloc v).memory st.nextPtr = v := by
  simp [nextPtr, alloc]

-- @[simp]
-- theorem alloc_nextPtr_alloc {}

-- @[simp]
-- theorem get_alloc_succ : (st.alloc v)

end State

def Env.ofModule (m : Module): Env := fun i => (m.decls.find? fun d => d.name == i).map (·.fn)

@[reducible]
def Env.extend (Γ₁ : Env) (Γ₂ : Env) : Env := fun i => Γ₁ i <|> Γ₂ i

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
| loopProgress : Nat → Nat → Nat → Ident → Expr → ExprAux

def ExprAux.inductionOn
  {motive : ExprAux P → Prop}
  (lit : ∀a t, motive (.expr (.lit a t)))
  (var : ∀x, motive (.expr (.var x)))
  (declareVar : ∀x e, motive (.expr e) → motive (.expr (.declareVar x e)))
  (declareMutVar : ∀x e, motive (.expr e) → motive (.expr (.declareMutVar x e)))
  (assignMut : ∀x e, motive (.expr e) → motive (.expr (.assignMut x e)))
  (require : ∀e, motive (.expr e) → motive (.expr (.assert e)))
  (unconstrained : motive (.expr .fresh))
  (block_nil : ∀e, motive (.expr e) → motive (.expr (.block []  e)))
  (block_cons : ∀hd e es, motive (.expr hd) → motive (.expr (.block es e)) → motive (.expr (.block (hd :: es) e)))
  (call_nil : ∀f, motive (.expr (.call f [])))
  (call_cons : ∀f a args, motive (.expr a) → motive (.expr (.call f args)) → motive (.expr (.call f (a::args))))
  (ite : ∀c t e, motive (.expr c) → motive (.expr t) → motive (.expr e) → motive (.expr (.ite c t e)))
  (skip : motive (.expr .skip))
  (loop : ∀i c b e, motive (.expr c) → motive (.expr b) → motive (.expr e) → motive (.expr (.loop i c b e)))
  (loopProgress : ∀s i j x e, motive (.expr e) → motive (.loopProgress s i j x e))
  (callArgPrep_nil : ∀f vs, motive (.callArgPrep f vs []))
  (callArgPrep_cons : ∀f a args vs, motive (.expr a) → motive (.callArgPrep f vs args) → motive (.callArgPrep f vs (a::args))):
  ∀e, motive e := by
  intro e
  cases e with
  | callArgPrep f vs es =>
    induction es with
    | nil => apply callArgPrep_nil
    | cons e es ih =>
      apply callArgPrep_cons _ _ _ _ ?_ ih
      induction e using Expr.inductionOn <;> tauto
  | loopProgress s i j x e =>
      apply loopProgress _ _ _ _ _ ?_
      induction e using Expr.inductionOn <;> tauto
  | expr e => induction e using Expr.inductionOn <;> tauto

inductive BigStepBuiltin : Builtin → List (Value P) → Value P → Prop where
| eq : BigStepBuiltin .eq [v1, v2] ⟨.bool, (v1 == v2)⟩
| ltU : BigStepBuiltin .lt [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.bool, n1 < n2⟩
| assert : BigStepBuiltin .assert [⟨.bool, true⟩] ⟨.unit, ()⟩
| addF : BigStepBuiltin .add [⟨.field, n1⟩, ⟨.field, n2⟩] ⟨.field, n1 + n2⟩
| addU : (n1.val + n2.val < 2 ^ s) → BigStepBuiltin .add [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.u s, n1 + n2⟩ -- oflow error in circuit as well?
| sub : BigStepBuiltin .sub [⟨.field, n1⟩, ⟨.field, n2⟩] ⟨.field, n1 - n2⟩
| subU : (n1.val ≤ n2.val) → BigStepBuiltin .sub [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.u s, n1 - n2⟩ -- oflow error in circuit as well?
| divU : BigStepBuiltin .div [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.u s, n1 / n2⟩ -- div 0?
| toLeBytes {result : List (U 8)} {byteLen : U 32} :
  (n = ∑i, (result.get i : ZMod P) * 256 ^ i.val) →
  (result.length = byteLen) →
  BigStepBuiltin .toLeBytes [⟨.field, n⟩, ⟨.u 32, byteLen⟩] ⟨.slice (.u 8), result⟩
| modulusNumBits : BigStepBuiltin .modulusNumBits [] ⟨.u 64, Field.numBits P⟩ -- wrap or throw?
| castU : BigStepBuiltin (.cast (.u s)) [⟨.u s', i⟩] ⟨.u s, i⟩
| not : BigStepBuiltin .not [⟨.bool, b⟩] ⟨.bool, !b⟩
| index : (hp : i.val < s.length) → BigStepBuiltin .index [⟨.slice tp, s⟩, ⟨.u 32, i⟩] ⟨tp, s[i]⟩

@[simp]
theorem BigStepBuiltin.lt_u_iff : BigStepBuiltin P .lt [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.bool, n1 < n2⟩ := by
  apply Iff.intro <;> {
    introB
    try casesm BigStepBuiltin _ _ _ _
    simp_all [BigStepBuiltin.ltU]
  }

@[simp]
theorem BigStepBuiltin.sub_field_iff : BigStepBuiltin P .sub [⟨.field, n1⟩, ⟨.field, n2⟩] v ↔ v = ⟨.field, n1 - n2⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.sub

@[simp]
theorem BigStepBuiltin.sub_u_iff : BigStepBuiltin P .sub [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.u s, n1 - n2⟩ ∧ n1.val ≤ n2.val := by
  apply Iff.intro
  · intro hp; cases hp; simpa
  · introB
    simp_all [BigStepBuiltin.subU]

@[simp]
theorem BigStepBuiltin.add_field_iff : BigStepBuiltin P .add [⟨.field, n1⟩, ⟨.field, n2⟩] v ↔ v = ⟨.field, n1 + n2⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply addF

@[simp]
theorem BigStepBuiltin.add_u_iff : BigStepBuiltin P .add [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.u s, n1 + n2⟩ ∧ (n1.val + n2.val < 2^s) := by
  apply Iff.intro
  · intro hp; cases hp; simpa
  · introB
    simp_all [BigStepBuiltin.addU]

@[simp]
theorem BigStepBuiltin.div_u_iff : BigStepBuiltin P .div [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.u s, n1 / n2⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · introB
    simp_all [BigStepBuiltin.divU]

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

@[simp]
theorem BigStepBuiltin.modulusNumBits_iff : BigStepBuiltin P .modulusNumBits [] v ↔ v = ⟨.u 64, Field.numBits P⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.modulusNumBits

@[simp]
theorem BigStepBuiltin.toLeBytes_iff : BigStepBuiltin P .toLeBytes [⟨.field, n⟩, ⟨.u 32, len⟩] result ↔  ∃r, result = ⟨.slice (.u 8), r⟩ ∧ (n = ∑i, ((r.get i) : ZMod P) * 256 ^ i.val) ∧ (r.length = len) := by
  apply Iff.intro
  · intro hp
    cases hp
    apply Exists.intro
    apply And.intro <;> try rfl
    apply And.intro <;> assumption
  · introB
    simp_all [BigStepBuiltin.toLeBytes]

@[simp]
theorem BigStepBuiltin.castU_iff : BigStepBuiltin P (.cast (.u s)) [⟨.u s', i⟩] v ↔ v = ⟨.u s, i⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.castU

@[simp]
theorem BigStepBuiltin.not_iff : BigStepBuiltin P .not [⟨.bool, b⟩] v ↔ v = ⟨.bool, !b⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp
  · intro hp
    simp [hp]
    apply BigStepBuiltin.not

@[simp]
theorem BigStepBuiltin.index_iff : BigStepBuiltin P .index [⟨.slice tp, s⟩, ⟨.u 32, i⟩] v ↔ ∃ (hp: i.val < s.length), v = ⟨tp, s[i]⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp_all
  · intro hp
    cases hp
    simp_all
    apply BigStepBuiltin.index


inductive BigStepAux : Env → State P → Scope P → ExprAux P → State P → Scope P → Value P → Prop where
| skip : BigStepAux Γ st sc (.expr .skip) st sc ⟨.unit, ()⟩
| litNone : BigStepAux Γ st sc (.expr (.lit n .none)) st sc ⟨.field, n⟩
| litU : BigStepAux Γ st sc (.expr (.lit n (.some (.u s)))) st sc ⟨.u s, n⟩
| litFalse : BigStepAux Γ st sc (.expr (.lit 0 (.some .bool))) st sc ⟨.bool, false⟩
| litTrue : BigStepAux Γ st sc (.expr (.lit 1 (.some .bool))) st sc ⟨.bool, true⟩
| varValue : sc x = some (LocalVal.value v) → BigStepAux Γ st sc (.expr (.var x)) st sc v
| varDeref : sc x = some (LocalVal.autoDeref ptr) → st.memory ptr = some v → BigStepAux Γ st sc (.expr (.var x)) st sc v
| declareVar :
  BigStepAux Γ st sc (.expr e) st' sc v →
  BigStepAux Γ st sc (.expr (.declareVar x e)) st' (sc.update x (.value v)) (.unit P)
| declareMutVar :
  BigStepAux Γ st sc (.expr e) st' sc v →
  BigStepAux Γ st sc (.expr (.declareMutVar x e)) (st'.alloc v) (sc.update x (.autoDeref st'.nextPtr)) (.unit P)
| assignMut :
  sc x = some (.autoDeref ptr) →
  BigStepAux Γ st sc (.expr e) st' sc v →
  BigStepAux Γ st sc (.expr (.assignMut x e)) (st'.set ptr v) sc (.unit P)
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
| loop:
    BigStepAux Γ st  sc (.expr lo) st' sc ⟨.u s, lov⟩ →
    BigStepAux Γ st' sc (.expr hi) st'' sc ⟨.u s, hiv⟩ →
    BigStepAux Γ st'' sc (.loopProgress s lov hiv i body) st''' sc v →
    BigStepAux Γ st sc (.expr (.loop i lo hi body)) st''' sc v
| loopCont:
    (lo < hi) →
    BigStepAux Γ st  (sc.update i (.value ⟨.u s, lo⟩)) (.expr body) st' (sc.update i (.value ⟨.u s, lo⟩)) _ →
    BigStepAux Γ st' sc (.loopProgress s lo.succ hi i body) st'' sc v →
    BigStepAux Γ st sc (.loopProgress s lo hi i body) st'' sc v
| loopDone:
    (lo ≥ hi) →
    BigStepAux Γ st sc (.loopProgress s lo hi i body) st sc ⟨.unit, ()⟩

@[simp]
theorem BigStepAux.skip_iff: BigStepAux P Γ st sc (.expr .skip) st' sc' v ↔ st = st' ∧ sc = sc' ∧ v = ⟨.unit, ()⟩ := by
  apply Iff.intro
  · intro hp; cases hp; simp_all
  · intro hp
    simp_all [BigStepAux.skip]

@[simp]
theorem BigStepAux.litNone_iff: BigStepAux P Γ st sc (.expr (.lit n .none)) st' sc' v ↔ st = st' ∧ sc = sc' ∧ v = ⟨.field, n⟩ := by
  apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litNone])

@[simp]
theorem BigStepAux.litU_iff: BigStepAux P Γ st sc (.expr (.lit n (.some (.u s)))) st' sc' v ↔ st = st' ∧ sc = sc' ∧ v = ⟨.u s, n⟩ := by
  apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litU])

@[simp]
theorem BigStepAux.litFalse_iff: BigStepAux P Γ st sc (.expr (.lit 0 (.some .bool))) st' sc' v ↔ st = st' ∧ sc = sc' ∧ v = ⟨.bool, false⟩ := by
  apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litFalse])

@[simp]
theorem BigStepAux.litTrue_iff: BigStepAux P Γ st sc (.expr (.lit 1 (.some .bool))) st' sc' v ↔ st = st' ∧ sc = sc' ∧ v = ⟨.bool, true⟩ := by
  apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litTrue])

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

theorem BigStepAux.callArgPrepDeclDone_iff2 (fname : String) (hp : Γ fname = some func):
  BigStepAux P Γ st sc (.callArgPrep (.decl fname) args []) st' sc' v ↔
  ∃sc'', BigStepAux P Γ st (fun x => some (.value $ args.get! (func.params.indexOf x))) (.expr func.body) st' sc'' v ∧ sc' = sc := by
  rw [BigStepAux.callArgPrepDeclDone_iff]
  simp [hp]
  cases func
  simp
  binder_simp
  simp

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
theorem BigStepAux.declareMutVar_iff:
  BigStepAux P Γ st sc (.expr (.declareMutVar x e)) st' sc' v ↔
  ∃a st'', BigStepAux P Γ st sc (.expr e) st'' sc a ∧ v = .unit P ∧ sc' = sc.update x (.autoDeref st''.nextPtr) ∧ st' = st''.alloc a := by
  apply Iff.intro
  · intro hp
    cases hp
    repeat apply Exists.intro
    apply And.intro <;> try assumption
    apply And.intro <;> try rfl
    apply And.intro <;> rfl
  · introB
    subst_vars
    apply BigStepAux.declareMutVar
    assumption

@[simp]
theorem BigStepAux.assignMut_iff:
  BigStepAux P Γ st sc (.expr (.assignMut x e)) st' sc' v ↔
  ∃ptr a st'', sc x = some (.autoDeref ptr) ∧ BigStepAux P Γ st sc (.expr e) st'' sc a ∧ v = .unit P ∧ st' = st''.set ptr a ∧ sc = sc' := by
  apply Iff.intro
  · intro hp
    cases hp
    repeat apply Exists.intro
    apply And.intro; assumption
    apply And.intro; assumption
    apply And.intro; rfl
    apply And.intro <;> rfl
  · introB
    subst_vars
    apply BigStepAux.assignMut <;> assumption

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

@[simp]
theorem BigStepAux.loop_iff:
  BigStepAux P Γ st sc (.expr (.loop i lo hi body)) st''' sc' v ↔
  ∃s st' st'' lov hiv, BigStepAux P Γ st sc (.expr lo) st' sc ⟨.u s, lov⟩ ∧ BigStepAux P Γ st' sc (.expr hi) st'' sc ⟨.u s, hiv⟩ ∧ BigStepAux P Γ st'' sc (.loopProgress s lov hiv i body) st''' sc v  ∧ sc = sc' := by
  apply Iff.intro
  · intro hp
    cases hp
    tauto
  · introB
    subst_vars
    apply BigStepAux.loop <;> assumption

theorem BigStepAux.loopCont_iff (hp : lo < hi):
  BigStepAux P Γ st sc (.loopProgress s lo hi i body) st'' sc' v ↔
  ∃a st',
    BigStepAux P Γ st (sc.update i (.value ⟨.u s, lo⟩)) (.expr body) st' (sc.update i (.value ⟨.u s, lo⟩)) a ∧
    BigStepAux P Γ st' sc (.loopProgress s lo.succ hi i body) st'' sc v ∧
    sc = sc' := by
  apply Iff.intro
  · intro hp
    cases hp
    · repeat apply Exists.intro
      apply And.intro <;> try assumption
      apply And.intro <;> try assumption
      rfl
    · linarith
  · introB
    subst_vars
    apply BigStepAux.loopCont <;> try assumption

@[simp]
theorem BigStepAux.loopDone_iff (hp : lo ≥ hi):
  BigStepAux P Γ st sc (.loopProgress s lo hi i body) st' sc' v ↔
  v = ⟨.unit, ()⟩ ∧ st = st' ∧ sc = sc':= by
  apply Iff.intro
  · intro hp
    cases hp <;> try linarith
    tauto
  · introB; subst_vars
    apply BigStepAux.loopDone
    assumption

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
    let num_bytes = (((field::modulus_num_bits() #as u 32) + (7: u 32)) / (8 : u 32));
    let x_bytes = field::Field::to_le_bytes(x, num_bytes);
    let y_bytes = field::Field::to_le_bytes(y, num_bytes);
    let mut x_is_lt = false;
    let mut done = false;
    for i in (0 : u 32) .. num_bytes {
        if (!done) then {
            let x_byte = x_bytes[((num_bytes - (1 : u 32)) - i)] #as u 8;
            let y_byte = y_bytes[((num_bytes - (1 : u 32)) - i)] #as u 8;
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

-- set_option trace.Meta.Tactic.simp.discharge true

syntax "ex_dsch2" :tactic
macro_rules
| `(tactic|ex_dsch2) =>
  `(tactic| introB; apply Exists.intro; assumption)

section macros
open Lean Elab.Tactic Parser.Tactic Lean.Meta
syntax "crush" : tactic
macro_rules
| `(tactic|crush) => `(tactic| repeat (first | simp | simp (disch := ex_dsch) only [simplify_binder] | simp (disch := ex_dsch2) only [simplify_binder_under_ex]))
end macros



@[simp]
theorem Scope.update_inj {sc : Scope P} : sc.update x v = sc.update x v' ↔ v = v' := by
  apply Iff.intro
  · intro h
    have : sc.update x v x = sc.update x v' x := by
      apply congr <;> simp [*]
    simp at this
    assumption
  · rintro ⟨rfl⟩
    rfl

theorem assignableEq:
  BigStepAux P (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "assertEq") [a, b] []) st' sc' v ↔
  a = b ∧ v = .unit P ∧ st = st' ∧ sc = sc' := by
  simp only [BigStepAux.callArgPrepDeclDone_iff]
  crush
  tauto

@[simp] theorem zmodPrimeIsFin [Fact (Nat.Prime P)]: ZMod P = Fin P := by
  have : ∃p, P = p + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    apply Nat.Prime.ne_zero
    apply Fact.out
  rcases this
  subst_vars
  rfl

theorem assignableRecursiveMul [Fact (Nat.Prime P)]:
  BigStepAux P (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "recursiveMul") [⟨.field, a⟩, ⟨.field, b⟩] []) st' sc' v ↔
  v = ⟨.field, a * b⟩ ∧ st = st' ∧ sc = sc' := by
  have : ∃p, P = p + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    apply Nat.Prime.ne_zero
    apply Fact.out
  rcases this with ⟨p, rfl⟩
  rcases a with ⟨a, ha⟩
  induction a generalizing sc sc' v with
  | zero =>
    simp only [BigStepAux.callArgPrepDeclDone_iff]
    crush
    tauto
  | succ a ih =>
    have ap1_def : (⟨a + 1, ha⟩ : ZMod (p+1)) = (⟨a, by linarith⟩) + 1 := by
      congr
      repeat (rw [Nat.mod_eq_of_lt] <;> try linarith)

    have : (⟨a, by linarith⟩: ZMod (p+1)) + 1 ≠ 0 := by
      intro h
      injection h with h
      repeat rw [Nat.mod_eq_of_lt] at h
      any_goals linarith
      rw [Nat.mod_eq_of_lt]
      any_goals linarith

    simp only [BigStepAux.callArgPrepDeclDone_iff]
    crush
    simp only [this, ap1_def, ih]
    crush
    simp only [this, ap1_def, ih]
    crush
    ring_nf
    tauto

def modulusNumBitsFn : Function := ⟨[], .call (.builtin .modulusNumBits) []⟩
def toLeBytesFn : Function := ⟨["self", "byte_len"], .call (.builtin .toLeBytes) [.var "self", .var "byte_len"]⟩


@[reducible]
def stdlib : Env := fun i => match i with
| "field::modulus_num_bits" => some modulusNumBitsFn
| "field::Field::to_le_bytes" => some toLeBytesFn
| _ => none

-- set_option trace.Meta.Tactic.simp.discharge true

def BigStepCall (P : Nat) (Γ : Env) (state : State P) (f : Function) (args : List (Value P)) (state' : State P) (v : Value P) :=
  ∃sc', BigStepAux P Γ state (fun x => some (.value $ args.get! (f.params.indexOf x))) (.expr f.body) state' sc' v

@[simp]
theorem modulusNumBits_sem : BigStepCall P Γ st modulusNumBitsFn [] st' v ↔ st = st' ∧ v = ⟨.u 64, Field.numBits P⟩ := by
  simp [BigStepCall, modulusNumBitsFn]; tauto

-- @[simp]
-- theorem toLeBytes_sem :
--     BigStepCall P Γ st toLeBytesFn [⟨.field, a⟩, ⟨.u 32, len⟩] st' v ↔
--     st = st' ∧ (Field.toLeBytes a).length ≤ len.val ∧ v = ⟨.slice (.u 8), Field.padEnd len.val $ Field.toLeBytes a⟩ := by
--   simp [BigStepCall, toLeBytesFn]; crush; tauto

theorem BigStepAux.callArgPrepDeclDone_iff3 (fname : String) (hp : Γ fname = some func) (P : Nat) {v : Value P} {st st' : State P} {args : List (Value P)} {sc sc' : Scope P}:
  BigStepAux P Γ st sc (.callArgPrep (.decl fname) args []) st' sc' v ↔
  BigStepCall P Γ st func args st' v ∧ sc' = sc := by
  simp [BigStepCall, BigStepAux.callArgPrepDeclDone_iff2 _ _ hp]

lemma Nat.eq_zero_of_lt_one : ∀n, n < 1 → n = 0 := by intros; linarith

example :
    ∃st' sc', BigStepAux 17 (stdlib.extend (Lampe.Env.ofModule testMod)) st sc (.callArgPrep (.decl "lt_fallback") [⟨.field, 10⟩, ⟨.field, 5⟩] []) st' sc' ⟨.bool, true⟩ := by
  simp (disch := with_unfolding_all rfl) only [BigStepAux.callArgPrepDeclDone_iff3]
  unfold BigStepCall
  crush
  simp (disch := with_unfolding_all conv_lhs => whnf) only [BigStepAux.callArgPrepDeclDone_iff3 "field::modulus_num_bits", BigStepAux.callArgPrepDeclDone_iff3 "field::Field::to_le_bytes"]
  crush
  unfold BigStepCall
  unfold toLeBytesFn
  crush
  simp [Field.numBits, Nat.log2]
  conv in (occs := *) (Fin.val _ / Fin.val _) => whnf
  simp [BigStepAux.loopCont_iff]
  crush
  apply And.intro
  · decide
  · apply Exists.intro
    use [10]
    crush
    apply And.intro (by decide)
    use [22]
    crush
    apply And.intro (by decide)
    apply And.intro rfl
    simp [State.alloc, State.set]




-- theorem ltFallbackSem : ∃a1 a2,
--   BigStepAux (P + 1) (stdlib.extend (Lampe.Env.ofModule testMod)) st sc (.callArgPrep (.decl "lt_fallback") [⟨.field, a⟩, ⟨.field, b⟩] []) st' sc' v ↔
--   v = ⟨.bool, a.val < b.val⟩ ∧ sc = sc' ∧ st' = (st.alloc a1).alloc a2 := by
--   simp (disch := with_unfolding_all rfl) only [BigStepAux.callArgPrepDeclDone_iff3]
--   unfold BigStepCall
--   crush
--   simp (disch := with_unfolding_all conv_lhs => whnf) only [BigStepAux.callArgPrepDeclDone_iff3 "field::modulus_num_bits", BigStepAux.callArgPrepDeclDone_iff3 "field::Field::to_le_bytes"]
--   crush
--   induction P using Nat.binaryRec with
--   | z =>
--     simp [Field.numBits, Nat.log2]
--     conv in (occs := *) (Fin.val _ / Fin.val _) => whnf
--     crush
--     simp [BigStepAux.loopCont_iff]
--     crush
--     rcases a with ⟨a, ha⟩
--     have : a = 0 := by linarith
--     cases this
--     rcases b with ⟨b, hb⟩
--     have : b = 0 := by linarith
--     cases this
--     simp [Field.toLeBytes, Field.toLeBytes.go, Field.padEnd]
--     repeat apply Exists.intro
--     apply Iff.intro
--     · introB
--       subst_vars
--     · sorry




    -- simp
  -- binder_simp
