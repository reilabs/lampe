import Lampe.Ast
import Lampe.Value
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
-- import Lampe.Syntax
import Mathlib

namespace Lampe

variable (P : Nat)

def Assignment := Nat → Value P

def Env := Ident → Option Function

#print Env

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
theorem Env.ofModule_def (m : Module) (i : Ident) : Env.ofModule m i = (m.decls.find? fun d => d.name == i).map (fun dcl => dcl.fn) := by
  rfl

inductive LocalVal where
| value : Value P → LocalVal
| autoDeref : Nat → LocalVal

-- def Scope := Ident → Option (LocalVal P)

-- def Scope.update {P:Nat} (sc : Scope P) (x : Ident) (v : LocalVal P) : Scope P := fun y => if x = y then some v else sc y

-- @[simp]
-- theorem Scope.update_get_eq {P:Nat} {sc : Scope P} {x : Ident} {v : LocalVal P} : sc.update x v x = some v := by
--   simp [Scope.update]

-- @[simp]
-- theorem Scope.update_get_of_neq {P:Nat} {sc : Scope P} {x y: Ident} {v : LocalVal P} (h : x ≠ y) : sc.update x v y = sc y := by
--   simp [Scope.update]
--   intro
--   tauto

-- def ExprAux.inductionOn
--   {motive : ExprAux P → Prop}
--   (lit : ∀a t, motive (.expr (.lit a t)))
--   (var : ∀x, motive (.expr (.var x)))
--   (declareVar : ∀x e, motive (.expr e) → motive (.expr (.declareVar x e)))
--   (declareMutVar : ∀x e, motive (.expr e) → motive (.expr (.declareMutVar x e)))
--   (assignMut : ∀x e, motive (.expr e) → motive (.expr (.assignMut x e)))
--   (require : ∀e, motive (.expr e) → motive (.expr (.assert e)))
--   (fresh : motive (.expr .fresh))
--   (block_nil : ∀e, motive (.expr e) → motive (.expr (.block []  e)))
--   (block_cons : ∀hd e es, motive (.expr hd) → motive (.expr (.block es e)) → motive (.expr (.block (hd :: es) e)))
--   (call_nil : ∀f, motive (.expr (.call f [])))
--   (call_cons : ∀f a args, motive (.expr a) → motive (.expr (.call f args)) → motive (.expr (.call f (a::args))))
--   (ite : ∀c t e, motive (.expr c) → motive (.expr t) → motive (.expr e) → motive (.expr (.ite c t e)))
--   (skip : motive (.expr .skip))
--   (loop : ∀i c b e, motive (.expr c) → motive (.expr b) → motive (.expr e) → motive (.expr (.loop i c b e)))
--   (loopProgress : ∀s i j x e, motive (.expr e) → motive (.loopProgress s i j x e))
--   (callArgPrep_nil : ∀f vs, motive (.callArgPrep f vs []))
--   (callArgPrep_cons : ∀f a args vs, motive (.expr a) → motive (.callArgPrep f vs args) → motive (.callArgPrep f vs (a::args))):
--   ∀e, motive e := by
--   intro e
--   cases e with
--   | callArgPrep f vs es =>
--     induction es with
--     | nil => apply callArgPrep_nil
--     | cons e es ih =>
--       apply callArgPrep_cons _ _ _ _ ?_ ih
--       induction e using Expr.inductionOn <;> tauto
--   | loopProgress s i j x e =>
--       apply loopProgress _ _ _ _ _ ?_
--       induction e using Expr.inductionOn <;> tauto
--   | expr e => induction e using Expr.inductionOn <;> tauto

inductive BigStepBuiltin : (inp: List Tp) → (out : Tp) → Builtin → HList (InstanceOf P) inp → InstanceOf P out → Prop where
| eq : BigStepBuiltin [a, a] .bool .eq h![v1, v2] (v1 == v2)
| ltU : BigStepBuiltin [.u s, .u s] .bool .lt h![n1, n2] (n1 < n2)
| assert : BigStepBuiltin [.bool] .unit .assert h![true] .unit
-- | addF : BigStepBuiltin .add [⟨.field, n1⟩, ⟨.field, n2⟩] ⟨.field, n1 + n2⟩
-- | addU : (n1.val + n2.val < 2 ^ s) → BigStepBuiltin .add [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.u s, n1 + n2⟩ -- oflow error in circuit as well?
-- | sub : BigStepBuiltin .sub [⟨.field, n1⟩, ⟨.field, n2⟩] ⟨.field, n1 - n2⟩
-- | subU : (n2.val ≤ n1.val) → BigStepBuiltin .sub [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.u s, n1 - n2⟩ -- oflow error in circuit as well?
-- | divU : BigStepBuiltin .div [⟨.u s, n1⟩, ⟨.u s, n2⟩] ⟨.u s, n1 / n2⟩ -- div 0?
-- | toLeBytes {result : List (U 8)} {byteLen : U 32} :
--   (n = ∑i, (result.get i : ZMod P) * 256 ^ i.val) →
--   (result.length = byteLen) →
--   BigStepBuiltin .toLeBytes [⟨.field, n⟩, ⟨.u 32, byteLen⟩] ⟨.slice (.u 8), result⟩
-- | modulusNumBits : BigStepBuiltin .modulusNumBits [] ⟨.u 64, Field.numBits P⟩ -- wrap or throw?
-- | castU : BigStepBuiltin (.cast (.u s)) [⟨.u s', i⟩] ⟨.u s, i⟩
-- | not : BigStepBuiltin .not [⟨.bool, b⟩] ⟨.bool, !b⟩
-- | index : (hp : i.val < s.length) → BigStepBuiltin .index [⟨.slice tp, s⟩, ⟨.u 32, i⟩] ⟨tp, s[i]⟩
| fresh : BigStepBuiltin [] tp .fresh h![] v

-- @[simp]
-- theorem BigStepBuiltin.lt_u_iff : BigStepBuiltin P .lt [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.bool, n1 < n2⟩ := by
--   apply Iff.intro <;> {
--     intro_cases
--     try casesm BigStepBuiltin _ _ _ _
--     simp_all [BigStepBuiltin.ltU]
--   }

-- @[simp]
-- theorem BigStepBuiltin.sub_field_iff : BigStepBuiltin P .sub [⟨.field, n1⟩, ⟨.field, n2⟩] v ↔ v = ⟨.field, n1 - n2⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply BigStepBuiltin.sub

-- @[simp]
-- theorem BigStepBuiltin.sub_u_iff : BigStepBuiltin P .sub [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.u s, n1 - n2⟩ ∧ n2.val ≤ n1.val := by
--   apply Iff.intro
--   · intro hp; cases hp; simpa
--   · intro_cases
--     simp_all [BigStepBuiltin.subU]

-- @[simp]
-- theorem BigStepBuiltin.add_field_iff : BigStepBuiltin P .add [⟨.field, n1⟩, ⟨.field, n2⟩] v ↔ v = ⟨.field, n1 + n2⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply addF

-- @[simp]
-- theorem BigStepBuiltin.add_u_iff : BigStepBuiltin P .add [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.u s, n1 + n2⟩ ∧ (n1.val + n2.val < 2^s) := by
--   apply Iff.intro
--   · intro hp; cases hp; simpa
--   · intro_cases
--     simp_all [BigStepBuiltin.addU]

-- @[simp]
-- theorem BigStepBuiltin.div_u_iff : BigStepBuiltin P .div [⟨.u s, n1⟩, ⟨.u s, n2⟩] v ↔ v = ⟨.u s, n1 / n2⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro_cases
--     simp_all [BigStepBuiltin.divU]

-- @[simp]
-- theorem BigStepBuiltin.eq_iff : BigStepBuiltin P .eq [v1, v2] v ↔ v = ⟨.bool, (v1 == v2)⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply BigStepBuiltin.eq

-- @[simp]
-- theorem BigStepBuiltin.assert_iff : BigStepBuiltin P .assert [v] r ↔ v = ⟨.bool, true⟩ ∧ r = .unit P := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply BigStepBuiltin.assert

-- @[simp]
-- theorem BigStepBuiltin.modulusNumBits_iff : BigStepBuiltin P .modulusNumBits [] v ↔ v = ⟨.u 64, Field.numBits P⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply BigStepBuiltin.modulusNumBits

-- @[simp]
-- theorem BigStepBuiltin.toLeBytes_iff : BigStepBuiltin P .toLeBytes [⟨.field, n⟩, ⟨.u 32, len⟩] result ↔  ∃r, result = ⟨.slice (.u 8), r⟩ ∧ (n = ∑i, ((r.get i) : ZMod P) * 256 ^ i.val) ∧ (r.length = len) := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     apply Exists.intro
--     apply And.intro <;> try rfl
--     apply And.intro <;> assumption
--   · intro_cases
--     simp_all [BigStepBuiltin.toLeBytes]

-- @[simp]
-- theorem BigStepBuiltin.castU_iff : BigStepBuiltin P (.cast (.u s)) [⟨.u s', i⟩] v ↔ v = ⟨.u s, i⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply BigStepBuiltin.castU

-- @[simp]
-- theorem BigStepBuiltin.not_iff : BigStepBuiltin P .not [⟨.bool, b⟩] v ↔ v = ⟨.bool, !b⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp
--   · intro hp
--     simp [hp]
--     apply BigStepBuiltin.not

-- @[simp]
-- theorem BigStepBuiltin.index_iff : BigStepBuiltin P .index [⟨.slice tp, s⟩, ⟨.u 32, i⟩] v ↔ ∃ (hp: i.val < s.length), v = ⟨tp, s[i]⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp_all
--   · intro hp
--     cases hp
--     simp_all
--     apply BigStepBuiltin.index

mutual

inductive BigStepArgs : {args : List Tp} → Env → State P → HList (Expr' (InstanceOf P)) args → State P → HList (InstanceOf P) args → Prop where
| nil : BigStepArgs Γ st HList.nil st HList.nil
| cons :
    BigStepAux Γ st e st' v →
    BigStepArgs Γ st' exprs st'' results →
    BigStepArgs Γ st (HList.cons e exprs) st'' (HList.cons v results)

inductive BigStepLoop : {s : Nat} → Env → State P → Nat → Nat → (U s → Expr' (InstanceOf P) r) → State P → Prop where
| cont :
    (lo < hi) →
    BigStepAux Γ st (body lo) st' v' →
    BigStepLoop Γ st' lo.succ hi body st'' →
    BigStepLoop Γ st lo hi body st''
| done :
    (lo ≥ hi) →
    BigStepLoop Γ st lo hi body st

inductive BigStepAux : {tp : Tp .type} → Env → State P → Expr' (InstanceOf P) tp → State P → InstanceOf P tp → Prop where
| skip : BigStepAux Γ st .skip st ()
| litField : BigStepAux Γ st (.lit .field n) st n
| litU : BigStepAux Γ st (.lit (.u s) n) st n
| litFalse : BigStepAux Γ st (.lit .bool 0) st false
| litTrue : BigStepAux Γ st (.lit .bool 1) st true
| var : BigStepAux Γ st (.var v) st v
| letIn :
    BigStepAux Γ st e st' v →
    BigStepAux Γ st' (b v) st'' v' →
    BigStepAux Γ st (.letIn e b) st'' v'
| callBuiltin :
    BigStepArgs Γ st eargs st' vargs →
    BigStepBuiltin P _ _ b vargs v →
    BigStepAux Γ st (.call _ _ (.builtin b) eargs) st' v
| callDecl:
    Γ fname = some fn →
    BigStepArgs Γ st eargs st' vargs →
    BigStepAux Γ st' (fn.2.2 vargs) st'' v →
    BigStepAux Γ st (.call fn.1 fn.2.1 (.decl fname) eargs) st'' v
| seq:
    BigStepAux Γ st e1 st' v' →
    BigStepAux Γ st' e2 st'' v →
    BigStepAux Γ st (.seq e1 e2) st'' v
| iteTrue:
    BigStepAux Γ st c st' true →
    BigStepAux Γ st' t st'' v →
    BigStepAux Γ st (.ite c t e) st'' v
| iteFalse:
    BigStepAux Γ st c st' false →
    BigStepAux Γ st' e st'' v →
    BigStepAux Γ st (.ite c t e) st'' v
| loop:
    BigStepAux Γ st lo st' vlo →
    BigStepAux Γ st' hi st'' vhi →
    BigStepLoop Γ st'' vlo vhi body st''' →
    BigStepAux Γ st (.loop lo hi body) st''' ()

end

-- @[simp]
-- theorem BigStepAux.skip_iff: BigStepAux P Γ st (.expr .skip) st' v ↔ st = st' ∧ v = ⟨.unit, ()⟩ := by
--   apply Iff.intro
--   · intro hp; cases hp; simp_all
--   · intro hp
--     simp_all [BigStepAux.skip]

-- @[simp]
-- theorem BigStepAux.litNone_iff: BigStepAux P Γ st (.expr (.lit n .field)) st' v ↔ st = st' ∧ v = ⟨.field, n⟩ := by
--   apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litNone])

-- @[simp]
-- theorem BigStepAux.litU_iff: BigStepAux P Γ st (.expr (.lit n (.u s))) st' v ↔ st = st' ∧ v = ⟨.u s, n⟩ := by
--   apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litU])

-- @[simp]
-- theorem BigStepAux.litFalse_iff: BigStepAux P Γ st (.expr (.lit 0 .bool)) st' v ↔ st = st' ∧ v = ⟨.bool, false⟩ := by
--   apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litFalse])

-- @[simp]
-- theorem BigStepAux.litTrue_iff: BigStepAux P Γ st (.expr (.lit 1 .bool)) st' v ↔ st = st' ∧ v = ⟨.bool, true⟩ := by
--   apply Iff.intro <;> (intro h; cases h; simp_all [BigStepAux.litTrue])

-- @[simp]
-- theorem BigStepAux.var_iff: BigStepAux P Γ st (.expr (.var x)) st' v ↔ (x = (.inr v) ∨ (∃ptr, x = (.inl ptr) ∧ st.memory ptr = some v)) ∧ st = st' := by
--   apply Iff.intro
--   · rintro ⟨_|_⟩ <;> simp_all
--   · rintro ⟨(_|⟨ptr, _, _⟩), _, _, _⟩
--     · simp_all [BigStepAux.varValue]
--     · subst_vars
--       apply BigStepAux.varDeref <;> assumption

-- @[simp]
-- theorem BigStepAux.call_iff:
--   BigStepAux P Γ st (.expr (.call f args)) st' v ↔
--   BigStepAux P Γ st (.callArgPrep f [] args) st' v := by
--   apply Iff.intro
--   · intro hp; cases hp
--     assumption
--   · intro_cases
--     apply BigStepAux.call; assumption

-- @[simp]
-- theorem BigStepAux.callArgPrepNext_iff:
--   BigStepAux P Γ st (.callArgPrep f args (e::es)) st' v ↔
--   ∃a st'', BigStepAux P Γ st (.expr e) st'' a ∧ BigStepAux P Γ st'' (.callArgPrep f (args++[a]) es) st' v := by
--   apply Iff.intro
--   · intro hp; cases hp
--     repeat apply Exists.intro
--     apply And.intro <;> assumption
--   · intro_cases
--     apply BigStepAux.callArgPrepNext <;> assumption

-- def BigStepCall (P : Nat) (Γ : Env) (state : State P) (f : Function) (args : List (Value P)) (state' : State P) (v : Value P) :=
--   BigStepAux P Γ state (.expr $ f (Value P) Nat args) state' v

-- theorem BigStepAux.callArgPrepDeclDone_iff {fname : String} (hp : Γ fname = some func) {v : Value P} {st st' : State P} {args : List (Value P)}:
--   BigStepAux P Γ st (.callArgPrep (.decl fname) args []) st' v ↔
--   BigStepCall P Γ st func args st' v := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     rename_i h_lookup h_exe
--     unfold BigStepCall
--     rw [hp] at h_lookup
--     injection h_lookup with h_lookup
--     cases h_lookup
--     assumption
--   · intros
--     apply BigStepAux.callArgPrepDeclDone <;> assumption

-- @[simp]
-- theorem BigStepAux.callArgPrepBultinDone_iff:
--   BigStepAux P Γ st (.callArgPrep (.builtin b) vs []) st' v ↔
--   BigStepBuiltin P b vs v ∧ st = st' := by
--   apply Iff.intro
--   · intro hp; cases hp; simp_all
--   · intro hp
--     simp_all [BigStepAux.callArgPrepBuiltinDone]

-- @[simp]
-- theorem BigStepAux.seq_iff:
--   BigStepAux P Γ st (.expr (.seq e₁ e₂)) st' v ↔
--   ∃a st'', BigStepAux P Γ st (.expr e₁) st'' a ∧ BigStepAux P Γ st'' (.expr e₂) st' v := by
--   apply Iff.intro
--   · intro hp; cases hp
--     repeat apply Exists.intro
--     apply And.intro <;> assumption
--   · intro_cases
--     apply BigStepAux.seq <;> assumption

-- @[simp]
-- theorem BigStepAux.declareVar_iff:
--   BigStepAux P Γ st sc (.expr (.declareVar x e)) st' sc' v ↔
--   ∃a, BigStepAux P Γ st sc (.expr e) st' sc a ∧ v = .unit P ∧ sc' = sc.update x (.value a) := by
--   apply Iff.intro
--   · intro hp; cases hp
--     repeat apply Exists.intro
--     apply And.intro <;> try assumption
--     apply And.intro <;> try rfl
--   · intro_cases
--     subst_vars
--     apply BigStepAux.declareVar
--     assumption

-- @[simp]
-- theorem BigStepAux.declareMutVar_iff:
--   BigStepAux P Γ st sc (.expr (.declareMutVar x e)) st' sc' v ↔
--   ∃a st'', BigStepAux P Γ st sc (.expr e) st'' sc a ∧ v = .unit P ∧ sc' = sc.update x (.autoDeref st''.nextPtr) ∧ st' = st''.alloc a := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     repeat apply Exists.intro
--     apply And.intro <;> try assumption
--     apply And.intro <;> try rfl
--     apply And.intro <;> rfl
--   · intro_cases
--     subst_vars
--     apply BigStepAux.declareMutVar
--     assumption

-- @[simp]
-- theorem BigStepAux.assignMut_iff:
--   BigStepAux P Γ st sc (.expr (.assignMut x e)) st' sc' v ↔
--   ∃ptr a st'', sc x = some (.autoDeref ptr) ∧ BigStepAux P Γ st sc (.expr e) st'' sc a ∧ v = .unit P ∧ st' = st''.set ptr a ∧ sc = sc' := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     repeat apply Exists.intro
--     apply And.intro; assumption
--     apply And.intro; assumption
--     apply And.intro; rfl
--     apply And.intro <;> rfl
--   · intro_cases
--     subst_vars
--     apply BigStepAux.assignMut <;> assumption

-- @[simp]
-- theorem BigStepAux.unconstrained_iff:
--   BigStepAux P Γ st sc (.expr .fresh) st' sc' v ↔ st = st' ∧ sc = sc' := by
--   apply Iff.intro
--   · intro hp; cases hp; simp_all
--   · rintro ⟨⟨_⟩, ⟨_⟩⟩
--     apply BigStepAux.fresh

-- @[simp]
-- theorem BigStepAux.ite_iff:
--   BigStepAux P Γ st sc (.expr (.ite c t e)) st' sc' v ↔
--   sc = sc' ∧ ∃v' st'', BigStepAux P Γ st sc (.expr c) st'' sc v' ∧
--     ((v' = ⟨.bool, true⟩ ∧ BigStepAux P Γ st'' sc (.expr t) st' sc v) ∨
--      (v' = ⟨.bool, false⟩ ∧ BigStepAux P Γ st'' sc (.expr e) st' sc v)) := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     · simp
--       repeat apply Exists.intro
--       apply And.intro
--       · assumption
--       apply Or.inl
--       tauto
--     · simp
--       repeat apply Exists.intro
--       apply And.intro
--       · assumption
--       apply Or.inr
--       tauto
--   · intro_cases
--     casesm* _ ∨ _
--     · simp_all
--       apply BigStepAux.iteTrue <;> tauto
--     · simp_all
--       apply BigStepAux.iteFalse <;> tauto

-- @[simp]
-- theorem BigStepAux.loop_iff:
--   BigStepAux P Γ st sc (.expr (.loop i lo hi body)) st''' sc' v ↔
--   ∃s st' st'' lov hiv, BigStepAux P Γ st sc (.expr lo) st' sc ⟨.u s, lov⟩ ∧ BigStepAux P Γ st' sc (.expr hi) st'' sc ⟨.u s, hiv⟩ ∧ BigStepAux P Γ st'' sc (.loopProgress s lov hiv i body) st''' sc v  ∧ sc = sc' := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     tauto
--   · intro_cases
--     subst_vars
--     apply BigStepAux.loop <;> assumption

-- theorem BigStepAux.loopCont_iff (hp : lo < hi):
--   BigStepAux P Γ st sc (.loopProgress s lo hi i body) st'' sc' v ↔
--   ∃a st',
--     BigStepAux P Γ st (sc.update i (.value ⟨.u s, lo⟩)) (.expr body) st' (sc.update i (.value ⟨.u s, lo⟩)) a ∧
--     BigStepAux P Γ st' sc (.loopProgress s lo.succ hi i body) st'' sc v ∧
--     sc = sc' := by
--   apply Iff.intro
--   · intro hp
--     cases hp
--     · repeat apply Exists.intro
--       apply And.intro <;> try assumption
--       apply And.intro <;> try assumption
--       rfl
--     · linarith
--   · intro_cases
--     subst_vars
--     apply BigStepAux.loopCont <;> try assumption

-- @[simp]
-- theorem BigStepAux.loopDone_iff (hp : lo ≥ hi):
--   BigStepAux P Γ st sc (.loopProgress s lo hi i body) st' sc' v ↔
--   v = ⟨.unit, ()⟩ ∧ st = st' ∧ sc = sc':= by
--   apply Iff.intro
--   · intro hp
--     cases hp <;> try linarith
--     tauto
--   · intro_cases; subst_vars
--     apply BigStepAux.loopDone
--     assumption

end Lampe



open Lampe

def modulusNumBitsFn : Function := ⟨[], ⟨.u 64, fun _ => .call [] (.u 64) (.builtin .modulusNumBits) h![]⟩⟩
def toLeBytesFn : Function := ⟨[.field, .u 32], ⟨.slice (.u 8), fun h![i, s] =>
  .call [.field, .u 32] (.slice (.u 8)) (.builtin .toLeBytes) h![.var i, .var s]
⟩⟩

#print toLeBytesFn


@[reducible]
def stdlib : Env := fun i => match i with
| "field::modulus_num_bits" => some modulusNumBitsFn
| "field::Field::to_le_bytes" => some toLeBytesFn
| _ => none

-- @[simp]
-- theorem modulusNumBits_sem : BigStepCall P Γ st modulusNumBitsFn [] st' v ↔ st = st' ∧ v = ⟨.u 64, Field.numBits P⟩ := by
--   simp [BigStepCall, modulusNumBitsFn]; tauto

-- @[simp]
-- theorem toLeBytes_sem :
--     BigStepCall P Γ st toLeBytesFn [⟨.field, n⟩, ⟨.u 32, len⟩] st' v ↔
--     st = st' ∧ ∃r, v = ⟨.slice (.u 8), r⟩ ∧ (n = ∑i, ((r.get i) : ZMod P) * 256 ^ i.val) ∧ (r.length = len) := by
--   simp [BigStepCall, toLeBytesFn]
--   apply Iff.intro
--   · intro_cases
--     rename BigStepBuiltin _ _ _ _ => hp
--     cases hp
--     simp_all
--   · intro_cases
--     subst_vars
--     repeat (any_goals first | apply Exists.intro | apply And.intro)
--     any_goals rfl
--     convert BigStepBuiltin.toLeBytes _ _
--     rfl
--     assumption
