import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Mathlib

namespace Lampe

variable (P : Prime)

def Ref.forward : Ref → Nat → Ref
| ⟨i⟩, n => ⟨ i + n ⟩

namespace Ref

@[simp]
lemma forward_zero {r:Ref} : r.forward 0 = r := by
  rfl

@[simp]
lemma forward_forward {r:Ref} {n m : Nat} : (r.forward n).forward m = r.forward (n + m) := by
  simp_arith [forward]

end Ref

def Env := Ident → Option Function

def AnyValue := (tp : Tp) × tp.denote P

structure State where
size : Nat
memory : Fin size → AnyValue P

namespace State

instance : Inhabited (State P) := ⟨{size := 0, memory := Fin.elim0}⟩

def nextRef {P} (st : State P): Ref := Ref.mk st.size

def alloc (st : State P) (tp : Tp) (v : tp.denote P) : State P := {
    size := st.size + 1
    memory := fun i => if h : i = Fin.last _ then ⟨tp, v⟩ else st.memory (i.castPred h)
}

def allocs (st : State P): List (AnyValue P) → State P
| [] => st
| ⟨tp, v⟩ :: allocs => State.allocs (st.alloc P tp v) allocs

def get (st : State P) (r : Ref) (hr : r.val < st.size): (tp : Tp) × tp.denote P := st.memory ⟨r.val, hr⟩

def get? (st : State P) (r : Ref): Option (AnyValue P) := if h : r.val < st.size then some (st.get P r h) else none

def set (st : State P) (r : Ref) (tp : Tp) (v : Tp.denote P tp): State P :=
  {st with memory := fun i => if i.val = r.val then ⟨tp, v⟩ else st.memory i}

@[simp]
theorem nextRef_val {state : State P} : state.nextRef.val = state.size := by
  simp [nextRef]

@[simp]
theorem allocs_size {state : State P} : (state.allocs P as).size = state.size + as.length := by
  induction as generalizing state with
  | nil => rfl
  | cons a as ih =>
    simp [allocs, ih, alloc]
    simp_arith

@[simp]
theorem alloc_get_size {state : State P} : (state.alloc P tp v).nextRef = state.nextRef.forward 1 := by
  simp [alloc, nextRef, Ref.forward]

theorem alloc_allocs_singleton {state : State P} : state.alloc P tp v = state.allocs P [⟨tp, v⟩] := by
  rfl

theorem allocs_allocs_singleton { state : State P } : (state.allocs P [s]).allocs P ss = state.allocs P (s :: ss) := by
  rfl

lemma allocs_cons_cons {state : State P} : (state.allocs P (a::b::as)) = (state.alloc P a.1 a.2).allocs P (b::as) := by
  rfl

lemma allocs_snoc {state : State P} : (state.allocs P (as ++ [a])) = alloc P (state.allocs P as) a.1 a.2 := by
  induction as generalizing state with
  | nil => rfl
  | cons a as ih =>
    simp [allocs, ih]

lemma alloc_get_lt {state : State P} {h'} (h : r.val < state.size) :
    (state.alloc P tp v).get P r h' = state.get P r h := by
  have : r.val ≠ state.size := Nat.ne_of_lt h
  simp [get, alloc, Fin.last, this]
  rfl

lemma allocs_get_nextRef {state : State P} {h} :
    (state.allocs P (a :: as)).get P state.nextRef h = a := by
  induction as using List.list_reverse_induction with
  | base => simp [allocs, alloc, nextRef, get, Fin.last]
  | ind a as ih =>
    simp only [←List.cons_append, allocs_snoc]
    rw [alloc_get_lt]
    · simp [ih]
    · simp

lemma allocs_get?_nextRef {state : State P}:
    (state.allocs P (a :: as)).get? P state.nextRef = some a := by
  simp [get?, allocs_get_nextRef]

lemma alloc_nextRef {state : State P} {tp : Tp} {v : tp.denote P} :
    (state.alloc P tp v).nextRef = state.nextRef.forward 1 := by
  simp [alloc, nextRef, Ref.forward]

@[simp]
theorem allocs_get_forward {state : State P} {h : (state.nextRef.forward (k + 1)).val < (state.allocs P (a::as)).size}:
    (state.allocs P (a::as)).get P (state.nextRef.forward (k + 1)) h =
    (state.allocs P as).get P (state.nextRef.forward k) (by simp [Ref.forward, allocs_size] at *; linarith) := by
  induction as generalizing a state k with
  | nil => simp [Ref.forward] at h
  | cons hh tt ih =>
    simp [Ref.forward] at h
    simp [allocs_cons_cons]
    apply Eq.trans (b := (get P (allocs P (alloc P state a.fst a.snd) (hh :: tt)) ((state.alloc P a.1 a.2).nextRef.forward k)) ?_)
    · simp_arith [Ref.forward]
      congr 2
      simp_arith
    · cases k with
      | zero => simp only [Ref.forward_zero, allocs_get_nextRef]
      | succ k =>
        simp only [ih]
        conv_lhs =>
          simp only [alloc_nextRef, Ref.forward_forward, add_comm]
          simp only [alloc_allocs_singleton, allocs_allocs_singleton, ih]
    · simp [alloc, nextRef, Ref.forward, h]

theorem allocs_get?_forward {state : State P}:
    (state.allocs P (a::as)).get? P (state.nextRef.forward (k + 1)) = (state.allocs P as).get? P (state.nextRef.forward k) := by
  simp [get?]
  split <;> {
    split <;> {
      simp [Ref.forward] at *
      try simp [Ref.forward] at *
      try linarith
    }
  }

end State

def Env.ofModule (m : Module): Env := fun i => (m.decls.find? fun d => d.name == i).map (·.fn)

@[reducible]
def Env.extend (Γ₁ : Env) (Γ₂ : Env) : Env := fun i => Γ₁ i <|> Γ₂ i

@[reducible]
def getProj {fields : List Tp} (mem : Member tp fields) (v : Tp.denote P (.struct fields)): Tp.denote P tp := match mem with
| .head => v.1
| .tail mem => getProj mem v.2

def fpToU : Fp P → U s := fun x => ⟨x.val % 2 ^ s, by apply Nat.mod_lt; apply Nat.zero_lt_of_ne_zero; apply pow_ne_zero; decide⟩
def uToU : U s → U t := fun x => ⟨x.val % 2 ^ t, by apply Nat.mod_lt; apply Nat.zero_lt_of_ne_zero; apply pow_ne_zero; decide⟩
def uToFp : U s → Fp P := fun x => ⟨x.val % P.natVal, by apply Nat.mod_lt; apply Nat.zero_lt_of_ne_zero; apply Nat.Prime.ne_zero; apply P.prop⟩

inductive BigStepBuiltin : (inp: List Tp) → (out : Tp) → Builtin → HList (Tp.denote P) inp → out.denote P → Prop where
| eqU : BigStepBuiltin [.u s, .u s] .bool .eq h![v1, v2] (v1 == v2)
| eqF : BigStepBuiltin [.field, .field] .bool .eq h![v1, v2] (v1 == v2)
| ltU : BigStepBuiltin [.u s, .u s] .bool .lt h![n1, n2] (n1 < n2)
| assert : BigStepBuiltin [.bool] .unit .assert h![true] .unit
| addF : BigStepBuiltin [.field, .field] .field .add h![n1, n2] (n1 + n2)
| addU : (n1.val + n2.val < 2 ^ s) → BigStepBuiltin [.u s, .u s] (.u s) .add h![n1, n2] (n1 + n2) -- oflow error in circuit as well?
| divF {n2 : Fp P}: (n2 ≠ 0) → BigStepBuiltin [.field, .field] .field .div h![n1, n2] (n1 / n2)
| divU {n1 n2 : U s} : (n2 ≠ 0) → BigStepBuiltin [.u s, .u s] (.u s) .div h![n1, n2] (n1 / n2) -- div by zero error in circuit?
| subF : BigStepBuiltin [.field, .field] .field .sub h![n1, n2] (n1 - n2)
| subU : (n2.val ≤ n1.val) → BigStepBuiltin [.u s, .u s] (.u s) .sub h![n1, n2] (n1 - n2) -- oflow error in circuit as well?
| castUU : BigStepBuiltin [.u s] (.u t) .cast h![n] n
| castUF : BigStepBuiltin [.u s] .field .cast h![n] (uToFp P n)
| castFU : BigStepBuiltin [.field] (.u s) .cast h![n] (fpToU P n)
| not : BigStepBuiltin [.bool] .bool .not h![b] (!b)
| fresh : BigStepBuiltin [] tp .fresh h![] v
| modulusNumBits : BigStepBuiltin [] (.u 64) .modulusNumBits h![] (numBits P.natVal)
| toLeBytes {result : List (U 8)} {s : U 32} {n : Fp P} :
    result.length = s.val →
    ∑i, (result.get i).val * 2^i.val = n →
    BigStepBuiltin [.field, .u 32] (.slice (.u 8)) .toLeBytes h![n, s] result
| index {slice : List (t.denote P)} : (h : List.length slice > i.val) →
    BigStepBuiltin [.slice t, .u s] t .index h![slice, i] (slice.get ⟨i, h⟩)


mutual

inductive BigStepArgs : {args : List Tp} → Env → State P → HList (Expr rep) args → State P → HList (Tp.denote P) args → Prop where
| nil : BigStepArgs Γ st .nil st .nil
| cons :
    BigStep Γ st e st' v →
    BigStepArgs Γ st' exprs st'' results →
    BigStepArgs Γ st (.cons e exprs) st'' (.cons v results)

inductive BigStepFields : {fields : List Tp} → Env → State P → HList (Expr rep) fields → State P → Tp.denoteArgs P fields → Prop where
| nil : BigStepFields Γ st .nil st ()
| cons :
    BigStep Γ st e st' v →
    BigStepFields Γ st' exprs st'' results →
    BigStepFields Γ st (.cons e exprs) st'' (v, results)

inductive BigStepLoop : {s : Nat} → Env → State P → Nat → Nat → (U s → Expr (Tp.denote P) tp) → State P → Prop where
| cont {lo hi : ℕ} {body : U s → Expr (Tp.denote P) tp}:
    (lo < hi) →
    BigStep Γ st (body (lo : U s)) st' v' →
    BigStepLoop Γ st' lo.succ hi body st'' →
    BigStepLoop Γ st lo hi body st''
| done :
    (lo ≥ hi) →
    BigStepLoop Γ st lo hi body st

inductive BigStep : {tp : Tp} → Env → State P → Expr (Tp.denote P) tp → State P → tp.denote P → Prop where
| skip : BigStep Γ st .skip st ()
| litField : BigStep Γ st (.lit .field n) st n
| litU : BigStep Γ st (.lit (.u s) n) st n
| litFalse : BigStep Γ st (.lit .bool 0) st false
| litTrue : BigStep Γ st (.lit .bool 1) st true
| var : BigStep Γ st (.var v) st v
| letIn :
    BigStep Γ st e st' v →
    BigStep Γ st' (b v) st'' v' →
    BigStep Γ st (.letIn e b) st'' v'
| letMutIn {e : Expr _ tp}:
    BigStep Γ st e st' v →
    BigStep Γ (st'.alloc P tp v) (b st'.nextRef) st'' v' →
    BigStep Γ st (.letMutIn e b) st'' v'
| callBuiltin :
    BigStepArgs Γ st eargs st' vargs →
    BigStepBuiltin P _ _ b vargs v →
    BigStep Γ st (.call h![] _ (.builtin b) eargs) st' v
| callDecl:
    Γ fname = some fn →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    BigStepArgs Γ st args st' vargs →
    BigStep Γ st' (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ vargs)) st'' v →
    BigStep Γ st (@Expr.call _ tyKinds argTypes generics res (.decl fname) args) st'' v
| seq:
    BigStep Γ st e1 st' v' →
    BigStep Γ st' e2 st'' v →
    BigStep Γ st (.seq e1 e2) st'' v
| iteTrue:
    BigStep Γ st c st' true →
    BigStep Γ st' t st'' v →
    BigStep Γ st (.ite c t e) st'' v
| iteFalse:
    BigStep Γ st c st' false →
    BigStep Γ st' e st'' v →
    BigStep Γ st (.ite c t e) st'' v
| loop:
    BigStep Γ st lo st' vlo →
    BigStep Γ st' hi st'' vhi →
    BigStepLoop Γ st'' vlo vhi body st''' →
    BigStep Γ st (.loop lo hi body) st''' ()
| struct:
    BigStepFields Γ st fields st' values →
    BigStep Γ st (.struct fields) st' values
| proj:
    BigStep Γ st struct st' v →
    BigStep Γ st (.proj mem struct) st' (getProj P mem v)
| readRef {refE : Expr (Tp.denote P) (.ref tp)}:
    st.get? P ref = some ⟨tp, v⟩ →
    BigStep Γ st (.readRef (.var ref)) st v
| writeRef {e : Expr (Tp.denote P) tp}:
    BigStep Γ st e st' v →
    BigStep Γ st (.writeRef (.var ref) e) (st'.set P ref tp v) ()

end

end Lampe

open Lampe
