import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Mathlib

namespace Lampe

variable (P : Nat)

def Env := Ident → Option Function

structure State where
memory : Nat → Option ((tp : Tp) × tp.denote P)
nextFreeMemory : Nat

def Env.ofModule (m : Module): Env := fun i => (m.decls.find? fun d => d.name == i).map (·.fn)

@[reducible]
def Env.extend (Γ₁ : Env) (Γ₂ : Env) : Env := fun i => Γ₁ i <|> Γ₂ i

inductive BigStepBuiltin : (inp: List Tp) → (out : Tp) → Builtin → HList (Tp.denote P) inp → out.denote P → Prop where
| eqU : BigStepBuiltin [.u s, .u s] .bool .eq h![v1, v2] (v1 == v2)
| eqF : BigStepBuiltin [.field, .field] .bool .eq h![v1, v2] (v1 == v2)
| ltU : BigStepBuiltin [.u s, .u s] .bool .lt h![n1, n2] (n1 < n2)
| assert : BigStepBuiltin [.bool] .unit .assert h![true] .unit
| addU : (n1.val + n2.val < 2 ^ s) → BigStepBuiltin [.u s, .u s] (.u s) .add h![n1, n2] (n1 + n2) -- oflow error in circuit as well?
| subU : (n2.val ≤ n1.val) → BigStepBuiltin [.u s, .u s] (.u s) .sub h![n1, n2] (n1 - n2) -- oflow error in circuit as well?
| fresh : BigStepBuiltin [] tp .fresh h![] v

mutual

inductive BigStepArgs : {args : List Tp} → Env → State P → HList (Expr rep) args → State P → HList (Tp.denote P) args → Prop where
| nil : BigStepArgs Γ st .nil st .nil
| cons :
    BigStepAux Γ st e st' v →
    BigStepArgs Γ st' exprs st'' results →
    BigStepArgs Γ st (.cons e exprs) st'' (.cons v results)

inductive BigStepLoop : {s : Nat} → Env → State P → Nat → Nat → (U s → Expr (Tp.denote P) tp) → State P → Prop where
| cont {body : U s → Expr (Tp.denote P) tp}:
    (lo < hi) →
    BigStepAux Γ st (body (lo : U s)) st' v' →
    BigStepLoop Γ st' lo.succ hi body st'' →
    BigStepLoop Γ st lo hi body st''
| done :
    (lo ≥ hi) →
    BigStepLoop Γ st lo hi body st

inductive BigStepAux : {tp : Tp} → Env → State P → Expr (Tp.denote P) tp → State P → tp.denote P → Prop where
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
    BigStepAux Γ st (.call h![] _ _ (.builtin b) eargs) st' v
| callDecl:
    Γ fname = some fn →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    BigStepArgs Γ st args st' vargs →
    BigStepAux Γ st' (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ vargs)) st'' v →
    BigStepAux Γ st (@Expr.call _ tyKinds generics argTypes res (.decl fname) args) st'' v
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

end Lampe

open Lampe
