import Lampe.Ast
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Mathlib
import Lampe.State


namespace Lampe

variable (P : Prime)

def Env := Ident → Option Function

def Env.ofModule (m : Module): Env := fun i => (m.decls.find? fun d => d.name == i).map (·.fn)

@[reducible]
def Env.extend (Γ₁ : Env) (Γ₂ : Env) : Env := fun i => Γ₁ i <|> Γ₂ i

@[reducible]
def getProj {fields : List Tp} (mem : Member tp fields) (v : Tp.denote P (.struct fields)): Tp.denote P tp := match mem with
| .head => v.1
| .tail mem => getProj mem v.2

-- def fpToU : Fp P → U s := fun x => ⟨x.val % 2 ^ s, by apply Nat.mod_lt; apply Nat.zero_lt_of_ne_zero; apply pow_ne_zero; decide⟩
-- def uToU : U s → U t := fun x => ⟨x.val % 2 ^ t, by apply Nat.mod_lt; apply Nat.zero_lt_of_ne_zero; apply pow_ne_zero; decide⟩
-- def uToFp : U s → Fp P := fun x => ⟨x.val % P.natVal, by apply Nat.mod_lt; apply Nat.zero_lt_of_ne_zero; apply Nat.Prime.ne_zero; apply P.prop⟩

-- inductive BigStepBuiltin : (inp: List Tp) → (out : Tp) → Builtin → HList (Tp.denote P) inp → out.denote P → Prop where
-- | eqU : BigStepBuiltin [.u s, .u s] .bool .eq h![v1, v2] (v1 == v2)
-- | eqF : BigStepBuiltin [.field, .field] .bool .eq h![v1, v2] (v1 == v2)
-- | ltU : BigStepBuiltin [.u s, .u s] .bool .lt h![n1, n2] (n1 < n2)
-- | assert : BigStepBuiltin [.bool] .unit .assert h![true] .unit
-- | addF : BigStepBuiltin [.field, .field] .field .add h![n1, n2] (n1 + n2)
-- | addU : (n1.val + n2.val < 2 ^ s) → BigStepBuiltin [.u s, .u s] (.u s) .add h![n1, n2] (n1 + n2) -- oflow error in circuit as well?
-- | divF {n2 : Fp P}: (n2 ≠ 0) → BigStepBuiltin [.field, .field] .field .div h![n1, n2] (n1 / n2)
-- | divU {n1 n2 : U s} : (n2 ≠ 0) → BigStepBuiltin [.u s, .u s] (.u s) .div h![n1, n2] (n1 / n2) -- div by zero error in circuit?
-- | subF : BigStepBuiltin [.field, .field] .field .sub h![n1, n2] (n1 - n2)
-- | subU : (n2.val ≤ n1.val) → BigStepBuiltin [.u s, .u s] (.u s) .sub h![n1, n2] (n1 - n2) -- oflow error in circuit as well?
-- | castUU : BigStepBuiltin [.u s] (.u t) .cast h![n] n
-- | castUF : BigStepBuiltin [.u s] .field .cast h![n] (uToFp P n)
-- | castFU : BigStepBuiltin [.field] (.u s) .cast h![n] (fpToU P n)
-- | not : BigStepBuiltin [.bool] .bool .not h![b] (!b)
-- | fresh : BigStepBuiltin [] tp .fresh h![] v
-- | modulusNumBits : BigStepBuiltin [] (.u 64) .modulusNumBits h![] (numBits P.natVal)
-- | toLeBytes {result : List (U 8)} {s : U 32} {n : Fp P} :
--     result.length = s.val →
--     ∑i, (result.get i).val * 2^i.val = n →
--     BigStepBuiltin [.field, .u 32] (.slice (.u 8)) .toLeBytes h![n, s] result
-- | index {slice : List (t.denote P)} : (h : List.length slice > i.val) →
--     BigStepBuiltin [.slice t, .u s] t .index h![slice, i] (slice.get ⟨i, h⟩)
-- | sliceLen {slice : List (t.denote P)} : BigStepBuiltin [.slice t] (.u 32) .sliceLen h![slice] slice.length


-- mutual

-- inductive BigStepLoop : {s : Nat} → Env → State P → Nat → Nat → (U s → Expr (Tp.denote P) tp) → State P → Prop where
-- | cont {lo hi : ℕ} {body : U s → Expr (Tp.denote P) tp}:
--     (lo < hi) →
--     BigStep Γ st (body (lo : U s)) st' v' →
--     BigStepLoop Γ st' lo.succ hi body st'' →
--     BigStepLoop Γ st lo hi body st''
-- | done :
--     (lo ≥ hi) →
--     BigStepLoop Γ st lo hi body st

inductive BigStep : {tp : Tp} → Env → State P → Expr (Tp.denote P) tp → Option (State P × tp.denote P) → Prop where
| skip : BigStep Γ st .skip (some (st, ()))
| litField : BigStep Γ st (.lit .field n) (some (st, n))
| litU : BigStep Γ st (.lit (.u s) n) (some (st, n))
| litFalse : BigStep Γ st (.lit .bool 0) (some (st, false))
| litTrue : BigStep Γ st (.lit .bool 1) (some (st, true))
| var : BigStep Γ st (.var v) (some (st, v))
| letIn_success :
    BigStep Γ st e (some (st', v)) →
    BigStep Γ st' (b v) r →
    BigStep Γ st (.letIn e b) r
| letIn_fail :
    BigStep Γ st e none →
    BigStep Γ st (.letIn e b) none
| callBuiltin :
    b.bigStep P st argTypes resType args r  →
    BigStep Γ st (Expr.call h![] argTypes resType (.builtin b) args) r
| callDecl:
    Γ fname = some fn →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    BigStep Γ st (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ args)) r →
    BigStep Γ st (@Expr.call _ tyKinds generics argTypes res (.decl fname) args) r
| seq_success:
    BigStep Γ st e1 (some (st', v')) →
    BigStep Γ st' e2 r →
    BigStep Γ st (.seq e1 e2) r
| seq_fail:
    BigStep Γ st e1 none →
    BigStep Γ st (.seq e1 e2) none
| iteTrue:
    BigStep Γ st c (some (st', true)) →
    BigStep Γ st' t r →
    BigStep Γ st (.ite c t e) r
| iteFalse:
    BigStep Γ st c (some (st', false)) →
    BigStep Γ st' e r →
    BigStep Γ st (.ite c t e) r
| iteFail:
    BigStep Γ st c none →
    BigStep Γ st (.ite c t e) none

inductive Omni : Env → State P → Expr (Tp.denote P) tp → (Option (State P × tp.denote P) → Prop) → Prop where
| litField : Q (some (st, n)) → Omni Γ st (.lit .field n) Q
| litFalse : Q (some (st, false)) → Omni Γ st (.lit .bool 0) Q
| litTrue : Q (some (st, true)) → Omni Γ st (.lit .bool 1) Q
| var : Q (some (st, v)) → Omni Γ st (.var v) Q
| letIn :
    Omni Γ st e Q₁ →
    (∀v s, Q₁ (some (s, v)) → Omni Γ s (b v) Q) →
    (Q₁ none → Q none) →
    Omni Γ st (.letIn e b) Q
| callBuiltin {Q} :
    (b.omni P st argTypes resType args Q) →
    Omni Γ st (Expr.call h![] argTypes resType (.builtin b) args) Q
| callDecl:
    Γ fname = some fn →
    (hkc : fn.generics = tyKinds) →
    (htci : fn.inTps (hkc ▸ generics) = argTypes) →
    (htco : fn.outTp (hkc ▸ generics) = res) →
    Omni Γ st (htco ▸ fn.body _ (hkc ▸ generics) (htci ▸ args)) Q →
    Omni Γ st (@Expr.call _ tyKinds generics argTypes res (.decl fname) args) Q

end Lampe

open Lampe
