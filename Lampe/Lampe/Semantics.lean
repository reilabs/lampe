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

inductive Omni : Env → State P → Expr (Tp.denote P) tp → (Option (State P × tp.denote P) → Prop) → Prop where
| litField : Q (some (st, n)) → Omni Γ st (.lit .field n) Q
| litFalse : Q (some (st, false)) → Omni Γ st (.lit .bool 0) Q
| litTrue : Q (some (st, true)) → Omni Γ st (.lit .bool 1) Q
| litU {Q} : Q (some (st, ↑n)) → Omni Γ st (.lit (.u s) n) Q
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
| loopDone :
    lo ≥ hi →
    Omni Γ st (.loop lo hi body) Q
| loopNext {s} {lo hi : U s} {body} :
    lo < hi →
    Omni Γ st (.letIn (body lo) (fun _ => .loop (lo + 1) hi body)) Q →
    Omni Γ st (.loop lo hi body) Q

theorem Omni.conseq:
    Omni p Γ st e Q →
    (∀ v, Q v → Q' v) →
    Omni p Γ st e Q' := by
  intro h
  induction h <;> try (
    intro
    constructor
    all_goals tauto
  )
  case callBuiltin =>
    cases_type Builtin
    tauto
  case loopNext =>
    intro
    apply loopNext (by assumption)
    tauto

end Lampe
