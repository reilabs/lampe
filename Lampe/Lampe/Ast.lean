import Mathlib
import Lampe.Value

namespace Lampe

abbrev Ident := String

inductive Builtin where
| add
| sub
| mul
| div
| eq
| assert
| not
| lt
| index

inductive FunctionIdent where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent

inductive Expr : Type where
| lit : Nat → Expr
| var : Ident → Expr
| declareVar : Ident → Expr → Expr
| declareMutVar : Ident → Expr → Expr
| assignMut : Ident → Expr → Expr
| assert : Expr → Expr
| fresh : Expr
| block : List Expr → Expr → Expr
| call : FunctionIdent → List Expr → Expr
-- | callArgPrep : FunctionIdent → List Value → List Expr → Expr
| ite : Expr → Expr → Expr → Expr
| skip : Expr
| loop : Ident → Expr → Expr → Expr → Expr
-- | iteCondEval : Value → Expr → Expr → Expr

def Expr.inductionOn
  {motive : Expr → Prop}
  (lit : ∀a, motive (.lit a))
  (var : ∀x, motive (.var x))
  (declareVar : ∀x e, motive e → motive (.declareVar x e))
  (declareMutVar : ∀x e, motive e → motive (.declareMutVar x e))
  (assignMut : ∀x e, motive e → motive (.assignMut x e))
  (require : ∀e, motive e → motive (.assert e))
  (unconstrained : motive .fresh)
  (block_nil : ∀e, motive e → motive (.block []  e))
  (block_cons : ∀hd e es, motive hd → motive (.block es e) → motive (.block (hd :: es) e))
  (call_nil : ∀f, motive (.call f []))
  (call_cons : ∀f a as, motive a → motive (.call f as) → motive (.call f (a::as)))
  (ite : ∀c t e, motive c → motive t → motive e → motive (.ite c t e))
  (skip : motive .skip)
  (loop : ∀i c b e, motive c → motive b → motive e → motive (.loop i c b e)):
  ∀e, motive e := by
  intros
  let motive_list : List Expr → Prop := fun es => (∀e, motive e → motive (block es e)) ∧ (∀ f, motive (call f es))
  apply Expr.rec
  case motive_2 => exact motive_list
  any_goals tauto

structure Function where
params : List Ident
body : Expr

structure FunctionDecl where
name : Ident
fn : Function

structure Module where
decls : List FunctionDecl

end Lampe
