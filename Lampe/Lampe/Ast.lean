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

inductive FunctionIdent where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent

inductive Expr : Type where
| lit : Nat → Expr
| var : Ident → Expr
| assign : Ident → Expr → Expr
| assert : Expr → Expr
| fresh : Expr
| block : List Expr → Expr → Expr
| call : FunctionIdent → List Expr → Expr
-- | callArgPrep : FunctionIdent → List Value → List Expr → Expr
| ite : Expr → Expr → Expr → Expr
-- | iteCondEval : Value → Expr → Expr → Expr

structure Function where
params : List Ident
body : Expr

structure FunctionDecl where
name : Ident
fn : Function

structure Module where
decls : List FunctionDecl

end Lampe
