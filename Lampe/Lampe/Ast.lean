import Mathlib
import Lampe.Value

namespace Lampe

abbrev Ident := String

inductive Builtin : Type where
| add
| sub
| mul
| div
| eq
| assert
| not
| lt
| index
| cast : Nat → Builtin
| modulusNumBits
| toLeBytes
| fresh

inductive FunctionIdent : Type where
| builtin : Builtin → FunctionIdent
| decl : Ident → FunctionIdent

-- inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v) where
-- | nil : HList β []
-- | cons : ∀ {a : α} {as : List α}, β a → HList β as → HList β (a :: as)

-- syntax "h![" term,* "]" : term
-- macro_rules
-- | `(h![]) => `(HList.nil)
-- | `(h![$x]) => `(HList.cons $x HList.nil)
-- | `(h![$x, $xs,*]) => `(HList.cons $x h![$xs,*])

set_option pp.universes true
#check Tp'.denote
#check Kind.denote .type
#check (Tp.bool Kind.denote)
#check Tp' Kind.denote .type

inductive Expr' (rep : Tp .type → Type u): Tp .type → Type (u + 2) where
| lit : (tp : Tp.{1} .type) → Nat → Expr' rep tp
| var : rep tp → Expr' rep tp
| letIn : Expr' rep t₁ → (rep t₁ → Expr' rep t₂) → Expr' rep t₂
| seq : Expr' rep _ → Expr' rep t → Expr' rep t
| call : (args : Tp (.tyList .type)) → (res : Tp .type) → FunctionIdent → Tp.denoteArgs P args → Expr' rep res
| ite : Expr' rep (fun _ => .bool) → Expr' rep a → Expr' rep a → Expr' rep a
| skip : Expr' rep (fun _ => .unit)
| loop : Expr' rep (Tp.u s) → Expr' rep (Tp.u s) → (rep (Tp.u s) → Expr' rep r) → Expr' rep Tp.unit

def Expr (tp : Tp .type) := ∀ {rep}, Expr' rep tp

structure Function : Type 10 where
generics : List Kind
inTp : HList (generics.map Kind.denote) → Tp .type

-- def Expr (tp : Tp) := ∀ {rep}, Expr' rep tp

-- def Function := (inpTp : List Tp) × (out : Tp) × ({rep : Tp → Type} → HList rep inpTp → Expr' rep out)

-- def Expr.inductionOn
--   {motive : Expr → Prop}
--   (lit : ∀t a, motive (.lit a t))
--   (var : ∀x, motive (.var x))
--   (declareVar : ∀x e, motive e → motive (.declareVar x e))
--   (declareMutVar : ∀x e, motive e → motive (.declareMutVar x e))
--   (assignMut : ∀x e, motive e → motive (.assignMut x e))
--   (require : ∀e, motive e → motive (.assert e))
--   (unconstrained : motive .fresh)
--   (block_nil : ∀e, motive e → motive (.block []  e))
--   (block_cons : ∀hd e es, motive hd → motive (.block es e) → motive (.block (hd :: es) e))
--   (call_nil : ∀f, motive (.call f []))
--   (call_cons : ∀f a as, motive a → motive (.call f as) → motive (.call f (a::as)))
--   (ite : ∀c t e, motive c → motive t → motive e → motive (.ite c t e))
--   (skip : motive .skip)
--   (loop : ∀i c b e, motive c → motive b → motive e → motive (.loop i c b e)):
--   ∀e, motive e := by
--   intros
--   let motive_list : List Expr → Prop := fun es => (∀e, motive e → motive (block es e)) ∧ (∀ f, motive (call f es))
--   apply Expr.rec
--   case motive_2 => exact motive_list
--   any_goals tauto



-- structure Function where
-- params : List Ident
-- body : Expr

structure FunctionDecl where
name : Ident
fn : @Function

structure Module where
decls : List FunctionDecl

end Lampe
