import Mathlib
import Lean
import Lampe.Ast
import Qq

namespace Lampe

open Lean Elab Meta Qq

declare_syntax_cat nr_ident
declare_syntax_cat nr_type
declare_syntax_cat nr_expr
declare_syntax_cat nr_block_contents

syntax ident:nr_ident
syntax ident"::"nr_ident : nr_ident



partial def elabNrIdent : Syntax → MetaM String
| `(nr_ident|$x:ident) => pure $ x.getId.toString
| `(nr_ident|$x:ident::$y:nr_ident) => do
  let tl ← elabNrIdent y
  pure $ s!"{x.getId.toString}::{tl}"
| _ => throwUnsupportedSyntax


syntax ident:nr_type
syntax ident "<" nr_type,* ">" : nr_type

partial def elabNrType (vmap : String → Option Q(Tp)): Syntax → MetaM Q(Tp)
| `(nr_type| u1) => pure q(Tp.u 1)
| `(nr_type| u8) => pure q(Tp.u 8)
| `(nr_type| u16) => pure q(Tp.u 16)
| `(nr_type| u32) => pure q(Tp.u 32)
| `(nr_type| u64) => pure q(Tp.u 64)
| `(nr_type| bool) => pure q(Tp.bool)
| `(nr_type| Field) => pure q(Tp.field)
| `(nr_type| $i:ident) => match vmap i.getId.toString with
  | some tp => pure tp
  | none => throwError "Unknown type {i.getId.toString}"
| _ => throwUnsupportedSyntax


syntax:100 "(" num ":" nr_type ")" : nr_expr
syntax:100 ident : nr_expr
syntax:100 nr_ident "<" nr_type,* ">" "(" (nr_expr ":" nr_type),* ")" : nr_expr
syntax:100 "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}" : nr_expr
syntax:100 "let" ident "=" nr_expr : nr_expr

def lit (rep : Q(Tp → Type)) (tp : Q(Tp)) (n : Nat) : Q(Lampe.Expr $rep $tp) := q(Lampe.Expr.lit $tp $n)
def letIn (rep : Q(Tp → Type)) (etp : Q(Tp)) (rtp : Q(Tp)) (ebody : Q(Lampe.Expr $rep $etp)) (rbody : Q($rep $etp → Lampe.Expr $rep $rtp)) : Q(Lampe.Expr $rep $rtp) := q(Lampe.Expr.letIn $ebody $rbody)

mutual

partial def elabBlock (rep : Q(Tp → Type)) (varMap : String → Option ((tp : Q(Tp)) × Q($rep $tp))) : List Syntax → MetaM ((tp : Q(Tp)) × Q(Lampe.Expr $rep $tp))
| h :: n :: rest => match h with
  | `(nr_expr | let $v = $e ) => do
    let ⟨etp, expr⟩ ← elabExpr rep varMap e
    let ⟨btp, bExpr⟩ ← withLocalDeclDQ (Name.mkSimple v.getId.toString) q($rep $etp) fun v' => do
      let ⟨resttp, rest⟩ ← elabBlock rep (fun s => if s = v.getId.toString then some ⟨etp, v'⟩ else varMap s) (n::rest)
      pure (resttp, ←mkLambdaFVars #[v'] rest)
    pure ⟨btp, letIn rep etp btp expr bExpr⟩
  | e => do
    let ⟨_, expr⟩ ← elabExpr rep varMap e
    let ⟨resttp, rest⟩ ← elabBlock rep varMap (n::rest)
    pure ⟨resttp, q(Lampe.Expr.seq $expr $rest)⟩
| [e] => match e with
  | `(nr_expr | let $_ = $e)
  | `(nr_expr | $e) => elabExpr rep varMap e
| _ => pure ⟨q(Tp.unit), q(Lampe.Expr.skip)⟩

partial def elabExpr (rep : Q(Tp → Type)) (varMap : String → Option ((tp : Q(Tp)) × Q($rep $tp))) : Syntax → MetaM ((tp : Q(Tp)) × Q(Lampe.Expr $rep $tp))
| `(nr_expr|($n:num : $tp)) => do
  let tp ← elabNrType default tp
  let num ← pure n.getNat
  pure ⟨tp, lit rep tp num⟩
| `(nr_expr| { $exprs;* }) => elabBlock rep varMap exprs.getElems.toList
| `(nr_expr| $i:ident) => match varMap i.getId.toString with
  | some ⟨tp, v⟩ => pure ⟨tp, q(Lampe.Expr.var $v)⟩
  | none => throwUnsupportedSyntax
| p => dbg_trace p; throwUnsupportedSyntax

end


declare_syntax_cat nr_param_decl
syntax ident ":" nr_type : nr_param_decl
syntax nr_fn_decl := "fn" nr_ident "<" ident,* ">" "(" nr_param_decl,* ")" "->" nr_type "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}"

def tearOffHNil (emb : β → Type) (a : α) : HList emb [] → α := fun h![] => a

def tearOffHNilQ (α β : Q(Type)) (emb : Q($β → Type)) (a : Q($α)) : Q(HList $emb [] → $α) :=
  q(fun h![] => $a)

@[reducible]
def tearOffHLCons {a : α} {as : List α} {emb : α → Type} (f : emb a → HList emb as → β) : HList emb (a :: as) → β
| HList.cons x xs => f x xs

def tearOffHLConsQ {α β: Q(Type)} {a : Q($α)} {as : Q(List $α)} {emb : Q($α → Type)} (f : Q($emb $a → HList $emb $as → $β))
  : Q(HList $emb ($a :: $as) → $β) := q(tearOffHLCons $f)

def elabFnOfGenerics {β : Q(Type)} (α: Q(Type))
    (emb : Q($α → Type))
    (generics: Q(List $α))
    (idents : List Ident)
    (bodyGen : (Ident → Option Lean.Expr) -> MetaM Q($α))
    : MetaM Q(HList $emb $generics → $β)
  := match idents with
  | [] => do
    let b ← bodyGen fun _ => .none
    pure $ tearOffHNilQ β _ q(Kind.denote) b
  | id :: ids => do
    let lam ← withLocalDeclDQ (Name.mkSimple id) q(Kind.denote .type) fun v => do
      let body ← elabFnOfGenerics α emb generics ids fun ids => do
        bodyGen fun i => if i = id then some v else ids i
      mkLambdaFVars #[v] body
    dbg_trace lam
    mkAppM ``tearOffHLCons #[lam]
    -- pure $ tearOffHLConsQ (emb := q(Kind.denote)) lam

def mkLambda (pName : Ident) (pType : Lean.Expr) (body : Lean.Expr → MetaM Lean.Expr): MetaM Lean.Expr := do
  withLocalDeclD (Name.mkSimple pName) pType fun p => mkLambdaFVars #[p] =<< body p

def mkLambdaOfHList (base : List (Ident × Lean.Expr)) (emb : Lean.Expr) (body : (Ident → Option Lean.Expr) → MetaM Lean.Expr) : MetaM Lean.Expr := match base with
| [] => do mkAppM ``tearOffHNil #[emb, ←body fun _ => none]
| (id, tp) :: rest => do
  let int ← mkLambda id (←mkAppM' emb #[tp]) fun h =>
    mkLambdaOfHList rest emb fun vmap => body (fun i => if i = id then some h else vmap i)
  mkAppM ``tearOffHLCons #[int]

def elabParams (varMap : (Ident  → Option Q(Tp))) : Array Syntax → MetaM (List (Ident × Q(Tp))) := fun params => do
  params.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) =>(i.getId.toString, ·) <$> elabNrType varMap tp
    | _ => throwUnsupportedSyntax

def elabList (α : Q(Type)) : List Q($α) → Q(List $α)
| [] => q([])
| x :: xs => let tail := elabList α xs; q($x :: $tail)

def elabFnDecl : Syntax → MetaM Lean.Expr
| `(nr_fn_decl| fn $name < $generics,* > ( $params,* ) -> $outTp { $body }) => do
  let name : Q(Ident) ← mkStrLit <$> elabNrIdent name
  let generics := generics.getElems.toList.map fun i => (i.getId.toString, mkConst ``Kind.type)
  let genericsDecl ← mkListLit q(Kind) (generics.map (·.2))
  let paramTys ← mkLambdaOfHList generics (mkConst ``Kind.denote) fun varMap => do
    let params ← elabParams varMap params.getElems
    mkListLit q(Tp) (params.map Prod.snd)
  let out ← mkLambdaOfHList generics (mkConst ``Kind.denote) fun varMap => do
    elabNrType varMap outTp
  let body ← mkLambda "rep" q(Tp → Type) fun rep => do
    mkLambdaOfHList generics (mkConst ``Kind.denote) fun tyVars => do
      let params ← elabParams tyVars params.getElems
      mkLambdaOfHList (params.map Prod.snd)

  let fn ← mkAppM ``Function.mk #[genericsDecl, paramTys, out]
  -- pure params
  pure fn
  -- pure q(FunctionDecl.mk $name (Function.mk $genericsDecl $params $out sorry))
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do pure (← elabExpr q(Tp.denote 17) (fun _ => none) expr).2
elab "nrfn![" fn:nr_fn_decl "]" : term => do (elabFnDecl fn)

#check expr![ (1 : u8)]
#check expr![ { let y = (1 : u8) ; let y = y ; y} ]

#check nrfn![ fn myFn<A, B, C>(x : u8, y : A, z : B, w : C) -> u8 { x }]


end Lampe
