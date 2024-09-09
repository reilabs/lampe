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

def mkLambda (pName : Ident) (pType : Lean.Expr) (body : Lean.Expr → MetaM Lean.Expr): MetaM Lean.Expr := do
  withLocalDeclD (Name.mkSimple pName) pType fun p => mkLambdaFVars #[p] =<< body p

def HList.head : HList emb (a :: as) → emb a
| HList.cons x _ => x

def HList.tail : HList emb (a :: as) → HList emb as
| HList.cons _ xs => xs

def mkHListDestruct (base : List (Ident × Lean.Expr)) (emb : Lean.Expr) (hlist : Lean.Expr) (body : (Ident → Option (Lean.Expr × Lean.Expr)) → MetaM Lean.Expr) : MetaM Lean.Expr := match base with
| [] => body fun _ => .none
| (id, e) :: rest => do
  withLetDecl (Name.mkSimple id) (←mkAppM' emb #[e]) (←mkAppM ``HList.head #[hlist]) fun v => do
    let rest ← mkHListDestruct rest emb (←mkAppM ``HList.tail #[hlist]) fun vmap => body (fun i => if i = id then some (e, v) else vmap i)
    mkLetFVars #[v] rest

def mkLambdaOfHList' (pName: Ident) (elemType : Lean.Expr) (base : List (Ident × Lean.Expr)) (emb : Lean.Expr) (body : (Ident → Option (Lean.Expr × Lean.Expr)) → MetaM Lean.Expr) :
    MetaM Lean.Expr := do
  let args ← mkListLit elemType (base.map (·.2))
  mkLambda pName (←mkAppM ``HList #[emb, args]) fun h => mkHListDestruct base emb h body

def elabParams (varMap : (Ident  → Option Q(Tp))) : Array Syntax → MetaM (List (Ident × Q(Tp))) := fun params => do
  params.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) =>(i.getId.toString, ·) <$> elabNrType varMap tp
    | _ => throwUnsupportedSyntax

def elabList (α : Q(Type)) : List Q($α) → Q(List $α)
| [] => q([])
| x :: xs => let tail := elabList α xs; q($x :: $tail)

def elabFnDecl : Syntax → MetaM Lean.Expr
| `(nr_fn_decl| fn $name < $generics,* > ( $params,* ) -> $outTp { $bExprs;* }) => do
  let name : Q(Ident) ← mkStrLit <$> elabNrIdent name
  let generics := generics.getElems.toList.map fun i => (i.getId.toString, mkConst ``Kind.type)
  let genericsDecl ← mkListLit q(Kind) (generics.map (·.2))
  let paramTys ← mkLambdaOfHList' "generics" (mkConst ``Kind) generics (mkConst ``Kind.denote) fun varMap => do
    let params ← elabParams (fun i => Prod.snd <$> varMap i) params.getElems
    mkListLit q(Tp) (params.map Prod.snd)
  dbg_trace paramTys
  let out ← mkLambdaOfHList' "generics" (mkConst ``Kind) generics (mkConst ``Kind.denote) fun varMap => do
    elabNrType (fun i => Prod.snd <$> varMap i) outTp
  let body ← mkLambda "rep" q(Tp → Type) fun rep => do
    mkLambdaOfHList' "generics" (mkConst ``Kind) generics (mkConst ``Kind.denote) fun tyVars => do
      let params ← elabParams (fun i => Prod.snd <$> tyVars i) params.getElems
      mkLambdaOfHList' "arguments" (mkConst ``Tp) params rep fun varMap => do
        let ⟨_, expr⟩ ← elabBlock rep (fun i => (fun (tp, v) => ⟨tp, v⟩) <$> varMap i) bExprs.getElems.toList
        pure expr
  let fn ← mkAppM ``FunctionDecl.mk #[name, ←mkAppM ``Function.mk #[genericsDecl, paramTys, out, body]]
  pure fn
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do pure (← elabExpr q(Tp.denote 17) (fun _ => none) expr).2
elab "nrfn![" fn:nr_fn_decl "]" : term => do (elabFnDecl fn)

#check expr![ (1 : u8)]
#check expr![ { let y = (1 : u8) ; let y = y ; y} ]

#check nrfn![ fn myFn<A, B, C>(x : u8, y : A, z : B, w : C) -> u8 { let hehe = x ; hehe } ]


end Lampe
