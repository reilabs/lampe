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

partial def elabNrIdent : Syntax → TermElabM String
| `(nr_ident|$x:ident) => pure $ x.getId.toString
| `(nr_ident|$x:ident::$y:nr_ident) => do
  let tl ← elabNrIdent y
  pure $ s!"{x.getId.toString}::{tl}"
| _ => throwUnsupportedSyntax

syntax ident:nr_type
syntax ident "<" nr_type,* ">" : nr_type

def mkListLit : List (TSyntax `term) → MetaM (TSyntax `term)
| [] => `([])
| x :: xs => do
  let tail ← mkListLit xs
  `(List.cons $x $tail)

def mkHListLit : List (TSyntax `term) → MetaM (TSyntax `term)
| [] => `(HList.nil)
| x :: xs => do
  let tail ← mkHListLit xs
  `(HList.cons $x $tail)

partial def elabNrType (vmap : String → Option Q(Tp)): Syntax → TermElabM Q(Tp)
| `(nr_type| u1) => pure q(Tp.u 1)
| `(nr_type| u8) => pure q(Tp.u 8)
| `(nr_type| u16) => pure q(Tp.u 16)
| `(nr_type| u32) => pure q(Tp.u 32)
| `(nr_type| u64) => pure q(Tp.u 64)
| `(nr_type| bool) => pure q(Tp.bool)
| `(nr_type| Field) => pure q(Tp.field)
| `(nr_type| Unit) => pure q(Tp.unit)
| `(nr_type| $i:ident) => match vmap i.getId.toString with
  | some tp => pure tp
  | none => throwError "Unknown type {i.getId.toString}"
| _ => throwUnsupportedSyntax

partial def mkNrType : TSyntax `nr_type → MetaM (TSyntax `term)
| `(nr_type| u1) => `(Tp.u 1)
| `(nr_type| u8) => `(Tp.u 8)
| `(nr_type| u16) => `(Tp.u 16)
| `(nr_type| u32) => `(Tp.u 32)
| `(nr_type| u64) => `(Tp.u 64)
| `(nr_type| bool) => `(Tp.bool)
| `(nr_type| Field) => `(Tp.field)
| `(nr_type| Unit) => `(Tp.unit)
| `(nr_type| $i:ident) => `($i)
| _ => throwUnsupportedSyntax

partial def elabBuiltin (i : String) : TermElabM Q(Builtin) := match i with
| "add"            => pure q(Builtin.add)
| "sub"            => pure q(Builtin.sub)
| "mul"            => pure q(Builtin.mul)
| "div"            => pure q(Builtin.div)
| "eq"             => pure q(Builtin.eq)
| "assert"         => pure q(Builtin.assert)
| "not"            => pure q(Builtin.not)
| "lt"             => pure q(Builtin.lt)
| "index"          => pure q(Builtin.index)
| "cast"           => pure q(Builtin.cast)
| "modulusNumBits" => pure q(Builtin.modulusNumBits)
| "toLeBytes"      => pure q(Builtin.toLeBytes)
| "fresh"          => pure q(Builtin.fresh)
| _ => throwError "Unknown builtin {i}"

partial def mkBuiltin (i : String) : MetaM (TSyntax `term) := match i with
| "add"            => `(Builtin.add)
| "sub"            => `(Builtin.sub)
| "mul"            => `(Builtin.mul)
| "div"            => `(Builtin.div)
| "eq"             => `(Builtin.eq)
| "assert"         => `(Builtin.assert)
| "not"            => `(Builtin.not)
| "lt"             => `(Builtin.lt)
| "index"          => `(Builtin.index)
| "cast"           => `(Builtin.cast)
| "modulusNumBits" => `(Builtin.modulusNumBits)
| "toLeBytes"      => `(Builtin.toLeBytes)
| "fresh"          => `(Builtin.fresh)
| _ => throwError "Unknown builtin {i}"

syntax:100 "(" num ":" nr_type ")" : nr_expr
syntax:100 ident : nr_expr
syntax:100 "#" nr_ident "(" nr_expr,* ")" ":" nr_type : nr_expr
syntax:100 nr_ident "<" nr_type,* ">" "(" nr_expr,* ")" : nr_expr
syntax:100 "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}" : nr_expr
syntax:100 "let" ident "=" nr_expr : nr_expr

def lit (rep : Q(Tp → Type)) (tp : Q(Tp)) (n : Nat) : Q(Lampe.Expr $rep $tp) := q(Lampe.Expr.lit $tp $n)
def letIn (rep : Q(Tp → Type)) (etp : Q(Tp)) (rtp : Q(Tp)) (ebody : Q(Lampe.Expr $rep $etp)) (rbody : Q($rep $etp → Lampe.Expr $rep $rtp)) : Q(Lampe.Expr $rep $rtp) := q(Lampe.Expr.letIn $ebody $rbody)

mutual

partial def elabBlock (rep : Q(Tp → Type)) (tyVarMap : Ident → Option Q(Tp)) (varMap : String → Option ((tp : Q(Tp)) × Q($rep $tp))) : List Syntax → TermElabM ((tp : Q(Tp)) × Q(Lampe.Expr $rep $tp))
| h :: n :: rest => match h with
  | `(nr_expr | let $v = $e ) => do
    let ⟨etp, expr⟩ ← elabExpr rep tyVarMap varMap e
    let ⟨btp, bExpr⟩ ← withLocalDeclDQ (Name.mkSimple v.getId.toString) q($rep $etp) fun v' => do
      let ⟨resttp, rest⟩ ← elabBlock rep tyVarMap (fun s => if s = v.getId.toString then some ⟨etp, v'⟩ else varMap s) (n::rest)
      pure (resttp, ←mkLambdaFVars #[v'] rest)
    pure ⟨btp, letIn rep etp btp expr bExpr⟩
  | e => do
    let ⟨_, expr⟩ ← elabExpr rep tyVarMap varMap e
    let ⟨resttp, rest⟩ ← elabBlock rep tyVarMap varMap (n::rest)
    pure ⟨resttp, q(Lampe.Expr.seq $expr $rest)⟩
| [e] => match e with
  | `(nr_expr | let $_ = $e)
  | `(nr_expr | $e) => elabExpr rep tyVarMap varMap e
| _ => pure ⟨q(Tp.unit), q(Lampe.Expr.skip)⟩

partial def mkBlock : List (TSyntax `nr_expr) → MetaM (TSyntax `term)
| h :: n :: rest => match h with
  | `(nr_expr | let $v = $e ) => do
    let definition ← mkExpr e
    let body ← mkBlock (n::rest)
    `(Lampe.Expr.letIn $definition fun $v => $body)
  | e => do
    let fst ← mkExpr e
    let rest ← mkBlock (n::rest)
    `(Lampe.Expr.seq $fst $rest)
| [e] => match e with
  | `(nr_expr | let $_ = $e)
  | `(nr_expr | $e) => mkExpr e
| _ => `(Lampe.Expr.skip)


partial def mkExpr : TSyntax `nr_expr → MetaM (TSyntax `term)
| `(nr_expr|($n:num : $tp)) => do `(Lampe.Expr.lit $(←mkNrType tp) $n)
| `(nr_expr| { $exprs;* }) => mkBlock exprs.getElems.toList
| `(nr_expr| $i:ident) => `(Lampe.Expr.var $i)
| `(nr_expr| # $i:ident ($args,*): $tp) => do
  let args ← args.getElems.toList.mapM mkExpr
  `(Lampe.Expr.call h![] $(←mkNrType tp) (.builtin $(←mkBuiltin i.getId.toString)) $(←mkHListLit args))
| _ => throwUnsupportedSyntax

partial def elabExpr (rep : Q(Tp → Type)) (tyVarMap : Ident → Option Q(Tp)) (varMap : String → Option ((tp : Q(Tp)) × Q($rep $tp))) : Syntax → TermElabM ((tp : Q(Tp)) × Q(Lampe.Expr $rep $tp))
| `(nr_expr|($n:num : $tp)) => do
  let tp ← elabNrType tyVarMap tp
  let num ← pure n.getNat
  pure ⟨tp, lit rep tp num⟩
| `(nr_expr| { $exprs;* }) => elabBlock rep tyVarMap varMap exprs.getElems.toList
| `(nr_expr| $i:ident) => match varMap i.getId.toString with
  | some ⟨tp, v⟩ => pure ⟨tp, q(Lampe.Expr.var $v)⟩
  | none => throwUnsupportedSyntax
| `(nr_expr| # $i:ident ($args,*): $tp) => do
  let tp ← elabNrType tyVarMap tp
  let args ← args.getElems.toList.mapM fun e => elabExpr rep tyVarMap varMap e
  let argsHList ← args.foldrM (fun ⟨tp, v⟩ rest => do
    mkAppM ``HList.cons #[v, rest]
  ) (← mkAppOptM ``HList.nil #[none, some $ ← mkAppM ``Expr #[rep]])
  let builtin ← elabBuiltin i.getId.toString
  let decl ← mkAppM ``FunctionIdent.builtin #[builtin]
  let call ← mkAppM ``Lampe.Expr.call #[
    ←mkAppOptM ``HList.nil #[none, some $ mkConst ``Kind.denote],
    tp,
    decl,
    argsHList
  ]
  pure ⟨tp, call⟩
| _ => throwUnsupportedSyntax

end

declare_syntax_cat nr_param_decl
syntax ident ":" nr_type : nr_param_decl
syntax nr_fn_decl := "fn" nr_ident "<" ident,* ">" "(" nr_param_decl,* ")" "->" nr_type "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}"

def mkLambda (pName : Ident) (body : Lean.Expr → TermElabM Lean.Expr): TermElabM Lean.Expr := do
  Elab.Term.elabBinder (mkIdent $ Name.mkSimple pName) fun e => do
    let body ← body e
    mkLambdaFVars #[e] body

@[reducible]
def HList.head : HList emb (a :: as) → emb a
| HList.cons x _ => x

@[reducible]
def HList.tail : HList emb (a :: as) → HList emb as
| HList.cons _ xs => xs

def mkHListDestruct (base : List (Ident × Lean.Expr)) (hlist : Lean.Expr) (body : (Ident → Option (Lean.Expr × Lean.Expr)) → TermElabM Lean.Expr) : TermElabM Lean.Expr := match base with
| [] => body fun _ => .none
| (id, e) :: rest => do
  withLetDecl (Name.mkSimple id) (←mkFreshExprMVar none) (←mkAppM ``HList.head #[hlist]) fun v => do
    let rest ← mkHListDestruct rest (←mkAppM ``HList.tail #[hlist]) fun vmap => body (fun i => if i = id then some (e, v) else vmap i)
    mkLetFVars #[v] rest

def mkLambdaOfHList' (pName: Ident) (base : List (Ident × Lean.Expr)) (body : (Ident → Option (Lean.Expr × Lean.Expr)) → TermElabM Lean.Expr) :
    TermElabM Lean.Expr := do
  dbg_trace "mkLambdaOfHList' {pName}"
  mkLambda pName fun h => do
    dbg_trace "mkLambdaOfHList' {pName}"
    mkHListDestruct base h body

def elabParams (varMap : (Ident  → Option Q(Tp))) : Array Syntax → TermElabM (List (Ident × Q(Tp))) := fun params => do
  params.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) =>(i.getId.toString, ·) <$> elabNrType varMap tp
    | _ => throwUnsupportedSyntax

def elabList (α : Q(Type)) : List Q($α) → Q(List $α)
| [] => q([])
| x :: xs => let tail := elabList α xs; q($x :: $tail)



def elabFnDecl : Syntax → TermElabM Lean.Expr
| `(nr_fn_decl| fn $name < $generics,* > ( $params,* ) -> $outTp { $bExprs;* }) => do
  let name ← elabNrIdent name
  let generics := generics.getElems.toList.map fun i => (mkIdent $ Name.mkSimple i.getId.toString)
  let genericsDecl ← mkListLit (← generics.mapM fun _ => `(Kind.type))
  let params : List (TSyntax `term × TSyntax `term) ← params.getElems.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) => do pure (i, ←mkNrType tp)
    | _ => throwUnsupportedSyntax
  let inputsDecl ← `(fun generics => match generics with | $(←mkHListLit generics) => $(←mkListLit $ params.map Prod.snd ))
  let outType ← mkNrType outTp
  let outDecl ← `(fun generics => match generics with | $(←mkHListLit generics) => $outType)
  let body ← mkBlock bExprs.getElems.toList
  let bodyDecl ← `(
    fun rep generics => match generics with
      | $(←mkHListLit generics) => fun arguments => match arguments with
        | $(←mkHListLit $ params.map Prod.fst) => $body
  )
  let syn : TSyntax `term ← `(FunctionDecl.mk $(Syntax.mkStrLit name) $ Function.mk $genericsDecl $inputsDecl $outDecl $bodyDecl)
  Elab.Term.elabTerm syn.raw none
  -- let name : Q(Ident) ← mkStrLit <$> elabNrIdent name
  -- dbg_trace "elabFnDecl {name}"
  -- let generics := generics.getElems.toList.map fun i => (i.getId.toString, mkConst ``Kind.type)
  -- dbg_trace "elabFnDecl {name}"

  -- let genericsDecl ← mkListLit q(Kind) (generics.map (·.2))
  -- dbg_trace "elabFnDecl {name}"

  -- let paramTys ← mkLambdaOfHList' "generics" generics fun varMap => do
  --   let x : TSyntax _ := `(fun generics => $body)
  --   dbg_trace "elabFnDecl {name}"
  --   let params ← elabParams (fun i => Prod.snd <$> varMap i) params.getElems
  --   mkListLit q(Tp) (params.map Prod.snd)
  -- -- let out ← mkLambdaOfHList' "generics" generics fun varMap => do
  -- --   elabNrType (fun i => Prod.snd <$> varMap i) outTp
  -- -- let body ← mkLambda "rep" fun rep => do
  -- --   mkLambdaOfHList' "generics" generics fun tyVars => do
  -- --     let params ← elabParams (fun i => Prod.snd <$> tyVars i) params.getElems
  -- --     mkLambdaOfHList' "arguments" params fun varMap => do
  -- --       let ⟨_, expr⟩ ← elabBlock
  -- --         rep
  -- --         (fun i => Prod.snd <$> tyVars i)
  -- --         (fun i => (fun (tp, v) => ⟨tp, v⟩) <$> varMap i)
  -- --         bExprs.getElems.toList
  -- --       pure expr
  -- let fn ← mkAppM ``Function.mk #[genericsDecl, paramTys]--, out, body]
  -- pure fn
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do pure (← elabExpr q(Tp.denote 17) default (fun _ => none) expr).2
elab "nrfn![" fn:nr_fn_decl "]" : term => do (elabFnDecl fn)

#check expr![ (1 : u8)]
#check expr![ { let y = (1 : u8) ; let y = y ; y} ]

#check nrfn![ fn myFn<>() -> Unit {}]

#check nrfn![ fn myFn<A, B, C>(x : u8, y : A, z : B, w : C) -> u8 { let x = (1 : u8); x } ]

#check nrfn![ fn weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}]

end Lampe
