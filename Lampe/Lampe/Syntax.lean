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

partial def mkNrIdent [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : Syntax → m String
| `(nr_ident|$i:ident) => pure i.getId.toString
| `(nr_ident|$i:ident :: $j:nr_ident) => do pure s!"{i.getId}::{←mkNrIdent j}"
| i => throwError "Unexpected ident {i}"

syntax ident:nr_type
syntax "${" term "}" : nr_type
syntax nr_ident "<" nr_type,* ">" : nr_type
syntax "[" nr_type "]" : nr_type

def mkListLit [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : List (TSyntax `term) → m (TSyntax `term)
| [] => `([])
| x :: xs => do
  let tail ← mkListLit xs
  `(List.cons $x $tail)

def mkHListLit [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : List (TSyntax `term) → m (TSyntax `term)
| [] => `(HList.nil)
| x :: xs => do
  let tail ← mkHListLit xs
  `(HList.cons $x $tail)

partial def mkNrType [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : TSyntax `nr_type → m (TSyntax `term)
| `(nr_type| u1) => `(Tp.u 1)
| `(nr_type| u8) => `(Tp.u 8)
| `(nr_type| u16) => `(Tp.u 16)
| `(nr_type| u32) => `(Tp.u 32)
| `(nr_type| u64) => `(Tp.u 64)
| `(nr_type| bool) => `(Tp.bool)
| `(nr_type| Field) => `(Tp.field)
| `(nr_type| Unit) => `(Tp.unit)
| `(nr_type| $i:ident) => `($i)
| `(nr_type| $i:nr_ident < $generics,* >) => do
  let name := mkIdent $ Name.mkSimple $ ← mkNrIdent i
  let generics ← generics.getElems.toList.mapM mkNrType
  `(Struct.tp $name $(←mkHListLit generics))
| `(nr_type| ${ $i }) => pure i
| `(nr_type| [ $tp ]) => do `(Tp.slice $(←mkNrType tp))
| _ => throwUnsupportedSyntax

partial def mkBuiltin [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (i : String) : m (TSyntax `term) := match i with
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
| "modulus_num_bits" => `(Builtin.modulusNumBits)
| "to_le_bytes"      => `(Builtin.toLeBytes)
| "fresh"          => `(Builtin.fresh)
| _ => throwError "Unknown builtin {i}"

syntax num ":" nr_type : nr_expr
syntax ident : nr_expr
syntax "#" nr_ident "(" nr_expr,* ")" ":" nr_type : nr_expr
syntax nr_ident "<" nr_type,* ">" "(" nr_expr,* ")" ":" nr_type : nr_expr
syntax nr_ident "<" nr_type,* ">" "{" nr_expr,* "}" : nr_expr
syntax "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}" : nr_expr
syntax "${" term "}" : nr_expr
syntax "$" ident : nr_expr
syntax "let" ident "=" nr_expr : nr_expr
syntax "let" "mut" ident "=" nr_expr : nr_expr
syntax nr_expr "=" nr_expr : nr_expr
syntax nr_expr "." num : nr_expr
syntax "if" nr_expr nr_expr ("else" nr_expr)? : nr_expr
syntax "for" ident "in" nr_expr ".." nr_expr nr_expr : nr_expr
syntax "(" nr_expr ")" : nr_expr
syntax "*(" nr_expr ")" : nr_expr

mutual

partial def mkBlock [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (autoDeref : Name → Bool) : List (TSyntax `nr_expr) → m (TSyntax `term)
| h :: n :: rest => match h with
  | `(nr_expr | let $v = $e ) => do
    let definition ← mkExpr autoDeref e
    let body ← mkBlock autoDeref (n::rest)
    `(Lampe.Expr.letIn $definition fun $v => $body)
  | `(nr_expr | let mut $v = $e) => do
    let definition ← mkExpr autoDeref e
    let body ← mkBlock (fun i => if i = v.getId then true else autoDeref i) (n::rest)
    `(Lampe.Expr.letMutIn $definition fun $v => $body)
  | e => do
    let fst ← mkExpr autoDeref e
    let rest ← mkBlock autoDeref (n::rest)
    `(Lampe.Expr.seq $fst $rest)
| [e] => match e with
  | `(nr_expr | let $_ = $e)
  | `(nr_expr | let mut $_ = $e)
  | `(nr_expr | $e) => mkExpr autoDeref e
| _ => `(Lampe.Expr.skip)

partial def mkProj [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : Nat → m (TSyntax `term)
| 0 => `(Member.head)
| n+1 => do `(Member.tail $(←mkProj n))

partial def mkExpr [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (autoDeref : Name → Bool) : TSyntax `nr_expr → m (TSyntax `term)
| `(nr_expr|$n:num : $tp) => do `(Lampe.Expr.lit $(←mkNrType tp) $n)
| `(nr_expr| true) => `(Lampe.Expr.lit Tp.bool 1)
| `(nr_expr| false) => `(Lampe.Expr.lit Tp.bool 0)
| `(nr_expr| { $exprs;* }) => mkBlock autoDeref exprs.getElems.toList
| `(nr_expr| $i:ident) => do
  let v ← `(Lampe.Expr.var $i)
  if autoDeref i.getId then `(Lampe.Expr.readRef $v) else pure v
| `(nr_expr| # $i:ident ($args,*): $tp) => do
  let args ← args.getElems.toList.mapM (mkExpr autoDeref)
  `(Lampe.Expr.call h![] $(←mkNrType tp) (.builtin $(←mkBuiltin i.getId.toString)) $(←mkHListLit args))
| `(nr_expr| $i:nr_ident < $generics,* > ($args,*) : $tp) => do
  let name ← mkNrIdent i
  let generics ← generics.getElems.toList.mapM mkNrType
  let args ← args.getElems.toList.mapM (mkExpr autoDeref)
  let tyKinds ← mkListLit $ List.replicate generics.length (←`(Kind.type))
  `(Lampe.Expr.call (tyKinds := $tyKinds) $(←mkHListLit generics) $(←mkNrType tp) (.decl $(Syntax.mkStrLit name)) $(←mkHListLit args))
| `(nr_expr| $i:nr_ident < $generics,* > {$args,*}) => do
  let name := mkIdent $ Name.mkSimple $ ← mkNrIdent i
  let generics ← generics.getElems.toList.mapM mkNrType
  let args ← args.getElems.toList.mapM (mkExpr autoDeref)
  `(Struct.constructor $name $(←mkHListLit generics) $(←mkHListLit args))
| `(nr_expr| ${ $term:term }) => pure term
| `(nr_expr| $ $i:ident) => pure i
| `(nr_expr| $e . $n:num) => do `(Lampe.Expr.proj $(←mkProj n.getNat) $(←mkExpr autoDeref e))
| `(nr_expr| if $cond $t else $e) => do
  let cond ← mkExpr autoDeref cond
  let t ← mkExpr autoDeref t
  let e ← mkExpr autoDeref e
  `(Lampe.Expr.ite $cond $t $e)
| `(nr_expr| if $cond $t) => do
  let cond ← mkExpr autoDeref cond
  let t ← mkExpr autoDeref t
  `(Lampe.Expr.ite $cond $t Lampe.Expr.skip)
| `(nr_expr| for $i in $lo .. $hi $body) => do
  let lo ← mkExpr autoDeref lo
  let hi ← mkExpr autoDeref hi
  let body ← mkExpr autoDeref body
  `(Lampe.Expr.loop $lo $hi fun $i => $body)
| `(nr_expr| $v = $e) => do
  let ptr ← mkExpr (fun _ => false) v -- this is a bit hacky, but prevents auto-deref of the LHS var
  let newVal ← mkExpr autoDeref e
  `(Lampe.Expr.writeRef $ptr $newVal)
| `(nr_expr| *($e)) => do
  let ptr ← mkExpr autoDeref e
  `(Lampe.Expr.readRef $ptr)
| `(nr_expr| ( $e )) => mkExpr autoDeref e
| _ => throwUnsupportedSyntax

end

declare_syntax_cat nr_param_decl
syntax ident ":" nr_type : nr_param_decl
syntax nr_fn_decl := nr_ident "<" ident,* ">" "(" nr_param_decl,* ")" "->" nr_type "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}"

def mkFnDecl [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : Syntax → m (String × TSyntax `term)
| `(nr_fn_decl| $name < $generics,* > ( $params,* ) -> $outTp { $bExprs;* }) => do
  let name ← mkNrIdent name
  let generics := generics.getElems.toList.map fun i => (mkIdent $ Name.mkSimple i.getId.toString)
  let genericsDecl ← mkListLit (← generics.mapM fun _ => `(Kind.type))
  let params : List (TSyntax `term × TSyntax `term) ← params.getElems.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) => do pure (i, ←mkNrType tp)
    | _ => throwUnsupportedSyntax
  let inputsDecl ← `(fun generics => match generics with | $(←mkHListLit generics) => $(←mkListLit $ params.map Prod.snd ))
  let outType ← mkNrType outTp
  let outDecl ← `(fun generics => match generics with | $(←mkHListLit generics) => $outType)
  let body ← mkBlock (fun _ => false) bExprs.getElems.toList
  let bodyDecl ← `(
    fun rep generics => match generics with
      | $(←mkHListLit generics) => fun arguments => match arguments with
        | $(←mkHListLit $ params.map Prod.fst) => $body
  )
  let syn : TSyntax `term ← `(FunctionDecl.mk $(Syntax.mkStrLit name) $ Function.mk $genericsDecl $inputsDecl $outDecl $bodyDecl)
  pure (name, syn)
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do (Elab.Term.elabTerm (←mkExpr (fun _ => false) expr).raw none)
elab "nrfn![" "fn" fn:nr_fn_decl "]" : term => do Elab.Term.elabTerm (←mkFnDecl fn).2 none

#check expr![ (1 : u8)]
#check expr![ { let y = (1 : u8) ; let y = y ; y} ]

#check nrfn![ fn myFn<>() -> Unit {}]

#check nrfn![ fn myFn<A, B, C>(x : u8, y : A, z : B, w : C) -> u8 { let x = (1 : u8); x } ]

#check nrfn![ fn weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}]

#check fun x => expr![ ${x} ]

elab "nr_def" decl:nr_fn_decl : command => do
  let (name, decl) ← mkFnDecl decl
  let decl ← `(def $(mkIdent $ Name.mkSimple name) : Lampe.FunctionDecl := $decl)
  Elab.Command.elabCommand decl


-- nr_def weirdEq<I>(x : I, y : I) -> Unit {
--   let a = #fresh() : I;
--   #assert(#eq(a, x) : bool) : Unit;
--   #assert(#eq(a, y) : bool) : Unit;
-- }

-- #print weirdEq

-- #check expr![  std::foo <u8> ( (1 : u8) ) : u8   ]

end Lampe
