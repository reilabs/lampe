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

partial def mkNrIdent : Syntax → MetaM String
| `(nr_ident|$i:ident) => pure i.getId.toString
| `(nr_ident|$i:ident :: $j:nr_ident) => do pure s!"{i.getId}::{←mkNrIdent j}"
| i => throwError "Unexpected ident {i}"

syntax ident:nr_type
syntax nr_ident "<" nr_type,* ">" : nr_type

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
| `(nr_type| $i:nr_ident < $generics,* >) => do
  let name := mkIdent $ Name.mkSimple $ ← mkNrIdent i
  let generics ← generics.getElems.toList.mapM mkNrType
  `(Struct.tp $name $(←mkHListLit generics))
| _ => throwUnsupportedSyntax

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

syntax "(" num ":" nr_type ")" : nr_expr
syntax ident : nr_expr
syntax "#" nr_ident "(" nr_expr,* ")" ":" nr_type : nr_expr
syntax nr_ident "<" nr_type,* ">" "(" nr_expr,* ")" : nr_expr
syntax nr_ident "<" nr_type,* ">" "{" nr_expr,* "}" : nr_expr
syntax "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}" : nr_expr
syntax "let" ident "=" nr_expr : nr_expr

mutual

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
| `(nr_expr| false) => `(Lampe.Expr.lit Tp.bool 0)
| `(nr_expr| { $exprs;* }) => mkBlock exprs.getElems.toList
| `(nr_expr| $i:ident) => `(Lampe.Expr.var $i)
| `(nr_expr| # $i:ident ($args,*): $tp) => do
  let args ← args.getElems.toList.mapM mkExpr
  `(Lampe.Expr.call h![] $(←mkNrType tp) (.builtin $(←mkBuiltin i.getId.toString)) $(←mkHListLit args))
| `(nr_expr| $i:nr_ident < $generics,* > {$args,*}) => do
  let name := mkIdent $ Name.mkSimple $ ← mkNrIdent i
  let generics ← generics.getElems.toList.mapM mkNrType
  let args ← args.getElems.toList.mapM mkExpr
  `(Struct.constructor $name $(←mkHListLit generics) $(←mkHListLit args))
| _ => throwUnsupportedSyntax

end

declare_syntax_cat nr_param_decl
syntax ident ":" nr_type : nr_param_decl
syntax nr_fn_decl := "fn" nr_ident "<" ident,* ">" "(" nr_param_decl,* ")" "->" nr_type "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}"

def mkFnDecl : Syntax → TermElabM Lean.Expr
| `(nr_fn_decl| fn $name < $generics,* > ( $params,* ) -> $outTp { $bExprs;* }) => do
  let name ← mkNrIdent name
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
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do (Elab.Term.elabTerm (←mkExpr expr).raw none)
elab "nrfn![" fn:nr_fn_decl "]" : term => do (mkFnDecl fn)

#check expr![ (1 : u8)]
#check expr![ { let y = (1 : u8) ; let y = y ; y} ]

#check nrfn![ fn myFn<>() -> Unit {}]

#check nrfn![ fn myFn<A, B, C>(x : u8, y : A, z : B, w : C) -> u8 { let x = (1 : u8); x } ]

#check nrfn![ fn weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}]

def «std::Option» : Struct := {
  name := "std::Option",
  tyArgKinds := [Kind.type],
  fieldTypes := fun h![T] => [Tp.bool, T]
}

#check nrfn![ fn std::Option::some<I>(x : I) -> std::Option<I> {
  std::Option <I> { false, x };
}]

end Lampe
