import Mathlib
import Lean
import Lampe.Ast

namespace Lampe

open Lean Elab Meta

declare_syntax_cat nr_ident
syntax ident:nr_ident
syntax ident"::"nr_ident : nr_ident

partial def elabNrIdent : Syntax → MetaM String
| `(nr_ident|$x:ident) => pure $ x.getId.toString
| `(nr_ident|$x:ident::$y:nr_ident) => do
  let tl ← elabNrIdent y
  pure $ s!"{x.getId.toString}::{tl}"
| _ => throwUnsupportedSyntax

declare_syntax_cat nr_type
syntax "u" num:nr_type

partial def elabNrType : Syntax → MetaM Lean.Expr
| `(nr_type|u $n:num) => mkAppM ``Tp.u #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

declare_syntax_cat func
syntax:max "assert" : func
syntax:(max-1) nr_ident : func

partial def elabFun : Syntax → MetaM Lean.Expr
| `(func|assert) => mkAppM ``FunctionIdent.builtin #[mkConst ``Builtin.assert]
| `(func|$x:nr_ident) => do
  let x ← elabNrIdent x
  mkAppM ``FunctionIdent.decl #[mkStrLit x]
| _ => throwUnsupportedSyntax

declare_syntax_cat nr_expr

syntax:100 num (":" nr_type)? : nr_expr
syntax:100 nr_ident : nr_expr
syntax:100 "(" nr_expr ")" : nr_expr
syntax:100 "&mut " ident : nr_expr
syntax:100 "*" ident : nr_expr
syntax:100 "if" nr_expr "then" nr_expr ("else" nr_expr)? : nr_expr
syntax:100 "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}" : nr_expr
syntax:100 "let" ident "=" nr_expr : nr_expr
syntax:100 "let" "mut" ident "=" nr_expr : nr_expr
syntax:100 ident "=" nr_expr : nr_expr
syntax:100 func "(" nr_expr,* ")" : nr_expr

syntax:(100-3) nr_expr "[" nr_expr "]" : nr_expr
syntax:(100-5) "!" nr_expr : nr_expr

syntax:(100-10) nr_expr "*" nr_expr : nr_expr
syntax:(100-10) nr_expr "/" nr_expr : nr_expr

syntax:(100-20) nr_expr "+" nr_expr : nr_expr
syntax:(100-20) nr_expr "-" nr_expr : nr_expr

syntax:(100-30) nr_expr "==" nr_expr : nr_expr
syntax:(100-30) nr_expr "<" nr_expr : nr_expr

syntax:(100-35) nr_expr "#as" nr_type : nr_expr

syntax:(100-40) "for" ident "in" nr_expr ".." nr_expr nr_expr : nr_expr

mutual

partial def elabAsBuiltin (name : Name) (args : List Syntax): MetaM Lean.Expr := do
  let fn ← mkAppM ``FunctionIdent.builtin #[mkConst name]
  let args ← args.mapM elabExpr
  let args ← mkListLit (mkConst ``Expr) args
  mkAppM ``Expr.call #[fn, args]

partial def elabExpr : Syntax → MetaM Lean.Expr
| `(nr_expr|$n:num : $tp ) => do
  let tp ← elabNrType tp
  let tp ← mkAppM ``Option.some #[tp]
  mkAppM ``Expr.lit #[mkNatLit n.getNat, tp]
| `(nr_expr|$n:num) => do
  let tp ← mkAppOptM ``Option.none #[some (mkConst ``Tp)]
  mkAppM ``Expr.lit #[mkNatLit n.getNat, tp]
| `(nr_expr|fresh) => mkAppM ``Expr.fresh #[]
| `(nr_expr|true) => do mkAppM ``Expr.lit #[mkNatLit 1, ←mkAppM ``Option.some #[mkConst ``Tp.bool]]
| `(nr_expr|false) => do mkAppM ``Expr.lit #[mkNatLit 0, ←mkAppM ``Option.some #[mkConst ``Tp.bool]]
| `(nr_expr|$x:nr_ident) => do mkAppM ``Expr.var #[mkStrLit (←elabNrIdent x)]
| `(nr_expr|($expr)) => elabExpr expr
| `(nr_expr|&mut $_) => throwUnsupportedSyntax
| `(nr_expr|*$_) => throwUnsupportedSyntax
| `(nr_expr|if $cond then $ifT else $ifF) => do
  let cond ← elabExpr cond
  let ifT ← elabExpr ifT
  let ifF ← elabExpr ifF
  mkAppM ``Expr.ite #[cond, ifT, ifF]
| `(nr_expr|if $cond then $ifT) => do
  let cond ← elabExpr cond
  let ifT ← elabExpr ifT
  let ifF ← mkAppM ``Expr.skip #[]
  mkAppM ``Expr.ite #[cond, ifT, ifF]
| `(nr_expr|{$exprs;*}) => do
  let exprs ← exprs.getElems.mapM elabExpr
  let exprsInit := exprs.toList.dropLast
  let lastExpr ← match exprs.toList.getLast? with
  | some last => pure last
  | none => throwUnsupportedSyntax
  let exprs ← mkListLit (mkConst ``Expr) exprsInit
  mkAppM ``Expr.block #[exprs, lastExpr]
| `(nr_expr|let $x:ident = $val) => do
  let x := mkStrLit x.getId.toString
  let val ← elabExpr val
  mkAppM ``Expr.declareVar #[x, val]
| `(nr_expr|let mut $x:ident = $val) => do
  let x := mkStrLit x.getId.toString
  let val ← elabExpr val
  mkAppM ``Expr.declareMutVar #[x, val]
| `(nr_expr| $x:ident = $val) => do
  let x := mkStrLit x.getId.toString
  let val ← elabExpr val
  mkAppM ``Expr.assignMut #[x, val]
| `(nr_expr|$fn:func($args,*)) => do
  let fn ← elabFun fn
  let args ← args.getElems.mapM elabExpr
  let args ← mkListLit (mkConst ``Expr) args.toList
  mkAppM ``Expr.call #[fn, args]
| `(nr_expr|$lhs * $rhs) => elabAsBuiltin ``Builtin.mul [lhs, rhs]
| `(nr_expr|$lhs / $rhs) => elabAsBuiltin ``Builtin.div [lhs, rhs]
| `(nr_expr|$lhs + $rhs) => elabAsBuiltin ``Builtin.add [lhs, rhs]
| `(nr_expr|$lhs - $rhs) => elabAsBuiltin ``Builtin.sub [lhs, rhs]
| `(nr_expr|$lhs == $rhs) => elabAsBuiltin ``Builtin.eq [lhs, rhs]
| `(nr_expr|$lhs < $rhs) => elabAsBuiltin ``Builtin.lt [lhs, rhs]
| `(nr_expr|!$expr) => elabAsBuiltin ``Builtin.not [expr]
| `(nr_expr|$lhs[$rhs]) => elabAsBuiltin ``Builtin.index [lhs, rhs]
| `(nr_expr|for $i in $s .. $e $body) => do
  let i := mkStrLit i.getId.toString
  let s ← elabExpr s
  let e ← elabExpr e
  let body ← elabExpr body
  mkAppM ``Expr.loop #[i, s, e, body]
| `(nr_expr|$lhs #as $rhs) => do
  let rhs ← elabNrType rhs
  let lhs ← elabExpr lhs
  let bltn ← mkAppM ``Builtin.cast #[rhs]
  let fn ← mkAppM ``FunctionIdent.builtin #[bltn]
  let args ← mkListLit (mkConst ``Expr) [lhs]
  mkAppM ``Expr.call #[fn, args]
| e => do dbg_trace e; throwUnsupportedSyntax

end

elab "nr_expr! {" s:nr_expr "}" : term => elabExpr s

#reduce nr_expr! { 1 : u 8 + 2 }
#reduce nr_expr! { if n == 0 then 0 else { let n = n - 1; k + recadd(n, k) }}

declare_syntax_cat decl

syntax "fn" ident "(" ident,* ")" "{" sepBy1(nr_expr, ";", ";", allowTrailingSep) "}" : decl

partial def elabDecl : Syntax → MetaM Lean.Expr
| `(decl|fn $name:ident($params,* ) {$exprs;*}) => do
  let params := params.getElems.map (fun x => mkStrLit x.getId.toString)
  let params ← mkListLit (mkConst ``Ident) params.toList
  let exprs ← exprs.getElems.mapM elabExpr
  let exprsInit := exprs.toList.dropLast
  let lastExpr ← match exprs.toList.getLast? with
  | some last => pure last
  | none => throwUnsupportedSyntax
  let body ← if exprsInit.isEmpty then
    pure lastExpr
  else
    let exprs ← mkListLit (mkConst ``Expr) exprsInit
    mkAppM ``Expr.block #[exprs, lastExpr]
  let f ← mkAppM ``Function.mk #[params, body]
  let name := mkStrLit name.getId.toString
  mkAppM ``FunctionDecl.mk #[name, f]
| _ => throwUnsupportedSyntax

elab "nr_decl! {" s:decl "}" : term => elabDecl s

#reduce nr_decl! {
  fn add1(n) {
    n + 1
  }
}

declare_syntax_cat module

elab "noir! {" decls:decl* "}" : term => do
  let decls ← decls.mapM (fun decl => elabDecl decl.raw)
  let decls ← mkListLit (mkConst ``FunctionDecl) decls.toList
  mkAppM ``Module.mk #[decls]


#reduce nr_expr! {
      let num_bytes = field::modulus_num_bits()
}

def exampleModule := noir! {
  fn add1(n) {
    n + 1
  }

  fn adder(n, k) {
    if n == 0 then k else {
      let n = n - 1;
      k + adder(n, k)
    }
  }

  fn lt_fallback(x, y) {
      let num_bytes = ((as_u32(field::modulus_num_bits()) + 7) / 8);
      let x_bytes = field::Field::to_le_bytes(x, num_bytes);
      let y_bytes = field::Field::to_le_bytes(y, num_bytes);
      let mut x_is_lt = false;
      let mut done = false;
      for i in 0 .. num_bytes {
          if (!done) then {
              let x_byte = as_u8(x_bytes[((num_bytes - 1) - i)]);
              let y_byte = as_u8(y_bytes[((num_bytes - 1) - i)]);
              let bytes_match = (x_byte == y_byte);
              if (!bytes_match) then {
                  x_is_lt = (x_byte < y_byte);
                  done = true;
              }
          }
      };
      x_is_lt
  }
}

#print exampleModule

end Lampe
