import Lean
import Lampe.Hoare.SepTotal
import Lampe.Syntax
import Lampe.Tactic.Steps

open Lean
open PrettyPrinter
-- open Delaborator
-- open SubExpr
open Lampe

declare_syntax_cat pp_tp
syntax "u" noWs num : pp_tp
syntax "i" noWs num : pp_tp
syntax "bi" : pp_tp
syntax "bool" : pp_tp
syntax "unit" : pp_tp
syntax "str<" num ">" : pp_tp
syntax "fmtStr" noWs "<" num "," pp_tp,*">" : pp_tp
syntax "field" : pp_tp
syntax "[" pp_tp "]" : pp_tp
syntax "[" pp_tp ";" num "]" : pp_tp
syntax "(" pp_tp,* ")" : pp_tp
syntax "refTp" pp_tp : pp_tp
syntax "λ(" pp_tp,* ")" "->" pp_tp : pp_tp

def delabTpU : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
  | `($(_) $n:num) => do
    if let some n := n.raw.isNatLit? then
      let n := Syntax.mkNatLit n
      `(pp_tp|u$n)
    else
      throw ()
  | _ => throw ()

def delabTpI : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
  | `($(_) $n:num) => do
    if let some n := n.raw.isNatLit? then
      let n := Syntax.mkNatLit n
      `(pp_tp|i$n)
    else
      throw ()
  | _ => throw ()

def delabTpBi : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_)) => `(pp_tp|bi)

def delabTpBool : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_)) => `(pp_tp|bool)

def delabTpUnit : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_)) => `(pp_tp|unit)

def delabTpStr :  TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) $n:num) => do
  if let some n := n.raw.isNatLit? then
    let n := Syntax.mkNatLit n
    `(pp_tp|str<$n>)
  else
    throw ()
| _ => throw ()

def delabTpField :  TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_)) => `(pp_tp|field)

mutual

-- TODO: Finish this
partial def delabTpFmtStr :  TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) $n:num [$tps,*]) => do
  if let some n := n.raw.isNatLit? then
    let n := Syntax.mkNatLit n
    `(pp_tp|fmtStr<$n,>)
  else
    throw ()
| _ => throw ()

partial def delabTpSlice : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) $tp) => do `(pp_tp|[$(← delabTp tp)])
| _ => throw ()

partial def delabTpArray : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) $tp $n:num) => do
  if let some n := n.raw.isNatLit? then
    let n := Syntax.mkNatLit n
    `(pp_tp|[$(← delabTp tp); $n])
  else
    throw ()
| _ => throw ()

-- TODO: Finish this
partial def delabTpTuple : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) $name:ident [$tps,*]) => do
  let name := mkIdent name.raw.getId
  `(pp_tp| ())
| _ => throw ()

partial def delabTpRef : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) $tp) => do `(pp_tp|refTp $(← delabTp tp))
| _ => throw ()

-- TODO: Finish this
partial def delabTpFn : TSyntax `term → (UnexpandM <| TSyntax `pp_tp)
| `($(_) [$argTps,*] $outTp) => do `(pp_tp|λ() -> $(← delabTp outTp))
| _ => throw ()

partial def delabTp (stx : TSyntax `term) : UnexpandM <| TSyntax `pp_tp := do
  match stx with
    | `(``Tp.u $_) => delabTpU stx
    | `(``Tp.i $_) => delabTpI stx
    | `(``Tp.bi) => delabTpBi stx
    | `(``Tp.bool) => delabTpBool stx
    | `(``Tp.unit) => delabTpUnit stx
    | `(``Tp.str $_) => delabTpStr stx
    | `(``Tp.fmtStr $_ $_) => delabTpFmtStr stx
    | `(``Tp.field) => delabTpField stx
    | `(``Tp.slice $_) => delabTpSlice stx
    | `(``Tp.array $_) => delabTpArray stx
    | `(``Tp.tuple $_) => delabTpTuple stx
    | `(``Tp.ref $_) => delabTpRef stx
    | `(``Tp.fn $_) => delabTpFn stx
    | _ => throw ()

end

declare_syntax_cat pp_kind
syntax "u" noWs num : pp_kind
syntax "field" : pp_kind
syntax "type" : pp_kind

def delabKindU : TSyntax `term → (UnexpandM <| TSyntax `pp_kind)
| `($(_) $n:num) => do
  if let some n := n.raw.isNatLit? then
    let n := Syntax.mkNatLit n
    `(pp_kind|u$n)
  else
    throw ()
| _ => throw ()

def delabKindField : TSyntax `term → (UnexpandM <| TSyntax `pp_kind)
| `($(_)) => `(pp_kind|field)

def delabKindType : TSyntax `term → (UnexpandM <| TSyntax `pp_kind)
| `($(_)) => `(pp_kind|type)

declare_syntax_cat pp_expr
declare_syntax_cat pp_fn_binders
declare_syntax_cat pp_fn_generics
declare_syntax_cat pp_kinds

syntax "⟪" ppLine pp_expr ppLine "⟫" : term
syntax "@(" term ")": pp_expr
syntax num : pp_expr -- litNums, constFps, and constUs
syntax str : pp_expr -- litStrs, and fmtStrs
syntax ident : pp_kinds
syntax "<" pp_kinds,* ">" : pp_fn_generics
syntax "(" pp_expr,* ")" : pp_fn_binders
syntax "λ#" num pp_fn_binders : pp_expr -- lambda funcref
syntax ident pp_fn_generics pp_fn_binders : pp_expr -- decl and trait funcrefs
syntax ident : pp_expr -- Get
syntax ppDedent("let " ident " := " pp_expr ppHardLineUnlessUngrouped pp_expr) : pp_expr
syntax "#" ident pp_fn_binders : pp_expr -- builtin call
syntax "if" pp_expr "then" pp_expr "else" pp_expr : pp_expr
syntax "skip" : pp_expr
syntax "for" pp_expr "in" pp_expr "do" pp_expr : pp_expr

instance : Coe NumLit (TSyntax `pp_expr) where
  coe s := ⟨s.raw⟩

instance : Coe StrLit (TSyntax `pp_expr) where
  coe s := ⟨s.raw⟩

instance : Coe Lean.Ident (TSyntax `pp_expr) where
  coe s := ⟨s.raw⟩

@[app_unexpander Expr.litNum]
def delabLitNum : Unexpander
| `($(_) $_ $n:num) => `(⟪ $n ⟫)
| `($(_) $_ $num) => `(⟪@($num)⟫)
| stx => pure stx

@[app_unexpander Expr.litStr]
def delabLitStr : Unexpander
| `($(_) $_ $s) => do
  let stringPart := s.raw[1][0][1].getArgs
  let mut string := ""
  for c? in stringPart do
    if let some c := c?.isCharLit? then
      string := string.push c
  let stringStx := Syntax.mkStrLit string
  `(⟪ $stringStx ⟫)
| stx => pure stx

@[app_unexpander Expr.constFp]
def delabConstFp : Unexpander
| `($(_) $n:num $_) => `(⟪ $n ⟫)
| `($(_) $n $_) => `(⟪@($n)⟫)
| stx => pure stx

@[app_unexpander Expr.constU]
def delabConstU : Unexpander
| `($(_) $n:num $_) => `(⟪ $n ⟫)
| `($(_) $n $_) => `(⟪@($n)⟫)
| stx => pure stx

@[app_unexpander Expr.fmtStr]
def delabFmtStr : Unexpander
| `($(_) $_ $_ $fmtstr) => `(⟪@($fmtstr)⟫) -- TODO: finish this
| stx => pure stx

syntax ">>>" term "<<<" : pp_expr

@[app_unexpander Expr.fn]
def delabFn : Unexpander
| `($(_) $_ $_ $funcref) =>
  match funcref with
  | `(FuncRef.lambda $ref) => do
    match ref with
    | `($(_) $n:num) => do
      if let some n := n.raw.isNatLit? then
        let n := Syntax.mkNatLit n
        `(⟪ λ#$n() ⟫)
      else
        throw ()
    | stx => pure stx
  | `(FuncRef.decl $name:str [$kinds,*] h![$generics,*]) => do
    let name := mkIdent <| .mkSimple <| name.raw.isStrLit?.getD ""
    `(⟪ $name:ident <> ()  ⟫)
  | `(FuncRef.trait $selfTp $traitName $kinds $generics $fnName $fnKinds $fnGenerics) => do
    let name := mkIdent traitName.raw.getId
    let fnName := mkIdent fnName.raw.getId
    `(⟪ $name:ident <> ()  ⟫)
  | stx => pure stx
| stx => pure stx

@[app_unexpander Expr.var]
def delabVar : Unexpander
| `($(_) $var:ident) =>
  `(⟪ $var ⟫)
| stx => pure stx

@[app_unexpander Expr.letIn]
def delabLetIn : Unexpander
| `($(_) ⟪$a⟫ fun $v => ⟪$body⟫) =>
  let binding := mkIdent v.raw.getId
  `(⟪ let $binding := $a $body ⟫)
| `($(_) $a fun $v => ⟪$body⟫) =>
  let binding := mkIdent v.raw.getId
  `(⟪ let $binding := @($a) $body⟫)
| stx => pure stx


@[app_unexpander Expr.call]
def delabCall : Unexpander
| `($(_) $_ $_ $funcRef $args) => do
  `(⟪@($funcRef:term)⟫)
| stx => pure stx

-- TODO: Will likely need this
-- @[app_unexpander Lampe.FunctionDecl.call]
-- def delabFunctionDeclCall : Unexpander
-- | `($(_) $decl $gens $args) => do
--   let x := mkIdent decl.raw.getId
--   `($x <$gens> ($args))
-- | _ => pure

@[app_unexpander Expr.callBuiltin]
def delabCallBuiltin : Unexpander
| `($(_) $_ $_ $builtin h![$args,*]) =>
  let builtin := mkIdent builtin.raw.getId
  `(⟪ #$builtin:ident () ⟫)
| stx => pure stx


@[app_unexpander Expr.ite]
def delabITE : Unexpander
| `($(_) $cond ⟪$ifTrue⟫ ⟪$ifFalse⟫) =>
  let cond := mkIdent cond.raw.getId
  `(⟪ if $cond then $ifTrue else $ifFalse ⟫)
| stx => pure stx

@[app_unexpander Expr.skip]
def delabSkip : Unexpander
| `($(_)) =>
  `(⟪ skip ⟫)


@[app_unexpander Expr.loop]
def delabLoop : Unexpander
| `($(_) $low $high (fun $var => ⟪$body⟫)) =>
  let low := mkIdent low.raw.getId
  let high := mkIdent high.raw.getId
  let _ := mkIdent var.raw.getId
  `(⟪ for $low in $high do $body ⟫)
| stx => pure stx

-- TODO: gotta do this
@[app_unexpander Lampe.Expr.lam]
def delabLam : Unexpander
| stx => pure stx

section STHoare

declare_syntax_cat slp_cond
declare_syntax_cat sthoare

syntax "⦃" term "⦄" : slp_cond
syntax slp_cond ppLine ppLine term ppLine ppLine slp_cond : term

@[app_unexpander STHoare]
def delabSTHoare : Unexpander
| `($(_) $_ $_ $P ⟪$C⟫ $Q) =>
  `(⦃$P⦄ ⟪$C⟫ ⦃$Q⦄)
| `($(_) $_ $_ $P $C $Q) =>
  `(⦃$P⦄ $C ⦃$Q⦄)
| _ => pure

nr_def simple_muts<>(x : Field) -> Field {
  #fAdd(x, 1 : Field) : Field;
}

nr_def simple_muts2<>(x : Field) -> Field {
  let y = 5 : Field;
  let x = (@simpl_muts<> as λ(Field) → Field)(y);
  x
}

def Γ := Lampe.Env.mk [simple_muts, simple_muts2] []

example : STHoare p Γ ⟦⟧ (simple_muts2.call h![] h![x]) fun v => v = x := by
  enter_decl
  steps
  simp_all


end STHoare

