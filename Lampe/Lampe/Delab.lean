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
syntax "ref" pp_tp : pp_tp
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
| `($(_) $tp) => do `(pp_tp|ref $(← delabTp tp))
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
syntax ">>>" pp_expr "<<<" : term

syntax num : pp_expr -- litNums, constFps, and constUs
instance : Coe NumLit (TSyntax `pp_expr) where
  coe s := ⟨s.raw⟩

syntax str : pp_expr -- litStrs, and fmtStrs
instance : Coe StrLit (TSyntax `pp_expr) where
  coe s := ⟨s.raw⟩

-- declare_syntax_cat letin
-- declare_syntax_cat

-- syntax term : expr
-- syntax letin : expr
-- syntax ident noWs "<" sepBy(expr, ",", ",", allowTrailingSep) ">" noWs "(" sepBy(expr, ",", ",", allowTrailingSep) ")" : expr
-- syntax "let" ident ws "=" ws expr ";" : letin

@[app_unexpander Expr.litNum]
def delabLitNum : Unexpander
| `($(_) $_ $n:num) => `(>>> $n <<<)
| _ => pure


@[app_unexpander Expr.litStr]
def delabLitStr : Unexpander
| `($(_) $_ $s) => do
  let stringPart := s.raw[1][0][1].getArgs
  let mut string := ""
  for c? in stringPart do
    if let some c := c?.isCharLit? then
      string := string.push c
  let stringStx := Syntax.mkStrLit string
  `(>>> $stringStx <<<)
| _ => pure


@[app_unexpander Expr.constFp]
def delabConstFp : Unexpander
| `($(_) $n:num $_) => `(>>> $n <<<)
| _ => pure

@[app_unexpander Expr.constU]
def delabConstU : Unexpander
| `($(_) $n:num $_) => `(>>> $n <<<)
| _ => pure


@[app_unexpander Expr.fmtStr]
def delabFmtStr : Unexpander
| `($(_) $_ $_ $_) => sorry
| _ => pure

declare_syntax_cat pp_fn_binders
declare_syntax_cat pp_fn_generics
declare_syntax_cat pp_kinds

syntax ident : pp_kinds
syntax "<"pp_kinds,*">" : pp_fn_generics
syntax "(" pp_expr,* ")" : pp_fn_binders

syntax "λ#" num pp_fn_binders : pp_expr -- lambda funcref
syntax ident pp_fn_generics pp_fn_binders : pp_expr -- decl and trait funcrefs

@[app_unexpander Expr.fn]
def delabFn : Unexpander
| `($(_) $argTps $outTp $funcref) =>
  match funcref with
  | `(``FuncRef.lambda $ref) => `(>>> λ#3 () <<<)
  | `(``FuncRef.decl $name $kinds $generics) => `(>>>  <<<)
  | `(``FuncRef.trait $selfTp $traitName $kinds $generics $fnName $fnKinds $fnGenerics) => sorry
  | _ => pure
| _ => pure

nr_def simple_muts<>(x : Field) -> Field {
  #fAdd(x, 1 : Field) : Field
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

@[app_unexpander Expr.var]
def delabVar : Unexpander
| `($(_) $var) => sorry
| _ => pure

@[app_unexpander Expr.letIn]
def delabLetIn : Unexpander
| `($(_) $a fun $v => $body) => sorry
  -- let bIdent := mkIdent `XYZW
  -- let binding := mkIdent v.raw.getId
  -- `(letin| let $binding = $a;)
| _ => pure

@[app_unexpander Expr.call]
def delabCall : Unexpander
| `($(_) $_ $_) => sorry -- TODO: This one will be tricky I think
| _ => pure

-- TODO: Will likely need this
-- @[app_unexpander Lampe.FunctionDecl.call]
-- def delabFunctionDeclCall : Unexpander
-- | `($(_) $decl $gens $args) => do
--   let x := mkIdent decl.raw.getId
--   `($x <$gens> ($args))
-- | _ => pure

@[app_unexpander Expr.callBuiltin]
def delabCallBuiltin : Unexpander
| `($(_) $_ $_ $builtin $args) => sorry
| _ => pure

@[app_unexpander Expr.ite]
def delabITE : Unexpander
| `($(_) $cond $ifTrue $ifFalse) => sorry
| _ => pure

@[app_unexpander Expr.skip]
def delabSkip : Unexpander
| `($(_)) => sorry

@[app_unexpander Expr.loop]
def delabLoop : Unexpander
| `($(_) $low $high (fun $var => $body)) => sorry
| _ => pure

@[app_unexpander Lampe.Expr.lam]
def delabLam : Unexpander
| `($(_) $_ $_ fun $args => $body) => sorry
| _ => pure

section STHoare

declare_syntax_cat slp_cond
declare_syntax_cat sthoare

syntax "⦃" term "⦄" : slp_cond
syntax slp_cond ppLine ppLine ppGroup(pp_expr) ppLine ppLine slp_cond : term

@[app_unexpander STHoare]
def delabSTHoare : Unexpander
| `($(_) $_ $_ $P $C $Q) =>
  `(⦃$P⦄ $C ⦃$Q⦄)
| _ => pure

end STHoare


declare_syntax_cat lang
syntax num   : lang
syntax ident : lang
syntax "let " ident " := " lang " in " lang: lang
syntax "[Lang| " lang "]" : term

inductive LangExpr
  | numConst : Nat → LangExpr
  | ident    : String → LangExpr
  | letE     : String → LangExpr → LangExpr → LangExpr

macro_rules
  | `([Lang| $x:num ]) => `(LangExpr.numConst $x)
  | `([Lang| $x:ident]) => `(LangExpr.ident $(Lean.quote (toString x.getId)))
  | `([Lang| let $x:ident := $v:lang in $b:lang]) => `(LangExpr.letE $(Lean.quote (toString x.getId)) [Lang| $v] [Lang| $b])

instance : Coe NumLit (TSyntax `lang) where
  coe s := ⟨s.raw⟩

instance : Coe Lean.Ident (TSyntax `lang) where
  coe s := ⟨s.raw⟩

-- LangExpr.letE "foo" (LangExpr.numConst 12)
--   (LangExpr.letE "bar" (LangExpr.ident "foo") (LangExpr.ident "foo")) : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

@[app_unexpander LangExpr.numConst]
def unexpandNumConst : Unexpander
  | `($_numConst $x:num) => `([Lang| $x])
  | _ => throw ()

@[app_unexpander LangExpr.ident]
def unexpandIdent : Unexpander
  | `($_ident $x:str) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| $name])
  | _ => throw ()

@[app_unexpander LangExpr.letE]
def unexpandLet : Unexpander
  | `($_letE $x:str [Lang| $v:lang] [Lang| $b:lang]) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| let $name := $v in $b])
  | _ => throw ()

-- [Lang| let foo := 12 in foo] : LangExpr
#check [Lang|
  let foo := 12 in foo
]

-- [Lang| let foo := 12 in let bar := foo in foo] : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]
