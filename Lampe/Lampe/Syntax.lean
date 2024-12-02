import Mathlib
import Lean
import Lampe.Ast
import Lampe.Builtin
import Qq

namespace Lampe

open Lean Elab Meta Qq

declare_syntax_cat nr_ident
declare_syntax_cat nr_type
declare_syntax_cat nr_expr
declare_syntax_cat nr_block_contents
declare_syntax_cat nr_param_decl

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
| "add"            => ``(Builtin.fAdd)
| "sub"            => ``(Builtin.sub)
| "mul"            => ``(Builtin.mul)
| "div"            => ``(Builtin.div)
| "eq"             => ``(Builtin.fEq)
| "assert"         => ``(Builtin.assert)
| "not"            => ``(Builtin.not)
| "lt"             => ``(Builtin.lt)
| "index"          => ``(Builtin.index)
| "cast"           => ``(Builtin.cast)
| "modulus_num_bits" => ``(Builtin.fModNumBits)
| "to_le_bytes"      => ``(Builtin.toLeBytes)
| "fresh"          => ``(Builtin.fresh)
| "slice_len"      => ``(Builtin.sliceLen)
| "slice_push_back" => ``(Builtin.slicePushBack)
| "slice_push_front" => ``(Builtin.slicePushFront)
| "slice_pop_back" => ``(Builtin.slicePopBack)
| "slice_index" => ``(Builtin.sliceIndex)
| "slice_pop_front" => ``(Builtin.slicePopFront)
| "slice_insert"   => ``(Builtin.sliceInsert)
| "ref"   => ``(Builtin.ref)
| "read_ref"   => ``(Builtin.readRef)
| "write_ref"   => ``(Builtin.writeRef)
| _ => throwError "Unknown builtin {i}"

syntax ident ":" nr_type : nr_param_decl

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
syntax ident "=" nr_expr : nr_expr
syntax nr_expr "." num : nr_expr
syntax "if" nr_expr nr_expr ("else" nr_expr)? : nr_expr
syntax "for" ident "in" nr_expr ".." nr_expr nr_expr : nr_expr
syntax "(" nr_expr ")" : nr_expr
syntax "*(" nr_expr ")" : nr_expr
syntax "|" nr_param_decl,* "|" "->" nr_type nr_expr : nr_expr
syntax "^" nr_ident "(" nr_expr,* ")" ":" nr_type : nr_expr

syntax nr_fn_decl := nr_ident "<" ident,* ">" "(" nr_param_decl,* ")" "->" nr_type "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}"

def Expr.letMutIn (definition : Expr rep tp) (body : rep tp.ref → Expr rep tp'): Expr rep tp' :=
  let refDef := Expr.letIn definition fun v => Expr.call h![] _ (tp.ref) (.builtin .ref) h![v]
  Expr.letIn refDef body

def Expr.ref (val : rep tp): Expr rep tp.ref :=
  Expr.call h![] _ tp.ref (.builtin .ref) h![val]

def Expr.readRef (ref : rep tp.ref): Expr rep tp :=
  Expr.call h![] _ tp (.builtin .readRef) h![ref]

def Expr.writeRef (ref : rep tp.ref) (val : rep tp): Expr rep .unit :=
  Expr.call h![] _ .unit (.builtin .writeRef) h![ref, val]

structure DesugarState where
  autoDeref : Name → Bool
  nextFresh : Nat

class MonadSyntax (m: Type → Type) extends Monad m, MonadQuotation m, MonadExceptOf Exception m, MonadError m, MonadStateOf DesugarState m

instance [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m]: MonadSyntax (StateT DesugarState m) where
  add x y := StateT.lift $ AddErrorMessageContext.add x y

def isAutoDeref [MonadSyntax m] (i : Name): m Bool := do
  let s ← get
  pure $ s.autoDeref i

def registerAutoDeref [MonadSyntax m] (i : Name): m Unit := do
  modify fun s => { s with autoDeref := fun id => if id = i then true else s.autoDeref id }

def MonadSyntax.run [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (a : StateT DesugarState m α): m α :=
  StateT.run' a (DesugarState.mk (fun _ => false) 0)

def getName [MonadSyntax m] : Option Lean.Ident → m Lean.Ident
| none =>
  modifyGet fun s => (mkIdent (Name.mkSimple s!"#v_{s.nextFresh}"), { s with nextFresh := s.nextFresh + 1 })
| some n => pure n

def wrapSimple [MonadSyntax m] (e : TSyntax `term) (ident : Option Lean.Ident) (k : TSyntax `term → m (TSyntax `term)) : m (TSyntax `term) := do
  let ident ← getName ident
  let rest ← k ident
  `(Lampe.Expr.letIn $e fun $ident => $rest)

mutual

partial def mkBlock [MonadSyntax m] (items: List (TSyntax `nr_expr)) (k : TSyntax `term → m (TSyntax `term)): m (TSyntax `term) := match items with
| h :: n :: rest => match h with
  | `(nr_expr | let $v = $e ) => do
    mkExpr e (some v) fun _ => mkBlock (n::rest) k
  | `(nr_expr | let mut $v = $e) => do
    mkExpr e none fun eVal => do
      registerAutoDeref v.getId
      let body ← mkBlock (n::rest) k
      `(Lampe.Expr.letIn (Expr.ref $eVal) fun $v => $body)
  | e => do
  mkExpr e none fun _ => mkBlock (n::rest) k
| [e] => match e with
  | `(nr_expr | let $_ = $e)
  | `(nr_expr | let mut $_ = $e)
  | `(nr_expr | $e) => mkExpr e none k
| _ => do wrapSimple (←`(Lampe.Expr.skip)) none k

partial def mkArgs [MonadSyntax m] (args : List (TSyntax `nr_expr)) (k : List (TSyntax `term) → m (TSyntax `term)) : m (TSyntax `term) := match args with
| [] => k []
| h :: t =>
  mkExpr h none fun h => do
    mkArgs t fun t => k (h :: t)

partial def mkExpr [MonadSyntax m] (e : TSyntax `nr_expr) (vname : Option Lean.Ident) (k : TSyntax `term → m (TSyntax `term)): m (TSyntax `term) := match e with
| `(nr_expr|$n:num : $tp) => do wrapSimple (←``(Lampe.Expr.lit $(←mkNrType tp) $n)) vname k
| `(nr_expr| true) => do wrapSimple (←``(Lampe.Expr.lit Tp.bool 1)) vname k
| `(nr_expr| false) => do wrapSimple (←``(Lampe.Expr.lit Tp.bool 0)) vname k
| `(nr_expr| { $exprs;* }) => mkBlock exprs.getElems.toList k
| `(nr_expr| $i:ident) => do
  if ←isAutoDeref i.getId then wrapSimple (← ``(Lampe.Expr.readRef $i)) vname k else match vname with
  | none => k i
  | some _ => wrapSimple (←``(Lampe.Expr.var $i)) vname k
| `(nr_expr| # $i:ident ($args,*): $tp) => do
  mkArgs args.getElems.toList fun argVals => do
    wrapSimple (←`(Lampe.Expr.call h![] _ $(←mkNrType tp) (.builtin $(←mkBuiltin i.getId.toString)) $(←mkHListLit argVals))) vname k
| `(nr_expr| for $i in $lo .. $hi $body) => do
  mkExpr lo none fun lo =>
  mkExpr hi none fun hi => do
    let body ← mkExpr body none (fun x => ``(Lampe.Expr.var $x))
    wrapSimple (←`(Lampe.Expr.loop $lo $hi fun $i => $body)) vname k
| `(nr_expr| $v:ident = $e) => do
  mkExpr e none fun eVal => do
    wrapSimple (←`(Lampe.Expr.writeRef $v $eVal)) vname k
| `(nr_expr| ( $e )) => mkExpr e vname k
| `(nr_expr| if $cond $mainBody else $elseBody) => do
    mkExpr cond none fun cond => do
      let mainBody ← mkExpr mainBody none fun x => ``(Lampe.Expr.var $x)
      let elseBody ← mkExpr elseBody none fun x => ``(Lampe.Expr.var $x)
      wrapSimple (←`(Lampe.Expr.ite $cond $mainBody $elseBody)) vname k
| `(nr_expr| if $cond $mainBody) => do
    mkExpr cond none fun cond => do
      let mainBody ← mkExpr mainBody none fun x => ``(Lampe.Expr.var $x)
      wrapSimple (←`(Lampe.Expr.ite $cond $mainBody (Lampe.Expr.skip))) vname k
| `(nr_expr| | $params,* | -> $outTp $lambdaBody) => do
  let outTp ← mkNrType outTp
  let argTps ← mkListLit (← params.getElems.toList.mapM fun param => match param with
    | `(nr_param_decl|$_:ident : $tp) => mkNrType tp
    | _ => throwUnsupportedSyntax)
  let args ← mkHListLit (← params.getElems.toList.mapM fun param => match param with
    | `(nr_param_decl|$i:ident : $_) => `($i)
    | _ => throwUnsupportedSyntax)
  let body ← mkExpr lambdaBody none fun x => ``(Lampe.Expr.var $x)
  wrapSimple (←`(Lampe.Expr.lambda $argTps $outTp (fun $args => $body))) vname k
| `(nr_expr| ^ $i:ident ($args,*): $tp) => do
  mkArgs args.getElems.toList fun argVals => do
    wrapSimple (←`(Lampe.Expr.call h![] _ $(←mkNrType tp) (.lambda $i) $(←mkHListLit argVals))) vname k
| _ => throwUnsupportedSyntax

end

syntax ident ":" nr_type : nr_param_decl
syntax nr_trait_impl := "<" ident,* ">" nr_ident "<" ident,* ">" "for" nr_type "{" sepBy(nr_fn_decl, ";", ";", allowTrailingSep) "}"

def mkFnDecl [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (syn : Syntax) :  m (String × TSyntax `term) := match syn with
| `(nr_fn_decl| $name < $generics,* > ( $params,* ) -> $outTp { $bExprs;* }) => do
  let name ← mkNrIdent name
  let generics := generics.getElems.toList.map fun i => (mkIdent $ Name.mkSimple i.getId.toString)
  let genericsDecl ← mkListLit (← generics.mapM fun _ => `(Kind.type))
  let params : List (TSyntax `term × TSyntax `term) ← params.getElems.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) => do pure (i, ←mkNrType tp)
    | _ => throwUnsupportedSyntax
  let body ← MonadSyntax.run ((mkBlock bExprs.getElems.toList) (fun x => `(Expr.var $x)))
  let lambdaDecl ← `(fun rep generics => match generics with
    | $(←mkHListLit generics) => ⟨$(←mkListLit $ params.map Prod.snd), $(←mkNrType outTp), fun args => match args with
        | $(←mkHListLit $ params.map Prod.fst) => $body⟩)
  let syn : TSyntax `term ← `(FunctionDecl.mk $(Syntax.mkStrLit name) $ Function.mk $genericsDecl $lambdaDecl)
  pure (name, syn)
| _ => throwUnsupportedSyntax

def mkTraitImpl [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : Syntax → m (String × TSyntax `term)
| `(nr_trait_impl| < $generics,* > $traitName < $traitGenerics,* > for $targetType { $fns;* }) => do
  let implGenericKinds ← mkListLit (← generics.getElems.toList.mapM fun _ => `(Kind.type))
  let traitGenericKinds ← mkListLit (← traitGenerics.getElems.toList.mapM fun _ => `(Kind.type))
  let generics := generics.getElems.toList.map fun tyVar => (mkIdent $ Name.mkSimple tyVar.getId.toString)

  let traitName ← mkNrIdent traitName
  let fnDecls ← mkListLit (← fns.getElems.toList.mapM fun fn => do
    let fnDecl ← mkFnDecl fn
    `(Prod.mk $(Syntax.mkStrLit fnDecl.fst) $(fnDecl.snd)))
  let targetType ← mkNrType targetType
  let syn : TSyntax `term ← `(TraitImpl.mk
    (traitGenericKinds := $traitGenericKinds)
    (implGenericKinds := $implGenericKinds)
    (traitGenerics := fun _ => [])
    (constraints := fun _ => [])
    (self := fun generics => match generics with | $(←mkHListLit generics) => $targetType)
    (impl := $fnDecls))
  pure (traitName, syn)
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do
  let term ← MonadSyntax.run $ mkExpr expr none fun x => ``(Expr.var $x)
  Elab.Term.elabTerm term.raw none
elab "nrfn![" "fn" fn:nr_fn_decl "]" : term => do
  let stx ← `($((←mkFnDecl fn).2).fn)
  Elab.Term.elabTerm stx none

elab "nr_def" decl:nr_fn_decl : command => do
  let (name, decl) ← mkFnDecl decl
  let decl ← `(def $(mkIdent $ Name.mkSimple name) : Lampe.FunctionDecl := $decl)
  Elab.Command.elabCommand decl

elab "nr_trait_impl" impl:nr_trait_impl : command => do
  let (name, impl) ← mkTraitImpl impl
  let leanDefn ← `(def $(mkIdent $ Name.mkSimple name) : Lampe.TraitImpl := $impl)
  Elab.Command.elabCommand leanDefn

end Lampe
