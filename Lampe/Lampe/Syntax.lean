import Lean
import Qq

import Lampe.Ast
import Lampe.Builtin.Arith
import Lampe.Builtin.Array
import Lampe.Builtin.BigInt
import Lampe.Builtin.Bit
import Lampe.Builtin.Cmp
import Lampe.Builtin.Field
import Lampe.Builtin.Memory
import Lampe.Builtin.Slice
import Lampe.Builtin.Str
import Lampe.Builtin.Struct
import Lampe.Builtin.Lens

namespace Lampe

open Lean Elab Meta Qq

declare_syntax_cat nr_ident
declare_syntax_cat nr_type
declare_syntax_cat nr_expr
declare_syntax_cat nr_block_contents
declare_syntax_cat nr_param_decl

syntax ident : nr_ident
syntax ident "::" nr_ident : nr_ident

syntax ident : nr_type
syntax "${" term "}" : nr_type
syntax nr_ident "<" nr_type,* ">" : nr_type -- Struct
syntax "[" nr_type "]" : nr_type -- Slice
syntax "[" nr_type ";" num "]" : nr_type -- Array
syntax "`(" nr_type,* ")" : nr_type -- Tuple
syntax "&" nr_type : nr_type -- Reference
syntax "λ(" nr_type,* ")" "→" nr_type : nr_type -- Function

syntax ident ":" nr_type : nr_param_decl

syntax num ":" nr_type : nr_expr -- Numeric literal
syntax "#unit" : nr_expr -- Unit literal
syntax ident : nr_expr
syntax "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}" : nr_expr
syntax "${" term "}" : nr_expr
syntax "$" ident : nr_expr
syntax "let" ident "=" nr_expr : nr_expr
syntax "let" "mut" ident "=" nr_expr : nr_expr
syntax nr_expr "=" nr_expr : nr_expr -- Assignment
syntax "if" nr_expr nr_expr ("else" nr_expr)? : nr_expr -- If then else
syntax "for" ident "in" nr_expr ".." nr_expr nr_expr : nr_expr -- For loop
syntax "(" nr_expr ")" : nr_expr
syntax "|" nr_param_decl,* "|" "->" nr_type nr_expr : nr_expr -- Lambda
syntax "*(" nr_expr ")" : nr_expr -- Deref

syntax nr_ident "<" nr_type,* ">" "{" nr_expr,* "}" : nr_expr -- Struct constructor
syntax "`(" nr_expr,* ")" : nr_expr -- Tuple constructor
syntax "[" nr_expr ";" num "]" : nr_expr -- Repeated array constructor
syntax "&[" nr_expr ";" num "]" : nr_expr -- Repeated slice constructor
syntax "[" nr_expr,* "]" : nr_expr -- Array constructor
syntax "&[" nr_expr,* "]" : nr_expr -- Slice constructor

syntax "(" nr_expr "as" nr_ident "<" nr_type,* ">" ")" "." ident : nr_expr -- Struct access
syntax nr_expr "." num : nr_expr -- Tuple access
syntax nr_expr "[" nr_expr "]" : nr_expr -- Array access
syntax nr_expr "[[" nr_expr "]]" : nr_expr -- Slice access

syntax "#" nr_ident "(" nr_expr,* ")" ":" nr_type : nr_expr -- Builtin call

syntax "(" nr_type "as" nr_ident "<" nr_type,* ">" ")" "::" nr_ident "<" nr_type,* ">" "as" nr_type : nr_expr -- Trait func ident
syntax "@" nr_ident "<" nr_type,* ">" "as" nr_type : nr_expr -- Decl func ident

syntax nr_expr "(" nr_expr,* ")" : nr_expr -- Universal call

syntax nr_fn_decl := nr_ident "<" ident,* ">" "(" nr_param_decl,* ")" "->" nr_type "{" sepBy(nr_expr, ";", ";", allowTrailingSep) "}"
syntax nr_trait_constraint := nr_type ":" nr_ident "<" nr_type,* ">"
syntax nr_trait_fn_def := "fn" nr_fn_decl
syntax nr_trait_impl := "<" ident,* ">" nr_ident "<" nr_type,* ">" "for" nr_type "where" sepBy(nr_trait_constraint, ",", ",", allowTrailingSep)
  "{" sepBy(nr_trait_fn_def, ";", ";", allowTrailingSep) "}"
syntax nr_struct_def := "<" ident,* ">" "{" sepBy(nr_param_decl, ",", ",", allowTrailingSep) "}"

partial def mkNrIdent [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : Syntax → m String
| `(nr_ident|$i:ident) => pure i.getId.toString
| `(nr_ident|$i:ident :: $j:nr_ident) => do pure s!"{i.getId}::{←mkNrIdent j}"
| i => throwError "Unexpected ident {i}"

def mkFieldAccessorIdent (structName : String) (fieldName : String) : Lean.Ident :=
  mkIdent $ Name.mkSimple $ "field" ++ "#" ++ structName ++ "#" ++ fieldName

def mkStructDefIdent (structName : String) : Lean.Ident :=
   mkIdent $ Name.mkSimple $ "struct" ++ "#" ++ structName

def mkFunctionDefIdent (fnName : String) : Lean.Ident :=
  mkIdent $ Name.mkSimple fnName

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
| `(nr_type| & $tp) => do `(Tp.ref $(←mkNrType tp))
| `(nr_type| $structName:nr_ident < $generics,* >) => do
  let generics ← generics.getElems.toList.mapM mkNrType
  `(Struct.tp $(mkStructDefIdent (←mkNrIdent structName)) $(←mkHListLit generics))
| `(nr_type| ${ $i }) => pure i
| `(nr_type| [ $tp ]) => do `(Tp.slice $(←mkNrType tp))
| `(nr_type| [ $tp ; $len:num ]) => do `(Tp.array $(←mkNrType tp) $len)
| `(nr_type| `($tps,* )) => do
  let tps ← tps.getElems.toList.mapM mkNrType
  `(Tp.tuple none $(←mkListLit tps))
| `(nr_type| λ( $paramTps,* ) → $outTp) => do
  let paramTps ← (mkListLit (←paramTps.getElems.toList.mapM mkNrType))
  let outTp ← mkNrType outTp
  `(Tp.fn $paramTps $outTp)
| _ => throwUnsupportedSyntax

def mkBuiltin [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (i : String) : m (TSyntax `term) :=
   `($(mkIdent $ (Name.mkSimple "Builtin") ++ (Name.mkSimple i)))

def mkTupleMember [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (i : Nat) : m (TSyntax `term) := match i with
| .zero => `(Builtin.Member.head)
| .succ n' => do `(Builtin.Member.tail $(←mkTupleMember n'))

def mkStructMember [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m]
    (structName : TSyntax `nr_ident) (gs : List $ TSyntax `nr_type) (field : TSyntax `ident) :
    m (TSyntax `term) := do
  let gs ← mkHListLit (←gs.mapM fun gVal => mkNrType gVal)
  let accessor := mkFieldAccessorIdent (←mkNrIdent structName) (field.getId.toString)
  `($accessor $gs)

@[reducible]
def Expr.ref (val : rep tp) : Expr rep tp.ref :=
  Expr.callBuiltin _ tp.ref .ref h![val]

@[reducible]
def Expr.readRef (ref : rep tp.ref) : Expr rep tp :=
  Expr.callBuiltin _ tp .readRef h![ref]

@[reducible]
def Expr.writeRef (ref : rep tp.ref) (val : rep tp) : Expr rep .unit :=
  Expr.callBuiltin _ .unit .writeRef h![ref, val]

@[reducible]
def Expr.mkSlice (n : Nat) (vals : HList rep (List.replicate n tp)) : Expr rep (.slice tp) :=
  Expr.callBuiltin _ (.slice tp) (.mkSlice n) vals

@[reducible]
def Expr.mkArray (n : Nat) (vals : HList rep (List.replicate n tp)) : Expr rep (.array tp n) :=
  Expr.callBuiltin _ (.array tp n) (.mkArray n) vals

@[reducible]
def Expr.mkTuple (name : Option String) (args : HList rep tps) : Expr rep (.tuple name tps) :=
  Expr.callBuiltin tps (.tuple name tps) ( .mkTuple) args

@[reducible]
def Expr.modifyLens (r : rep $ .ref tp₁) (v : rep tp₂) (lens : Lens rep tp₁ tp₂) : Expr rep .unit :=
  Expr.callBuiltin [.ref tp₁, tp₂] .unit (.modifyLens lens) h![r, v]

@[reducible]
def Expr.getLens (v : rep tp₁) (lens : Lens rep tp₁ tp₂) : Expr rep tp₂ :=
  Expr.callBuiltin _ tp₂ (.getLens lens) h![v]

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
  StateT.run' a ⟨(fun _ => false), 0⟩

def getName [MonadSyntax m] : Option Lean.Ident → m Lean.Ident
| none =>
  modifyGet fun s => (mkIdent (Name.mkSimple s!"#v_{s.nextFresh}"), { s with nextFresh := s.nextFresh + 1 })
| some n => pure n

def wrapSimple [MonadSyntax m] (e : TSyntax `term) (ident : Option Lean.Ident) (k : TSyntax `term → m (TSyntax `term)) : m (TSyntax `term) := do
  let ident ← getName ident
  let rest ← k ident
  `(Lampe.Expr.letIn $e fun $ident => $rest)

/--
Represents a list of arguments and the corresponding identifiers.
-/
structure ArgSet where
  args : List $ TSyntax `nr_expr
  idents : List Lean.Ident
  lastId : Nat

def ArgSet.empty : ArgSet := ⟨[], [], 0⟩

instance : Inhabited ArgSet where
  default := ArgSet.empty

/--
Returns a new `ArgSet` with the given expression `expr` associated with a unique identifier.
Returns the corresponding identifier along with the new `ArgSet`.
-/
def ArgSet.next (a : ArgSet) (expr : TSyntax `nr_expr) : (Lean.Ident × ArgSet) :=
  let ident := mkIdent $ Name.mkSimple $ "#arg_" ++ (toString a.lastId)
  (ident, ⟨expr :: a.args, ident :: a.idents, a.lastId + 1⟩)

/--
Wraps the given expression `expr` with the identifiers in the `ArgSet`.
If `argVals` is empty, the expression is returned as is.
Otherwise, the expression is wrapped in a lambda that matches the identifiers in the `ArgSet` with the arguments.
-/
def ArgSet.wrap [MonadSyntax m] (a : ArgSet) (argVals : List $ TSyntax `term) (expr : TSyntax `term) :
    m $ TSyntax `term := do
  if argVals.isEmpty then
    `($expr)
  else
    `((fun args => match args with | $(←mkHListLit a.idents) => $expr) $(←mkHListLit argVals))

/--
Returns a term which constructs a `Lens` object that corresponds to the lens expression or lval `expr`.
This `Lens` object, denoted as `l`, can be used in two ways:
1. If `expr` is a lens expression, the builtin `getLens l` can be called with `getLeftmostExpr expr` for lens access.
2. It `expr` is an lval, the builtin `modifyLens l` can be combined with `getLValRef expr` along with a rhs for lens modification.
-/
partial def mkLens [MonadSyntax m] (expr : TSyntax `nr_expr) (a : ArgSet) : m $ (TSyntax `term) × ArgSet := match expr with
| `(nr_expr| ( $structExpr:nr_expr as $structName  < $structGens,* > ) . $fieldName) => do
  let mem ← mkStructMember structName structGens.getElems.toList fieldName
  let (lhsLens, a') ← mkLens structExpr a
  let lens' ← `(Lens.cons $lhsLens (Access.tuple $mem))
  pure (lens', a')
| `(nr_expr| $tupleExpr:nr_expr . $idx) => do
  let mem ← mkTupleMember idx.getNat
  let (lhsLens, a') ← mkLens tupleExpr a
  let lens' ← `(Lens.cons $lhsLens (Access.tuple $mem))
  pure (lens', a')
| `(nr_expr| $arrayExpr:nr_expr [ $idxExpr:nr_expr ]) => do
  let (idx, a') := a.next idxExpr
  let (lhsLens, a'') ← mkLens arrayExpr a'
  let lens' ← `(Lens.cons $lhsLens (Access.array $idx))
  pure (lens', a'')
| `(nr_expr| $sliceExpr:nr_expr [[ $idxExpr:nr_expr ]]) => do
  let (idx, a') := a.next idxExpr
  let (lhsLens, a'') ← mkLens sliceExpr a'
  let lens' ← `(Lens.cons $lhsLens (Access.slice $idx))
  pure (lens', a'')
| `(nr_expr| $_:nr_expr) => do
  let nil ← `(Lens.nil)
  pure (nil, a)

/--
Returns the leftmost expression of a lens access. For example, in `foo().b[3]`, this is `foo()`.
-/
partial def getLeftmostExpr (expr : TSyntax `nr_expr) : (TSyntax `nr_expr) := match expr with
| `(nr_expr| ( $structExpr:nr_expr as $_  < $_,* > ) . $_) => getLeftmostExpr structExpr
| `(nr_expr| $tupleExpr:nr_expr . $_) => getLeftmostExpr tupleExpr
| `(nr_expr| $arrayExpr:nr_expr [ $_ ]) => getLeftmostExpr arrayExpr
| `(nr_expr| $sliceExpr:nr_expr [[ $_ ]]) => getLeftmostExpr sliceExpr
| `(nr_expr| $e:nr_expr) => e

/--
Represents the "source" of an lval, i.e., the value `modifyLens` should be called with.
-/
inductive LValRef where
/-- The source is a mutable let binding. -/
| ident (id : TSyntax `ident)
/-- The source is the result of an expression which returns a reference. -/
| expr (expr : TSyntax `nr_expr)
/-- Malformed lval. -/
| none

instance : Inhabited LValRef := ⟨LValRef.none⟩

/--
We consider two types of lvals:
1. Whose "sources" are mutable let bindings, e.g., in `a.b[3]`, the "source" is `a` where `a` is a mutable let binding.
We already represent `a` as a reference. Accordingly, the `modifyLens` builtin can be called directly with `a`.
2. Whose "sources" are expressions that return a reference, e.g., in `*e.b[3]`, the "source" is `*e` where `e` is an expression that returns a reference.
We need to evaluate `e`, and `modifyLens` needs to be called with the result of `e` (which is a reference).

These two cases can be distinguished by the existence of the `*` operator.
-/
partial def getLValRef (lval : TSyntax `nr_expr) : LValRef := match lval with
| `(nr_expr| ( $structExpr:nr_expr as $_  < $_,* > ) . $_) => getLValRef structExpr
| `(nr_expr| $tupleExpr:nr_expr . $_) => getLValRef tupleExpr
| `(nr_expr| $arrayExpr:nr_expr [ $_ ]) => getLValRef arrayExpr
| `(nr_expr| $sliceExpr:nr_expr [[ $_ ]]) => getLValRef sliceExpr
| `(nr_expr| *( $refExpr:nr_expr )) => LValRef.expr refExpr
| `(nr_expr| $i:ident) => LValRef.ident i
| `(nr_expr| $_:nr_expr) => LValRef.none

/--
If `ty` is the syntax object corresponding to the function type, this extracts and returns the parameter types and the return type from the syntax object `ty`.
-/
partial def getFuncSignature [MonadSyntax m] (ty : TSyntax `nr_type) : m (List (TSyntax `term) × TSyntax `term) := match ty with
| `(nr_type| λ( $paramTps,* ) → $outTp) => do
  let paramTps ← paramTps.getElems.toList.mapM fun p => mkNrType p
  let outTp ← mkNrType outTp
  pure (paramTps, outTp)
| _ => throwUnsupportedSyntax

mutual

partial def mkBlock [MonadSyntax m] (items: List (TSyntax `nr_expr)) (k : TSyntax `term → m (TSyntax `term)): m (TSyntax `term) := match items with
| h :: n :: rest => match h with
  | `(nr_expr | let $v = $e ) => do
    mkExpr e (some v) fun _ => mkBlock (n :: rest) k
  | `(nr_expr | let mut $v = $e) => do
    mkExpr e none fun eVal => do
      registerAutoDeref v.getId
      let body ← mkBlock (n :: rest) k
      `(Lampe.Expr.letIn (Expr.ref $eVal) fun $v => $body)
  | e => do
  mkExpr e none fun _ => mkBlock (n :: rest) k
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

partial def mkExpr [MonadSyntax m] (e : TSyntax `nr_expr) (vname : Option Lean.Ident) (k : TSyntax `term → m (TSyntax `term)) : m (TSyntax `term) := match e with
| `(nr_expr| $n:num : $tp) => do wrapSimple (←`(Expr.lit $(←mkNrType tp) $n)) vname k
| `(nr_expr| true) => do wrapSimple (←`(Expr.lit Tp.bool 1)) vname k
| `(nr_expr| false) => do wrapSimple (←`(Expr.lit Tp.bool 0)) vname k
| `(nr_expr| #unit) => do wrapSimple (←`(Expr.lit Tp.unit 0)) vname k
| `(nr_expr| { $exprs;* }) => mkBlock exprs.getElems.toList k
| `(nr_expr| $i:ident) => do
  if ←isAutoDeref i.getId then
    wrapSimple (← `(Expr.readRef $i)) vname k
  else match vname with
    | none => k i
    | some _ => wrapSimple (←`(Expr.var $i)) vname k
| `(nr_expr| # $i:ident ($args,*): $tp) => do
  mkArgs args.getElems.toList fun argVals => do
    wrapSimple (←`(Expr.callBuiltin _ $(←mkNrType tp) $(←mkBuiltin i.getId.toString) $(←mkHListLit argVals))) vname k
| `(nr_expr| *( $expr:nr_expr )) => do
  mkExpr expr none fun v => do
    wrapSimple (←`(Expr.readRef $v)) vname k
| `(nr_expr| for $i in $lo .. $hi $body) => do
  mkExpr lo none fun lo =>
  mkExpr hi none fun hi => do
    let body ← mkExpr body none (fun x => `(Expr.var $x))
    wrapSimple (←`(Expr.loop $lo $hi fun $i => $body)) vname k
| `(nr_expr| $lhs:nr_expr = $rhs:nr_expr) => do
  let (lens, args) ← mkLens lhs ArgSet.empty
  mkExpr rhs none fun rhs => do
    mkArgs args.args fun vals => do
      match (getLValRef lhs) with
      | .ident r => wrapSimple (←`(Expr.modifyLens $r $rhs $(←args.wrap vals lens))) vname k
      | .expr expr => mkExpr expr none fun r => do
        wrapSimple (←`(Expr.modifyLens $r $rhs $(←args.wrap vals lens))) vname k
      | .none => throwUnsupportedSyntax
| `(nr_expr| ( $e )) => mkExpr e vname k
| `(nr_expr| if $cond $mainBody else $elseBody) => do
  mkExpr cond none fun cond => do
    let mainBody ← mkExpr mainBody none fun x => `(Expr.var $x)
    let elseBody ← mkExpr elseBody none fun x => `(Expr.var $x)
    wrapSimple (←`(Expr.ite $cond $mainBody $elseBody)) vname k
| `(nr_expr| if $cond $mainBody) => do
  mkExpr cond none fun cond => do
    let mainBody ← mkExpr mainBody none fun x => `(Expr.var $x)
    wrapSimple (←`(Expr.ite $cond $mainBody (Expr.skip))) vname k
| `(nr_expr| &[ $args,* ]) => do
  let args := args.getElems.toList
  let len := args.length
  mkArgs args fun argVals => do
    wrapSimple (←`(Expr.mkSlice $(Syntax.mkNumLit $ toString len) $(←mkHListLit argVals))) vname k
| `(nr_expr| [ $args,* ]) => do
  let args := args.getElems.toList
  let len := args.length
  mkArgs args fun argVals => do
    wrapSimple (←`(Expr.mkArray $(Syntax.mkNumLit $ toString len) $(←mkHListLit argVals))) vname k
| `(nr_expr| [ $arg ; $rep:num ]) => do
  mkExpr arg none fun argVal => do
    let argVals := List.replicate rep.getNat argVal
    wrapSimple (←`(Expr.mkArray $rep $(←mkHListLit argVals))) vname k
| `(nr_expr| &[ $arg ; $rep:num ]) => do
  mkExpr arg none fun argVal => do
    let argVals := List.replicate rep.getNat argVal
    wrapSimple (←`(Expr.mkSlice $rep $(←mkHListLit argVals))) vname k
| `(nr_expr| | $params,* | -> $outTp $lambdaBody) => do
  let outTp ← mkNrType outTp
  let argTps ← mkListLit (← params.getElems.toList.mapM fun param => match param with
    | `(nr_param_decl|$_:ident : $tp) => mkNrType tp
    | _ => throwUnsupportedSyntax)
  let args ← mkHListLit (← params.getElems.toList.mapM fun param => match param with
    | `(nr_param_decl|$i:ident : $_) => `($i)
    | _ => throwUnsupportedSyntax)
  let body ← mkExpr lambdaBody none fun x => `(Expr.var $x)
  wrapSimple (←`(Expr.lam $argTps $outTp (fun $args => $body))) vname k
| `(nr_expr| $structName:nr_ident < $structGenVals,* > { $args,* }) => do
   let structName ← mkNrIdent structName
   let fieldTps ← `(Struct.fieldTypes $(mkStructDefIdent structName) $(←mkHListLit (←structGenVals.getElems.toList.mapM fun gVal => mkNrType gVal)))
   mkArgs args.getElems.toList fun argVals => do
     wrapSimple (←`(Expr.mkTuple (tps := $fieldTps) (some $(Syntax.mkStrLit $ structName)) $(←mkHListLit argVals))) vname k
| `(nr_expr| `( $args,* )) => do
  mkArgs args.getElems.toList fun argVals => do
    wrapSimple (←`(Expr.mkTuple none $(←mkHListLit argVals))) vname k
| `(nr_expr| @ $fnName:nr_ident < $callGenVals:nr_type,* > as $t:nr_type) => do
  let callGenKinds ← mkListLit (←callGenVals.getElems.toList.mapM fun _ => `(Kind.type))
  let callGenVals ← mkHListLit (←callGenVals.getElems.toList.mapM fun gVal => mkNrType gVal)
  let fnName := Syntax.mkStrLit (←mkNrIdent fnName)
  let (paramTps, outTp) ← getFuncSignature t
  wrapSimple (←`(Expr.fn $(←mkListLit paramTps) $outTp (FuncRef.decl $fnName $callGenKinds $callGenVals))) vname k
| `(nr_expr| ( $selfTp as $traitName < $traitGenVals,* > ) :: $methodName < $callGenVals,* > as $t:nr_type) => do
  let callGenKinds ← mkListLit (←callGenVals.getElems.toList.mapM fun _ => `(Kind.type))
  let callGenVals ← mkHListLit (←callGenVals.getElems.toList.mapM fun gVal => mkNrType gVal)
  let traitGenKinds ← mkListLit (←traitGenVals.getElems.toList.mapM fun _ => `(Kind.type))
  let traitGenVals ← mkHListLit (←traitGenVals.getElems.toList.mapM fun gVal => mkNrType gVal)
  let methodName := Syntax.mkStrLit (←mkNrIdent methodName)
  let traitName := Syntax.mkStrLit (←mkNrIdent traitName)
  let (paramTps, outTp) ← getFuncSignature t
  wrapSimple (←`(Expr.fn $(←mkListLit paramTps) $outTp
    (FuncRef.trait $(←mkNrType selfTp) $traitName $traitGenKinds $traitGenVals $methodName $callGenKinds $callGenVals))) vname k
| `(nr_expr| $fnExpr:nr_expr ( $args:nr_expr,* )) => do
  mkExpr fnExpr none fun fnRef => do
    mkArgs args.getElems.toList fun argVals => do
      let args ← mkHListLit argVals
      wrapSimple (←`(Expr.call _ _ $fnRef $args)) vname k
| `(nr_expr| ( $_:nr_expr as $_:nr_ident  < $_,* > ) . $_:ident)
| `(nr_expr| $_:nr_expr . $_:num)
| `(nr_expr| $_:nr_expr [ $_:nr_expr ])
| `(nr_expr| $_:nr_expr [[ $_:nr_expr ]]) => do
  let expr := getLeftmostExpr e
  let (lens, args) ← mkLens e ArgSet.empty
  mkExpr expr none fun exprVal => do
    mkArgs args.args fun vals => do
      wrapSimple (←`(Expr.getLens $exprVal $(←args.wrap vals lens))) vname k
| _ => throwUnsupportedSyntax

end

def mkFnDecl [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (syn : Syntax) :  m (String × TSyntax `term) := match syn with
| `(nr_fn_decl| $name < $generics,* > ( $params,* ) -> $outTp { $bExprs;* }) => do
  let name ← mkNrIdent name
  let generics := generics.getElems.toList.map fun i => (mkIdent $ Name.mkSimple i.getId.toString)
  let genericsDecl ← mkListLit (← generics.mapM fun _ => `(Kind.type))
  let params : List (TSyntax `term × TSyntax `term) ← params.getElems.toList.mapM fun p => match p with
    | `(nr_param_decl|$i:ident : $tp) => do pure (i, ←mkNrType tp)
    | _ => throwUnsupportedSyntax
  let body ← MonadSyntax.run $ mkBlock bExprs.getElems.toList fun x => `(Expr.var $x)
  let lambdaDecl ← `(fun rep generics => match generics with
    | $(←mkHListLit generics) => ⟨$(←mkListLit $ params.map Prod.snd), $(←mkNrType outTp), fun args => match args with
        | $(←mkHListLit $ params.map Prod.fst) => $body⟩)
  let syn : TSyntax `term ← `(FunctionDecl.mk $(Syntax.mkStrLit name) $ Function.mk $genericsDecl $lambdaDecl)
  pure (name, syn)
| _ => throwUnsupportedSyntax

def mkTraitImpl [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : Syntax → m (String × TSyntax `term)
| `(nr_trait_impl| < $generics,* > $traitName < $traitGenVals,* > for $targetType where $constraints,* { $fns;* }) => do
  let implGenericKinds ← mkListLit (←generics.getElems.toList.mapM fun _ => `(Kind.type))
  let traitGenValKinds ← mkListLit (←traitGenVals.getElems.toList.mapM fun _ => `(Kind.type))
  let implGenerics := generics.getElems.toList.map fun tyVar => (mkIdent $ Name.mkSimple tyVar.getId.toString)
  let traitGenVals ← traitGenVals.getElems.toList.mapM fun tyVar => mkNrType tyVar
  let traitName ← mkNrIdent traitName
  let fnDecls ← mkListLit (←fns.getElems.toList.mapM fun fnSyn => match fnSyn with
    | `(nr_trait_fn_def| fn $fnDecl) => do
      let fnDecl ← mkFnDecl fnDecl
      `(Prod.mk $(Syntax.mkStrLit fnDecl.1) $(fnDecl.2).fn)
    | _ => throwUnsupportedSyntax)
  let constraints ← constraints.getElems.mapM fun constraint => match constraint with
    | `(nr_trait_constraint| $ty : $tr:nr_ident < $tgVals,* >) => do
      let traitName ← mkNrIdent tr
      let tgValKinds ← mkListLit (←tgVals.getElems.toList.mapM fun _ => `(Kind.type))
      let tgVals ← tgVals.getElems.toList.mapM fun tyVar => mkNrType tyVar
      `(⟨⟨$(Syntax.mkStrLit traitName), $tgValKinds, $(←mkHListLit tgVals)⟩, $(←mkNrType ty)⟩)
    | _ => throwUnsupportedSyntax
  let targetType ← mkNrType targetType
  let syn : TSyntax `term ← `(TraitImpl.mk
    (traitGenericKinds := $traitGenValKinds)
    (implGenericKinds := $implGenericKinds)
    (traitGenerics := fun gs => match gs with | $(←mkHListLit implGenerics) => $(←mkHListLit traitGenVals))
    (constraints := fun gs => match gs with | $(←mkHListLit implGenerics) => $(←mkListLit constraints.toList))
    (self := fun gs => match gs with | $(←mkHListLit implGenerics) => $targetType)
    (impl := fun gs => match gs with | $(←mkHListLit implGenerics) => $fnDecls))
  pure (traitName, syn)
| _ => throwUnsupportedSyntax

def mkStructDef [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (structName : TSyntax `nr_ident) : Syntax → m (TSyntax `term)
| `(nr_struct_def| < $generics,* > { $params,* }) => do
  let genericKinds ← mkListLit (←generics.getElems.toList.mapM fun _ => `(Kind.type))
  let generics := generics.getElems.toList.map fun tyVar => (mkIdent $ Name.mkSimple tyVar.getId.toString)
  let fieldTypes ← params.getElems.toList.mapM fun paramSyn => match paramSyn with
    | `(nr_param_decl| $_:ident : $ty:nr_type) => mkNrType ty
    | _ => throwUnsupportedSyntax
  let fieldTypes ← `(fun gs => match gs with | $(←mkHListLit generics) => $(←mkListLit fieldTypes))
  let structNameStrLit := Syntax.mkStrLit (←mkNrIdent structName)
  let syn ← `(Struct.mk $structNameStrLit $genericKinds $fieldTypes)
  pure syn
| _ => throwUnsupportedSyntax

def mkStructProjector [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] (structName : TSyntax `nr_ident) : Syntax → m (List $ TSyntax `command)
| `(nr_struct_def| < $generics,* > { $params,* }) => do
  let genericKinds ← mkListLit (←generics.getElems.toList.mapM fun _ => `(Kind.type))
  let generics := generics.getElems.toList.map fun tyVar => (mkIdent $ Name.mkSimple tyVar.getId.toString)
  params.getElems.toList.enum.mapM fun (idx, paramSyn) => match paramSyn with
    | `(nr_param_decl| $paramName:ident : $paramType:nr_type) => do
      let paramDefTy ← `(match generics with
        | $(←mkHListLit generics) => Builtin.Member $(←mkNrType paramType) (Struct.fieldTypes $(mkStructDefIdent (←mkNrIdent structName)) generics))
      let paramDefSyn ← `(match generics with
        | $(←mkHListLit generics) => $(←mkTupleMember idx))
      let defnNameSyn := mkFieldAccessorIdent (←mkNrIdent structName) paramName.getId.toString
      `(def $defnNameSyn (generics : HList Kind.denote $genericKinds) : $paramDefTy := $paramDefSyn)
    | _ => throwUnsupportedSyntax
| _ => throwUnsupportedSyntax

elab "expr![" expr:nr_expr "]" : term => do
  let term ← MonadSyntax.run $ mkExpr expr none fun x => `(Expr.var $x)
  Elab.Term.elabTerm term.raw none

elab "nrfn![" "fn" fn:nr_fn_decl "]" : term => do
  let stx ← `($((←mkFnDecl fn).2).fn)
  Elab.Term.elabTerm stx none

elab "nr_def" decl:nr_fn_decl : command => do
  let (name, decl) ← mkFnDecl decl
  let decl ← `(def $(mkFunctionDefIdent name) : Lampe.FunctionDecl := $decl)
  Elab.Command.elabCommand decl

elab "nr_trait_impl[" defName:ident "]" impl:nr_trait_impl : command => do
  let (name, impl) ← mkTraitImpl impl
  let decl ← `(def $defName : String × Lampe.TraitImpl := ($(Syntax.mkStrLit name), $impl))
  Elab.Command.elabCommand decl

elab "nr_struct_def" defName:nr_ident defn:nr_struct_def : command => do
  -- define the struct itself
  let cmd ← `(def $(mkStructDefIdent (←mkNrIdent defName)) := $(←mkStructDef defName defn))
  Elab.Command.elabCommand cmd
  -- define the field projections
  let projs ← mkStructProjector defName defn
  _ ← projs.mapM fun cmd => do
    Elab.Command.elabCommand cmd

end Lampe
