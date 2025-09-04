import Lean
import Qq

import Lampe.Ast
import Lampe.Ast.Extensions
import Lampe.Builtin.Arith
import Lampe.Builtin.Array
import Lampe.Builtin.BigInt
import Lampe.Builtin.Bit
import Lampe.Builtin.Cmp
import Lampe.Builtin.Field
import Lampe.Builtin.Lens
import Lampe.Builtin.Memory
import Lampe.Builtin.Slice
import Lampe.Builtin.Str
import Lampe.Builtin.Struct
import Lampe.Semantics.Env
import Lampe.Semantics.Trait
import Lampe.Syntax.Rules
import Lampe.Syntax.State
import Lampe.Syntax.Utils
import Lampe.Tp

namespace Lampe

open Lean Elab Meta Qq

open Lampe

/--
Returns a term which constructs a `Lens` object that corresponds to the lvalue expression `expr`.

By construction, we are guaranteed that `expr` is an lvalue, and hence the builtin `modifyLens l`
can be combined with `getLvalRef expr` along with an RHS expression for lens modification.

Note that lenses are no longer used _directly_ for field access in structs, so this function purely
deals with their functionality for writing.
-/
partial def makeLens [MonadUtil m]
  : (expr : TSyntax `noir_lval)
  → (a : Args)
  → m ((TSyntax `term) × Args)
| `(noir_lval|$_:ident), a => do
  let nil ← ``(Lens.nil)
  pure (nil, a)
| `(noir_lval|($data:noir_lval . $idx : $_)), a => do
  let mem ← makeMember idx.getNat
  let (lhsLens, a') ← makeLens data a
  let lens' ← ``(Lens.cons $lhsLens (Access.tuple $mem))
  pure (lens', a')
| `(noir_lval|($arrayExpr:noir_lval [ $idxExpr:noir_expr ] : $_)), a => do
  let (idx, a') := a.next idxExpr
  let (lhsLens, a'') ← makeLens arrayExpr a'
  let lens' ← ``(Lens.cons $lhsLens (Access.array $idx))
  pure (lens', a'')
| `(noir_lval|($sliceExpr:noir_lval [[ $idxExpr:noir_expr ]] : $_)), a => do
  let (idx, a') := a.next idxExpr
  let (lhsLens, a'') ← makeLens sliceExpr a'
  let lens' ← ``(Lens.cons $lhsLens (Access.slice $idx))
  pure (lens', a'')
| `(noir_lval|(* $_:noir_expr : $_)), a => do pure ((←``(Lens.nil)), a)
| a , _ => throwError "Invalid LValue syntax {a}"

/--
Extracts and returns the parameter and return types from the syntax object `ty` that represents the
function type, or errors if the provided `ty` is not a function type.
-/
partial def extractFuncSignature [MonadDSL m]
  : (ty : TSyntax `noir_type)
  → m (List (TSyntax `term) × TSyntax `term)
| `(noir_type|λ( $paramTypes,* ) → $returnType)
| `(noir_type|λ( $paramTypes,* ) -> $returnType) => do
  let paramTypesExtracted ← paramTypes.getElems.toList.mapM fun p => makeNoirType p
  let returnTypeExtracted ← makeNoirType returnType
  pure (paramTypesExtracted, returnTypeExtracted)
| s => throwError "{s} was not a valid function type expression"

/-- Builds a pattern from the provided syntax tree, or errors if it is not a valid pattern. -/
partial def makePat [MonadDSL m] : TSyntax `noir_pat -> m Binder
| `(noir_pat|$i:noir_ident) => do
  let name ← makeNoirIdent i
  pure $ Binder.variable name
| `(noir_pat|mut $i:noir_ident) => do
  let name ← makeNoirIdent i
  pure $ Binder.mutable name
| `(noir_pat|( $pats,* )) => do pure $ Binder.tuple (←pats.getElems.toList.mapM makePat)
| p => throwError "Invalid pattern syntax {p}"

/-- Makes a lambda parameter from the provided syntax -/
def makeLambdaParam [MonadDSL m] (p : TSyntax `noir_lam_param) : m LambdaParam := match p with
| `(noir_lam_param|$pat:noir_pat : $ty) => do
  let pat ← makePat pat
  let ty ← makeNoirType ty
  pure ⟨pat, ty⟩
| _ => throwUnsupportedSyntax 

mutual

/--
Transforms the provided `binder` and `rhs` expression into a (chain of) let bindings and calls the
continuation `k` to continue building the chain.
-/
partial def makeBinder [MonadDSL m]
    (binder : Binder)
    (rhs : TSyntax `noir_expr)
    (k : m (TSyntax `term))
  : m (TSyntax `term) := match binder with
| .variable v => makeExpr rhs (some v) (some fun _ => k)
| b => do
  makeExpr rhs (none) fun result => makeBinder' b result k

/--
Transforms the provided `binder` and `rhsIdent` identifier term into a (chain of) let bindings and
calls the continuation `k` to continue building the chain.

This will build spurious expressions if `rhsIdent` is not an identifier but instead an arbitrary
term.
-/
partial def makeBinder' [MonadDSL m]
    (binder : Binder)
    (rhsIdent : TSyntax `term)
    (k : m (TSyntax `term))
  : m (TSyntax `term) := match binder with
| .mutable v => do
  regAutoDeref $ v.getId
  wrapInLet (←``(Expr.ref $rhsIdent)) v (some fun _ => k)
| .tuple xs => do
    makeTupleBinders 0 xs rhsIdent k
| _ => throwError "Encountered invalid binder"

/--
Builds the chain of let bindings required to represent the provided `binders` being destructured
from the identifier given by the term `rhs`.
-/
partial def makeTupleBinders [MonadDSL m]
    (ix : Nat)
    (binders : List Binder)
    (rhs : TSyntax `term)
    (k : m (TSyntax `term))
  : m (TSyntax `term) := do
  let member ← makeMember ix
  match binders with
  | [] => k
  | (Binder.variable v) :: t => do
    wrapInLet
      (←``(Expr.getMember $rhs $member))
      (some v)
      (some fun _ => makeTupleBinders (ix + 1) t rhs k)
  | h :: t => do
    wrapInLet
      (←``(Expr.getMember $rhs $member))
      none
      fun a => makeBinder' h a (makeTupleBinders (ix + 1) t rhs k)

/--
Processes the provided `expr` syntax tree, optionally binding to `binder` into a Lean term,
continuing by calling `k`, or errors if `expr` is not valid.
-/
partial def makeExpr [MonadDSL m]
    (expr : TSyntax `noir_expr)
    (binder : Option Lean.Ident)
    (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := match expr with
-- Sorry
| `(noir_expr|sorry) => do ``(sorry)

-- Literals
| `(noir_expr|$n:num : $tp) => do wrapInLet (←``(Expr.litNum $(←makeNoirType tp) $n)) binder k
| `(noir_expr|-$n:num : $tp) => do wrapInLet (←``(Expr.litNum $(←makeNoirType tp) (-$n))) binder k
| `(noir_expr|$s:str) => do wrapInLet (←``(Expr.litStr (String.length $s) (NoirStr.of $s))) binder k
| `(noir_expr|#_true) => do wrapInLet (←``(Expr.litNum Tp.bool 1)) binder k
| `(noir_expr|#_false) => do wrapInLet (←``(Expr.litNum Tp.bool 0)) binder k
| `(noir_expr|#_unit) => do wrapInLet (←``(Expr.skip)) binder k

-- Const generics value conversions
| `(noir_expr|fConst!( $name : $_ )) => do wrapInLet (←``(Expr.constFp $name)) binder k
| `(noir_expr|uConst!( $name : $_ )) => do wrapInLet (←``(Expr.constU $name)) binder k

-- Blocks
| `(noir_expr|{ $exprs;* }) => do
  let block ← makeBlock exprs.getElems.toList binder none
  wrapInLet block binder k

-- Skip
| `(noir_expr|#_skip) => do wrapInLet (←``(Expr.skip)) binder k

-- Bare identifiers
| `(noir_expr|$id:ident) => do makeBareIdent id binder k

-- If-then(-else) expressions
| `(noir_expr|if $cond then $expr) => makeExpr cond none fun cond => do
  let expr ← makeExpr expr none none
  wrapInLet (←``(Expr.ite $cond $expr Expr.skip)) binder k
| `(noir_expr|if $cond then $ifTrue else $ifFalse) => makeExpr cond none fun cond => do
  let ifTrue ← makeExpr ifTrue none none
  let ifFalse ← makeExpr ifFalse none none
  wrapInLet (←``(Expr.ite $cond $ifTrue $ifFalse)) binder k

-- Member projection
| `(noir_expr|$value . $ix) => do
  makeExpr value none fun v => do
    let member ← makeMember ix.getNat
    let expr ← ``(Expr.getMember $v $member)
    wrapInLet expr binder k

-- Parenthesized expressions
| `(noir_expr|($expr:noir_expr)) => makeExpr expr binder k
| `(noir_expr|($expr:noir_lambda)) => makeLambda expr binder k

-- Builtin Calls
| `(noir_expr|(#_ $name:ident returning $tp)( $args,* )) =>
  makeArgs args.getElems.toList fun args => do
    let argVals ← makeHListLit args
    wrapInLet
      (←``(Expr.callBuiltin _ $(←makeNoirType tp) $(←makeBuiltin name.getId.toString) $argVals))
      binder
      k

-- Bare function refs
| `(noir_expr|$ref:noir_funcref) => match ref with
  | `(noir_funcref|(#_ $_:ident returning $_)) =>
    throwError "Encountered builtin {ref} as bare function reference"

  -- Ident funcrefs (calling via a local name)
  | `(noir_funcref|($name as $_)) => do
    let exprName ← `(noir_expr|$name:noir_ident)
    makeExpr exprName binder k

  -- Calls to declarations
  | `(noir_funcref|($name< $gens,* > as $ty)) => do
    let (genKinds, genVals) ← makeGenericValTerms gens.getElems.toList
    let fnName := Syntax.mkStrLit (←makeNoirIdent name).getId.toString
    let (paramTypes, outType) ← extractFuncSignature ty
    wrapInLet
      (← ``(Expr.fn
        $(←makeListLit paramTypes)
        $outType
        (FuncRef.decl $fnName $genKinds $genVals)
      ))
      binder
      k

  -- Calls to trait methods
  | `(noir_funcref|(($selfTp as $tName< $traitGens,* >)::$fName< $funcGens,* > as $tp)) => do
    let (traitGenKinds, traitGenVals) ← makeGenericValTerms traitGens.getElems.toList
    let (funcGenKinds, funcGenVals) ← makeGenericValTerms funcGens.getElems.toList
    let traitName := Syntax.mkStrLit (←makeNoirIdent tName).getId.toString
    let methodName := Syntax.mkStrLit (←makeNoirIdent fName).getId.toString
    let (paramTypes, outType) ← extractFuncSignature tp
    let selfTp ← makeNoirType selfTp

    wrapInLet
      (← ``(Expr.fn
        $(←makeListLit paramTypes)
        $outType
        (FuncRef.trait
          $selfTp
          $traitName
          $traitGenKinds
          $traitGenVals
          $methodName
          $funcGenKinds
          $funcGenVals
        )
      ))
      binder
      k

  -- Direct lambda calls (fn(a, b): c := a + b)(a, b)
  | `(noir_funcref|($_lam:noir_lambda)) =>
    throwError "Direct calls of lambdas are not currently supported"

  | _ => throwError "Unsupported function reference syntax"

-- Function calls
| `(noir_expr|$ref:noir_funcref( $args,* )) => do
  let ref ← `(noir_expr|$ref:noir_funcref)
  makeExpr ref none fun funcRef => makeArgs args.getElems.toList fun args => do
    let argVals ← makeHListLit args
    wrapInLet (←``(Expr.call _ _ $funcRef $argVals)) binder k

-- Lambdas
| `(noir_expr|$lam:noir_lambda) => makeLambda lam binder k

-- Assignments
| `(noir_expr|$lhs:noir_lval = $rhs) => do
  let (lens, args) ← makeLens lhs Args.empty
  makeExpr rhs none fun rhs => do
    makeArgs args.args fun vals => do
      match (←getLValueRef lhs) with
      | .ident r => do
        wrapInLet (←``(Expr.modifyLens $r $rhs $(←args.wrap vals lens))) binder k
      | .expr e => do
        makeExpr e none $ some fun lhs => do
          wrapInLet (←``(Expr.modifyLens $lhs $rhs $(←args.wrap vals lens))) binder k
      | .none => throwError "Encountered invalid lval {lhs}"

-- For loops
| `(noir_expr|for $i in $lo .. $hi do $body) => do
  let i ← makeNoirIdent i
  makeExpr lo none $ some fun lo =>
    makeExpr hi none $ some fun hi => do
      let body ← makeExpr body none none
      wrapInLet (←``(Expr.loop $lo $hi fun $i => $body)) binder k

-- Lets not in blocks
| e@`(noir_expr|let $_ = $_) => throwError "Encountered let binding {e} in invalid location; does your block need to end with a #_skip?"

-- Finally, our error case.
| e => throwError "Invalid expression {e}"

/-- Builds a lambda from the provided term, returning an error if it is invalid. -/
partial def makeLambda [MonadDSL m]
  : (lam : TSyntax `noir_lambda)
  → (binder : Option Lean.Ident)
  → (k : Option $ TSyntax `term → m (TSyntax `term))
  → m (TSyntax `term)
| `(noir_lambda|fn( $params,* ): $retType := $body), binder, k => do
  let retType : TSyntax `term ← makeNoirType retType
  let params ← params.getElems.toList.mapM makeLambdaParam 
  let paramTypes := params.map fun p => p.type
  let paramTypes ← makeListLit paramTypes
  let paramNames ← params.mapM fun b => match b.binder with
  | .variable n => ``($n)
  | .mutable _ => throwError "Mutable binders not currently supported in lambda parameters"
  | .tuple _ => throwError "Tuple binders not currently supported in lambda parameters"
  | .invalid => throwError "Encountered invalid binder"
  let args : TSyntax `term ← makeHListLit paramNames
  let body : TSyntax `term ← makeExpr body none none
  let matcher : TSyntax `term ← ``(fun args => match args with | $args => $body)
  wrapInLet
    (←``(Expr.lam $paramTypes $retType $matcher))
    binder
    k
| l, _, _ => throwError "Invalid lambda syntax {l} encountered"

/--
Handles the wrapping of a bare identifier in an automatic dereference if necessary, and otherwise
continues with the provided identifier.
-/
partial def makeBareIdent [MonadDSL m]
    (ident : TSyntax `ident)
    (binder : Option Lean.Ident)
    (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := do
  if ←isAutoDerefd ident.getId then
    wrapInLet (←``(Expr.readRef $ident)) binder k
  else match binder with
  | none => match k with
    | some k => k ident
    | none => ``(Expr.var $ident)
  | some _ => wrapInLet (←``(Expr.var $ident)) binder k

/--
Processes the provided `items` of the block into a lean term, calling the continuation `k` to
continue the process.
-/
partial def makeBlock [MonadDSL m]
    (items : List (TSyntax `noir_expr))
    (binder : Option Lean.Ident)
    (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := match items with
| head :: next :: rest => do
  match head with
  | `(noir_expr|let $b = $e) => do makeBinder (←makePat b) e (makeBlock (next :: rest) binder k)
  | e => do makeExpr e none $ some fun _ => makeBlock (next :: rest) binder k
| [last] => makeExpr last binder k
| _ => throwError "Empty blocks are invalid"

/--
Builds the Lean expression corresponding to a list of arguments from the syntax tree by unfolding
argument expressions to ensure they are in ANF.

Will result in an error if `makeExpr` or the continuation `k` fails on any of the provided `args`.
-/
partial def makeArgs [MonadDSL m]
    (args : List (TSyntax `noir_expr))
    (k : List (TSyntax `term) → m (TSyntax `term))
  : m (TSyntax `term) := match args with
| [] => k []
| h :: t => makeExpr h none (some fun h => makeArgs t fun t => k (h :: t))

end

/--
Handles the registration of mutable arguments for proper handling, or returns an error if invalid.
-/
def makeMutableArgs [MonadDSL m]
    (mutArgs : List (TSyntax `term))
    (k : m (TSyntax `term))
  : m (TSyntax `term) := match mutArgs with
| [] => k
| h :: t => match h with
  | `($h:ident) => do
    regAutoDeref h.getId
    ``(Expr.letIn (Expr.ref $h) fun $h => $(←makeMutableArgs t k))
  | _ => throwUnsupportedSyntax

/--
Builds a function declaration from the provided syntax, or returns an error if the syntax is
invalid.
-/
def makeFnDecl [MonadUtil m] (syn : Syntax) : m (Lean.Ident × TSyntax `term) := match syn with
| `(noir_fn_def|$name:noir_ident < $generics,* >( $params,* ) → $returnType := $body)
| `(noir_fn_def|$name:noir_ident < $generics,* >( $params,* ) -> $returnType := $body) => do
  let name ← makeNoirIdent name
  let (genericKinds, genericDefs) ← makeGenericDefTerms generics.getElems.toList
  let params ← params.getElems.toList.mapM makeFuncParam
  let mutParams := params.filterMap fun ⟨i, _, isMut⟩ => if isMut then some i else none
  let body ← MonadDSL.run $ makeMutableArgs mutParams do
    makeExpr body none none
  let lambda ← ``(fun rep generics => match generics with
  | $(genericDefs) => ⟨
      $(←makeListLit $ params.map fun ⟨_, t, _⟩ => t),
      $(←makeNoirType returnType),
      fun args => match args with
      | $(←makeHListLit $ params.map fun ⟨i, _, _⟩ => i) => $body
    ⟩
  )
  let syn ← ``(FunctionDecl.mk
              $(Syntax.mkStrLit name.getId.toString) $ Function.mk $genericKinds $lambda)
  pure (name, syn)
| _ => throwUnsupportedSyntax

/--
Builds a trait implementation from the provided syntax, or returns an error if the syntax is
invalid.
-/
def makeTraitImpl [MonadUtil m] : Syntax → m (Lean.Ident × TSyntax `term)
| `(noir_trait_impl|< $gDefs,* > $tName < $gVals,* > for $self where [ $wheres,* ] := { $defs;* }) => do
  let (genDefKinds, genDefVars) ← makeGenericDefTerms gDefs.getElems.toList
  let (genValKinds, genValVals) ← makeGenericValTerms gVals.getElems.toList
  let traitName ← makeNoirIdent tName
  let targetType ← makeNoirType self
  let fnDecls ← defs.getElems.toList.mapM fun d => match d with
  | `(noir_trait_impl_method|noir_def $func) => do
    let (s, d) ← makeFnDecl func
    ``(Prod.mk $(Syntax.mkStrLit s.getId.toString) (FunctionDecl.fn $d))
  | _ => throwUnsupportedSyntax
  let fnDecls ← makeListLit fnDecls
  let constraints ← wheres.getElems.mapM fun c => match c with
  | `(noir_where_clause|$genName:noir_type : $bound < $constraintGens,* >) => do
    let traitName ← makeNoirIdent bound
    let (tgKinds, tgVals) ← makeGenericValTerms constraintGens.getElems.toList
    ``(⟨⟨$(Syntax.mkStrLit traitName.getId.toString), $tgKinds, $tgVals⟩, $(←makeNoirType genName)⟩)
  | _ => throwUnsupportedSyntax
  let syn ← ``(TraitImpl.mk
    (traitGenericKinds := $genValKinds)
    (implGenericKinds := $genDefKinds)
    (traitGenerics := fun gs => match gs with | $genDefVars => $genValVals)
    (constraints := fun gs => match gs with | $genDefVars => $(←makeListLit constraints.toList))
    (self := fun gs => match gs with | $genDefVars => $targetType)
    (impl := fun gs => match gs with | $genDefVars => $fnDecls)
  )

  pure (traitName, syn)
| _ => throwUnsupportedSyntax

/--
Builds a struct definition from the provided syntax, or returns an error if the syntax is invalid.
-/
def makeStructDef [MonadUtil m] (name : TSyntax `noir_ident): Syntax → m (TSyntax `term)
| `(noir_type_def|< $genDefs,* > { $members,* }) => do
  let (genKinds, genDefs) ← makeGenericDefTerms genDefs.getElems.toList
  let fieldTypes ← members.getElems.toList.mapM fun paramSyn => match paramSyn with
  | `(noir_type|$type) => makeNoirType type
  let fieldTypes ← `(fun gs => match gs with | $genDefs => $(←makeListLit fieldTypes))
  let structNameStrLit := Syntax.mkStrLit (←makeNoirIdent name).getId.toString
  let syn ← ``(Struct.mk $structNameStrLit $genKinds $fieldTypes)

  pure syn
| _ => throwUnsupportedSyntax

/-- Builds a type alias from the provided syntax, or returns an error if invalid. -/
def makeTypeAlias [MonadUtil m] : Syntax → m (TSyntax `ident × TSyntax `term)
| `(noir_alias|$name < $genDefs,* > := $type ;) => do
  let (genKinds, genDefs) ← makeGenericDefTerms genDefs.getElems.toList
  let tp ← makeNoirType type
  let syn ← ``(fun (gens : HList Kind.denote $genKinds) => match gens with | $genDefs => $tp)
  let defName := makeTypeAliasIdent (←makeNoirIdent name)
  pure (defName, syn)
| _ => throwUnsupportedSyntax

/-- Builds a trait definition, or returns an error if the provided syntax is invalid. -/
def makeTraitDef [MonadUtil m] : Syntax → m (List $ TSyntax `command)
| `(noir_trait_def|$traitName < $traitGenDefs,* > [ $assocTps,* ] := { $methods;* }) => do
  let mut outputs := []

  let traitName ← makeNoirIdent traitName
  let (traitGenKinds, traitGenDefs) ← makeGenericDefTerms traitGenDefs.getElems.toList
  let traitGenKindsDecl ←
    `(abbrev $(makeTraitDefGenericKindsIdent traitName) : List Kind := $traitGenKinds)
  outputs := outputs.concat traitGenKindsDecl
  let (assocTypeGenKinds, assocTypeGenDefs) ← makeGenericDefTerms assocTps.getElems.toList
  let associatedTypesKindDecl ←
    `(abbrev $(makeTraitDefAssociatedTypesKindsIdent traitName) : List Kind := $assocTypeGenKinds)
  outputs := outputs.concat associatedTypesKindDecl

  let traitHasImplDecl : TSyntax `command ← 
    `(@[reducible] def $(makeTraitDefHasImplIdent traitName) 
      (env : $(←``(Env)))
      (traitGenerics : HList Kind.denote $(makeTraitDefGenericKindsIdent traitName))
      (selfType : Tp) :=
        $(←``(TraitResolvable)) env 
        ⟨⟨$(Syntax.mkStrLit traitName.getId.toString), 
          $(makeTraitDefGenericKindsIdent traitName), 
          traitGenerics⟩, 
        selfType⟩)
  outputs := outputs.concat traitHasImplDecl

  for method in methods.getElems.toList do match method with
  | `(noir_trait_method|method $methName < $methGens,*> ( $params,* ) → $retType)
  | `(noir_trait_method|method $methName < $methGens,*> ( $params,* ) -> $retType) => do
    let fnName ← makeNoirIdent methName
    let (fnGenKinds, fnGenDefs) ← makeGenericDefTerms methGens.getElems.toList
    let fnGensDecl ←
      `(abbrev $(makeTraitFunDefGenericKindsIdent traitName fnName) : List Kind := $fnGenKinds)
    outputs := outputs.concat fnGensDecl

    let params ← params.getElems.toList.mapM makeNoirType
    let inTypesDecl ← `(
      def $(makeTraitFunDefInputsIdent traitName fnName)
      : HList Kind.denote $(makeTraitDefGenericKindsIdent traitName)
      → Tp
      → HList Kind.denote $(makeTraitDefAssociatedTypesKindsIdent traitName)
      → HList Kind.denote $(makeTraitFunDefGenericKindsIdent traitName fnName)
      → List Tp := fun gens $(mkIdent $ Name.mkSimple "Self") assocTps fnGens => match gens with
        | $traitGenDefs => match fnGens with
          | $fnGenDefs => match assocTps with
            | $assocTypeGenDefs => $(←makeListLit params)
    )
    outputs := outputs.concat inTypesDecl

    let outTp ← makeNoirType retType
    let outTypeDecl ← `(
      def $(makeTraitFunDefOutputIdent traitName fnName)
      : HList Kind.denote $(makeTraitDefGenericKindsIdent traitName)
      → Tp
      → HList Kind.denote $(makeTraitDefAssociatedTypesKindsIdent traitName)
      → HList Kind.denote $(makeTraitFunDefGenericKindsIdent traitName fnName)
      → Tp := fun gens $(mkIdent $ Name.mkSimple "Self") assocTps fnGens => match gens with
        | $traitGenDefs => match fnGens with
          | $fnGenDefs => match assocTps with
            | $assocTypeGenDefs => $outTp
    )
    outputs := outputs.concat outTypeDecl

    let callDecl ← `(
      def $(makeTraitFunDefIdent traitName fnName) {p}
        (generics : HList Kind.denote $(makeTraitDefGenericKindsIdent traitName))
        (Self : Tp)
        (associatedTypes : HList Kind.denote $(makeTraitDefAssociatedTypesKindsIdent traitName))
        (fnGenerics : HList Kind.denote $(makeTraitFunDefGenericKindsIdent traitName fnName))
        (args : HList
          (Tp.denote p)
          ($(makeTraitFunDefInputsIdent traitName fnName) generics Self associatedTypes fnGenerics))
      : Expr
          (Tp.denote p)
          ($(makeTraitFunDefOutputIdent traitName fnName) generics Self associatedTypes fnGenerics) :=
      Expr.call
        ($(makeTraitFunDefInputsIdent traitName fnName) generics Self associatedTypes fnGenerics)
        ($(makeTraitFunDefOutputIdent traitName fnName) generics Self associatedTypes fnGenerics)
        (FuncRef.trait
          Self
          $(Syntax.mkStrLit traitName.getId.toString)
          $(makeTraitDefGenericKindsIdent traitName)
          generics
          $(Syntax.mkStrLit fnName.getId.toString)
          $(makeTraitFunDefGenericKindsIdent traitName fnName)
          fnGenerics
        )
        args
    )
    outputs := outputs.concat callDecl
  | _ => throwUnsupportedSyntax

  pure outputs
| _ => throwUnsupportedSyntax
