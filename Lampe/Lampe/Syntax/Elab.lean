import Lean

import Lampe.Syntax.Builders
import Lampe.Syntax.Rules
import Lampe.Syntax.State
import Lampe.Syntax.Utils

namespace Lampe

open Lean Elab

-- DSL: TERMS -------------------------------------------------------------------------------------

/--
Views `stx` as a compile-time-constant element of an array literal, returning a term for its
denoted value (the surrounding list ascription supplies the expected type). Returns `none` for
anything that is not a numeric or boolean literal.
-/
private partial def litArrayElem (stx : TSyntax `noir_expr) :
    Elab.Command.CommandElabM (Option (TSyntax `term)) := do
  match stx with
  | `(noir_expr|($e:noir_expr)) => litArrayElem e
  | `(noir_expr|$n:num : $_) => return some (←`($n))
  | `(noir_expr|-$n:num : $_) => return some (←`((-$n)))
  | `(noir_expr|#_true) => return some (←`(true))
  | `(noir_expr|#_false) => return some (←`(false))
  | _ => return none

/-- Applies `f` to every node of `stx` top-down, replacing a node (without descending into the
replacement) whenever `f` returns `some`. -/
private partial def replaceSyntaxTopDownM [Monad m] (f : Syntax → m (Option Syntax))
    (stx : Syntax) : m Syntax := do
  match ← f stx with
  | some new => return new
  | none => match stx with
    | .node info kind args => return .node info kind (← args.mapM (replaceSyntaxTopDownM f))
    | s => return s

/--
Rewrites every `#_ mkArray` / `#_ mkVector` call in `stx` whose arguments are all compile-time
constants into a single `Builtin.mkValArray` / `Builtin.mkValVector` call (via the `splice!`
escape hatch), hoisting the element values into an auxiliary definition named
`«<baseName>#lits<i>»`.

The general `mkArray` path `letIn`-binds every element, so an `n`-element literal produces a term
(and, later, proof goals) of depth `O(n)`; every recursive traversal of such a term — during
elaboration, `simp`, or unification — then needs recursion depth and time proportional to `n`,
which makes large array literals unusably slow. After this rewrite the extracted body and all
goals about it contain only the (shallow) auxiliary constant, so their cost is independent of the
array size. The auxiliary definition elaborates the deep list literal exactly once.

Arrays with any non-constant element (e.g. a function call) are left on the general path.
-/
private def hoistLiteralArrays (baseName : Name) (stx : Syntax) :
    Elab.Command.CommandElabM Syntax := do
  let counter ← IO.mkRef (0 : Nat)
  let pId := mkIdent `p
  let rewrite (node : Syntax) : Elab.Command.CommandElabM (Option Syntax) := do
    let tnode : TSyntax `noir_expr := ⟨node⟩
    match tnode with
    | `(noir_expr|(#_ $nm:ident returning $tp)( $args,* )) => do
      let isArray := nm.getId == `mkArray
      unless isArray || nm.getId == `mkVector do return none
      if args.getElems.isEmpty then return none
      let elems ← args.getElems.mapM litArrayElem
      let some elems := elems.mapM id | return none
      let arrTp ← MonadDSL.run (makeNoirType tp)
      -- Emit the element list in chunks joined by `++` so that the nesting depth of the
      -- elaborated term stays bounded regardless of the array length.
      let chunkSize := 256
      let mut chunks : Array (Array (TSyntax `term)) := #[]
      let mut i := 0
      while i < elems.size do
        chunks := chunks.push (elems.extract i (min (i + chunkSize) elems.size))
        i := i + chunkSize
      let mut body ← `([$(chunks.back!),*])
      for c in chunks.pop.reverse do
        body ← `([$c,*] ++ $body)
      let idx ← counter.modifyGet fun i => (i, i + 1)
      let auxId := mkIdent <| Name.mkSimple s!"{baseName.getString!}#lits{idx}"
      let elemTp ← if isArray then `(Tp.arrayElem $arrTp) else `(Tp.vectorElem $arrTp)
      Elab.Command.elabCommand <| ←
        `(def $auxId ($pId : Prime) : List (Tp.denote $pId $elemTp) := $body)
      let repl ← if isArray then
        `(noir_expr|
          splice!( Expr.callBuiltin [] $arrTp (Builtin.mkValArray $arrTp $auxId) h![] ))
      else
        `(noir_expr|
          splice!( Expr.callBuiltin [] $arrTp (Builtin.mkValVector $elemTp $auxId) h![] ))
      return some repl.raw
    | _ => return none
  replaceSyntaxTopDownM rewrite stx

/-- Elaborates a function definition written in the Noir eDSL. -/
elab d:noir_depr? "noir_def" decl:noir_fn_def : command => do
  let baseName ← makeNoirIdent decl.raw[0]
  let decl : TSyntax `noir_fn_def := ⟨← hoistLiteralArrays baseName.getId decl.raw⟩
  let (name, decl) ← makeFnDecl decl
  let decl ← match (←parseDeprecatedMessage d) with
  | some msg => `(
    @[deprecated $name $(Syntax.mkStrLit msg) (since := "")]
    def $name : FunctionDecl := $decl)
  | none => `(def $name : FunctionDecl := $decl)
  Elab.Command.elabCommand decl

/-- Elaborates a trait implementation written in the Noir eDSL. -/
elab "noir_trait_impl[" defName:ident "]" impl:noir_trait_impl : command => do
  let impl : TSyntax `noir_trait_impl := ⟨← hoistLiteralArrays defName.getId impl.raw⟩
  let (name, impl) ← makeTraitImpl impl
  let decl ← `(def $defName : String × TraitImpl := ($(Syntax.mkStrLit name.getId.toString), $impl))
  Elab.Command.elabCommand decl

/-- Elaborates a global definition written in the Noir eDSL. -/
macro "noir_global_def" name:noir_ident ":" type:noir_type "=" value:noir_expr ";" : command => do
  let globalDecl ← `(noir_fn_def| $name:noir_ident <> () -> $type:noir_type := $value:noir_expr)
  return ←`(noir_def $globalDecl:noir_fn_def)

-- DSL: TYPES -------------------------------------------------------------------------------------

/-- Elaborates a type alias written in the Noir eDSL. -/
elab "noir_type_alias" defn:noir_alias : command => do
  let (name, al) ← makeTypeAlias defn
  let decl ← `(@[reducible] def $name := $al)
  Elab.Command.elabCommand decl

/-- Elaborates a struct definition written in the Noir eDSL. -/
elab d:noir_depr? "noir_struct_def" defName:noir_ident defn:noir_type_def : command => do
  let ident := makeStructDefIdent (←makeNoirIdent defName)
  let cmd ← match (←parseDeprecatedMessage d) with
  | some msg => `(
    @[deprecated $ident $(Syntax.mkStrLit msg) (since := "")] 
    def $ident := $(←makeStructDef defName defn))
  | none => `(def $ident := $(←makeStructDef defName defn))
  Elab.Command.elabCommand cmd

/-- Elaborates a trait definition written in the Noir eDSL. -/
elab "noir_trait_def" defn:noir_trait_def : command => do
  let definitions ← makeTraitDef defn
  definitions.forM fun f => Elab.Command.elabCommand f

-- DEBUGGING --------------------------------------------------------------------------------------

/--
Elaborates an expression in the Noir eDSL, primarily intended for debugging.

It is intended to be used with `#check`, such as `#check expr!![1 : u8]`.
-/
elab "expr!![" expr:noir_expr "]" : term => do
  let term ← MonadDSL.run $ makeExpr expr none none
  Elab.Term.elabTerm term none

/--
Elaborates a type in the Noir eDSL, primarily intended for debugging.

It is intended to be used with `#check`, such as `#check type!![u64]`.
-/
elab "type!![" type:noir_type "]" : term => do
  let term ← MonadDSL.run $ makeNoirType type
  Elab.Term.elabTerm term none

/--
Elaborates a type in the Noir eDSL, primarily intended for debugging.

It is intended to be used with `#check`, such as `#check kind!![Type]`.
-/
elab "kind!![" kind:noir_kind "]" : term => do
  let term ← MonadDSL.run $ makeKind kind
  Elab.Term.elabTerm term none

/--
Elaborates a generic value in the Noir eDSL, primarily intended for debugging.

It is intended to be used with `#check`, such as `#check gVal![I : Type]`.
-/
elab "gVal!![" g:noir_gen_val "]" : term => do
  let term ← MonadDSL.run do
    let val ← makeGenericVal g
    let value := val.value
    let kind ← quoteKind val.kind
    ``(($value, $kind))
  Elab.Term.elabTerm term none
