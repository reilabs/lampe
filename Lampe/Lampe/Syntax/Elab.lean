import Lean

import Lampe.Syntax.Builders
import Lampe.Syntax.Rules
import Lampe.Syntax.State
import Lampe.Syntax.Utils

namespace Lampe

open Lean Elab

-- DSL: TERMS -------------------------------------------------------------------------------------

/-- Elaborates a function definition written in the Noir eDSL. -/
elab "noir_def" decl:noir_fn_def : command => do
  let (name, decl) ← makeFnDecl decl
  let decl ← `(def $name : FunctionDecl := $decl)
  Elab.Command.elabCommand decl

/-- Elaborates a trait implementation written in the Noir eDSL. -/
elab "noir_trait_impl[" defName:ident "]" impl:noir_trait_impl : command => do
  let (name, impl) ← makeTraitImpl impl
  let decl ← `(def $defName : String × TraitImpl := ($(Syntax.mkStrLit name.getId.toString), $impl))
  Elab.Command.elabCommand decl

/-- Elaborates a global definition written in the Noir eDSL. -/
macro "noir_global_def" name:ident ":" type:noir_type "=" value:noir_expr ";" : command => do
  let globalDecl ← `(noir_fn_def| $name:ident <> () -> $type:noir_type := $value:noir_expr)
  return ←`(noir_def $globalDecl:noir_fn_def)

-- DSL: TYPES -------------------------------------------------------------------------------------

/-- Elaborates a type alias written in the Noir eDSL. -/
elab "noir_type_alias" defn:noir_alias : command => do
  let (name, al) ← makeTypeAlias defn
  let decl ← `(@[reducible] def $name := $al)
  Elab.Command.elabCommand decl

/-- Elaborates a struct definition written in the Noir eDSL. -/
elab "noir_struct_def" defName:noir_ident defn:noir_type_def : command => do
  let cmd ← `(def $(makeStructDefIdent (←makeNoirIdent defName)) := $(←makeStructDef defName defn))
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
