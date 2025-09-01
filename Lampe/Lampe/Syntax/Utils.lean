import Lean

import Lampe.Builtin.Lens
import Lampe.Builtin.Memory
import Lampe.Builtin.Struct
import Lampe.Syntax.Rules
import Lampe.Tp

namespace Lampe

open Lean Elab Syntax
open Lampe

/--
The monad providing basic functionality for operations that do not require the ability to access the
desugaring state.
-/
class MonadUtil (m : Type → Type) extends
  Monad m,
  MonadQuotation m,
  MonadExceptOf Exception m,
  MonadError m

/--
Make typeclass resolution not so stupid, and make sure that the type checker knows that this is the
right thing.
-/
@[default_instance]
instance
  [Monad m]
  [MonadQuotation m]
  [MonadExceptOf Exception m]
  [MonadError m]
: MonadUtil m where

/-- A representation of a generic value, pairing the syntactic value with its concrete kind. -/
structure GenericValue where
  value : TSyntax `term
  kind : Lampe.Kind
deriving Nonempty

/-- A representation of a generic definition, pairing a type variable with its concrete kind. -/
structure GenericDef where
  name : TSyntax `term
  kind : Lampe.Kind
deriving Nonempty

/-- A representation of a function parameter. -/
structure FuncParam where
  name : Lean.Ident
  type : TSyntax `term
  isMut : Bool
deriving Nonempty

/--
A useful function for easily rendering Noir types as the type representation functions used by
Lampe.
-/
abbrev typeOf {tp : Tp} {rep : Tp → Type} : rep tp → Tp := fun _ => tp

/-- Makes a list literal from the provided list of terms. -/
def makeListLit [MonadUtil m] : List (TSyntax `term) → m (TSyntax `term)
| [] => `([])
| x :: xs => do
  let tail ← makeListLit xs
  ``(List.cons $x $tail)

/-- Makes an HList literal from the provided list of terms. -/
def makeHListLit [MonadUtil m] : List (TSyntax `term) → m (TSyntax `term)
| [] => `(HList.nil)
| x :: xs => do
  let tail ← makeHListLit xs
  ``(HList.cons $x $tail)

/--
Builds a numeric constant from the provided syntax term.

Throws an exception if unable to build an appropriate term from the provided syntax tree.
-/
partial def makeConstNum [MonadUtil m] : TSyntax `noir_const_num → m (TSyntax `term)
| `(noir_const_num|$n:num) => pure $ n
| `(noir_const_num|$i:ident) => ``($i)
| `(noir_const_num|($n)) => makeConstNum n
| `(noir_const_num|$n1 + $n2) => do
  let n1 ← makeConstNum n1
  let n2 ← makeConstNum n2
  ``(BitVec.add $n1 $n2)
| `(noir_const_num|$n1 - $n2) => do
  let n1 ← makeConstNum n1
  let n2 ← makeConstNum n2
  ``(BitVec.sub $n1 $n2)
| `(noir_const_num|$n1 * $n2) => do
  let n1 ← makeConstNum n1
  let n2 ← makeConstNum n2
  ``(BitVec.mul $n1 $n2)
| `(noir_const_num|$n1 / $n2) => do
  let n1 ← makeConstNum n1
  let n2 ← makeConstNum n2
  ``(BitVec.udiv $n1 $n2)
| `(noir_const_num|$n1 % $n2) => do
  let n1 ← makeConstNum n1
  let n2 ← makeConstNum n2
  ``(BitVec.umod $n1 $n2)
| n => throwError "Unexpected numeric syntax {n}"

/-- Builds a noir identifier from the provided syntax tree, or throws an error. -/
private partial def makeNoirIdentAux [MonadUtil m] : Syntax → m String
| `(ident|$i:ident) => pure i.getId.toString
| `(noir_ident|$i:ident) => pure i.getId.toString
| `(noir_ident|from) => pure "from"
| `(noir_ident|$i:ident :: $j:noir_ident) => do pure s!"{i.getId}::{←makeNoirIdentAux j}"
| `(noir_ident|_) => pure "_"
| i => throwError "Invalid identifier `{i}`"

def makeNoirIdent [MonadUtil m] : Syntax → m Lean.Ident :=
  fun stx => (mkIdent $ .mkSimple ·) <$> makeNoirIdentAux stx

/-- Builds the identifier for a struct definition. -/
def makeStructDefIdent (structName : Lean.Ident) : Lean.Ident :=
  mkIdent $ .mkSimple $ structName.getId.toString false

/-- Builds the identifier for a type alias. -/
def makeTypeAliasIdent (aliasName : Lean.Ident) : Lean.Ident :=
  mkIdent $ .mkSimple $ aliasName.getId.toString false

/-- Generates the term corresponding to the kind of a numeric generic. -/
def matchGenericDefinitions [MonadUtil m] : TSyntax `ident → m (TSyntax `term)
| `(ident|Field) => ``(Lampe.Kind.field)
| `(ident|u1) => ``(Lampe.Kind.u 1)
| `(ident|u8) => ``(Lampe.Kind.u 8)
| `(ident|u16) => ``(Lampe.Kind.u 16)
| `(ident|u32) => ``(Lampe.Kind.u 32)
| `(ident|u64) => ``(Lampe.Kind.u 64)
| `(ident|u128) => ``(Lampe.Kind.u 128)
| k => throwError "Invalid generic kind {k}"

/-- Turns the provided `kind` back into its syntactic term representation. -/
def quoteKind [MonadUtil m] (kind : Lampe.Kind) : m (TSyntax `term) :=
  match kind with
  | .u 1 => ``(Lampe.Kind.u 1)
  | .u 8 => ``(Lampe.Kind.u 8)
  | .u 16 => ``(Lampe.Kind.u 16)
  | .u 32 => ``(Lampe.Kind.u 32)
  | .u 64 => ``(Lampe.Kind.u 64)
  | .u 128 => ``(Lampe.Kind.u 128)
  | .field => ``(Lampe.Kind.field)
  | .type => ``(Lampe.Kind.type)
  | _ => throwUnsupportedSyntax

/-- Builds a literal kind from the provided syntax tree, throwing an error if invalid. -/
partial def makeKindValue [MonadUtil m] : (kind: TSyntax `noir_kind) → m Lampe.Kind
| `(noir_kind|Field) => pure Lampe.Kind.field
| `(noir_kind|u1) => pure $ Lampe.Kind.u 1
| `(noir_kind|u8) => pure $ Lampe.Kind.u 8
| `(noir_kind|u16) => pure $ Lampe.Kind.u 16
| `(noir_kind|u32) => pure $ Lampe.Kind.u 32
| `(noir_kind|u64) => pure $ Lampe.Kind.u 64
| `(noir_kind|u128) => pure $ Lampe.Kind.u 128
| `(noir_kind|Type) => pure $ Lampe.Kind.type
| k => throwError "Unsupported kind {k}"

/--
Builds the term corresponding to the kind of a generic parameter definition, throwing an error if
invalid.
-/
partial def makeKind [MonadUtil m] : (kind : TSyntax `noir_kind) → m (TSyntax `term)
| `(noir_kind|Field) => ``(Lampe.Kind.field)
| `(noir_kind|u1) => ``(Lampe.Kind.u 1)
| `(noir_kind|u8) => ``(Lampe.Kind.u 8)
| `(noir_kind|u16) => ``(Lampe.Kind.u 16)
| `(noir_kind|u32) => ``(Lampe.Kind.u 32)
| `(noir_kind|u64) => ``(Lampe.Kind.u 64)
| `(noir_kind|u128) => ``(Lampe.Kind.u 128)
| `(noir_kind|Type) => ``(Lampe.Kind.type)
| k => throwError "Unsupported kind {k}"

mutual

/-- Builds the term corresponding to a generic value, throwing an error if invalid. -/
partial def makeGenericVal [MonadUtil m] : TSyntax `noir_gen_val → m GenericValue
| `(noir_gen_val|$t:noir_type) => do
  pure ⟨←makeNoirType t, Lampe.Kind.type⟩
| `(noir_gen_val|$n:noir_const_num : $k:noir_kind) => do
  pure ⟨←makeConstNum n, ←makeKindValue k⟩
| g => throwError "Unsupported generic value {g}"

/--
Builds a list of terms where each corresponds to a generic value, throwing an error if invalid.
-/
partial def makeGenericVals [MonadUtil m]
    (generics : List $ TSyntax `noir_gen_val)
  : m $ List GenericValue := generics.mapM makeGenericVal

/--
Returns a pair of the generic kinds and the generic values as lists for the provided `generics`.

The first element of the pair is the kinds, containing a list literal as a term, while the second
element is the values, containing a HList literal as a term.
-/
partial def makeGenericValTerms [MonadUtil m]
    (generics : List $ TSyntax `noir_gen_val)
  : m ((TSyntax `term) × (TSyntax `term)) := do
  let generics ← makeGenericVals generics
  let genericKinds ← makeListLit $ ←generics.mapM fun g => quoteKind g.kind
  let genericVals ← makeHListLit $ generics.map fun g => g.value
  pure (genericKinds, genericVals)

/-- Builds the term corresponding to a generic definition, throwing an error if invalid. -/
partial def makeGenericDef [MonadUtil m] : TSyntax `noir_gen_def → m GenericDef
| `(noir_gen_def|$i:ident : $kind) => do pure ⟨i, ←makeKindValue kind⟩
| _ => throwUnsupportedSyntax

/--
Builds a list of terms where each corresponds to a generic definition, throwing an error if invalid.
-/
partial def makeGenericDefs [MonadUtil m]
    (generics: List $ TSyntax `noir_gen_def)
  : m $ List GenericDef := generics.mapM makeGenericDef

/--
Returns a pair of the generic kinds and the generic names as lists for the provided `generics`.

The first element of the pair is the kinds, containing a list literal as a term, while the second
element is the values, containing a HList literal as a term.
-/
partial def makeGenericDefTerms [MonadUtil m]
    (generics : List $ TSyntax `noir_gen_def)
  : m ((TSyntax `term) × (TSyntax `term)) := do
  let generics ← makeGenericDefs generics
  let genericKinds ← makeListLit $ ←generics.mapM fun g => quoteKind g.kind
  let genericNames ← makeHListLit $ generics.map fun g => g.name
  pure (genericKinds, genericNames)

/-- Builds the term corresponding to the provided type syntax, throwing an error if invalid. -/
partial def makeNoirType [MonadUtil m] : TSyntax `noir_type → m (TSyntax `term)
| `(noir_type|u1) => ``(Lampe.Tp.u 1)
| `(noir_type|u8) => ``(Lampe.Tp.u 8)
| `(noir_type|u16) => ``(Lampe.Tp.u 16)
| `(noir_type|u32) => ``(Lampe.Tp.u 32)
| `(noir_type|u64) => ``(Lampe.Tp.u 64)
| `(noir_type|u128) => ``(Lampe.Tp.u 128)
| `(noir_type|i1) => ``(Lampe.Tp.i 1)
| `(noir_type|i8) => ``(Lampe.Tp.i 8)
| `(noir_type|i16) => ``(Lampe.Tp.i 16)
| `(noir_type|i32) => ``(Lampe.Tp.i 32)
| `(noir_type|i64) => ``(Lampe.Tp.i 64)
| `(noir_type|i128) => ``(Lampe.Tp.i 128)
| `(noir_type|bool) => ``(Lampe.Tp.bool)
| `(noir_type|Field) => ``(Lampe.Tp.field)
| `(noir_type|String<$n:noir_gen_val>) => do
  let n_gen ← makeGenericVal n

  if n_gen.kind == .type then
    throwError "Length argument to string {n} was not a const generic"

  ``(Lampe.Tp.str $(n_gen.value))
| `(noir_type|FmtString<$n:noir_gen_val, $tp:noir_gen_val>) => do
  let n_gen ← makeGenericVal n

  if n_gen.kind == .type then
    throwError "Length argument to format string {n} was not a const generic"

  let tp := (←makeGenericVal tp).value
  ``(Lampe.Tp.fmtStr $(n_gen.value) $tp)
| `(noir_type|Unit) => `(Lampe.Tp.unit)
| `(noir_type|$i:ident) => ``($i)
| `(noir_type|&$tp) => do ``(Lampe.Tp.ref $(←makeNoirType tp))
| `(noir_type|$structName:noir_ident < $generics,* >) => do
  let nameIdent ← makeNoirIdent structName
  let genericsList := generics.getElems.toList
  let gensLen := genericsList.length

  -- Certain builtin types fall into this case and have to be handled specially.
  match nameIdent.getId.toString with
  | "Array" => do
      if gensLen != 2 then
        throwError "Array had wrong number of generic args {gensLen}"

      let elemGeneric ← makeGenericVal genericsList[0]!
      let sizeGeneric ← makeGenericVal genericsList[1]!

      if sizeGeneric.kind == .type then
        throwError "Array size {genericsList[1]!} not a const generic"

      ``(Lampe.Tp.array $(elemGeneric.value) $(sizeGeneric.value))
  | "Slice" => do
    if gensLen != 1 then
      throwError "Slice had wrong number of generic args {gensLen}"

    let elemGeneric ← makeGenericVal genericsList[0]!

    ``(Lampe.Tp.slice $(elemGeneric.value))
  | "Tuple" => do
    let generics := (←makeGenericVals genericsList).map fun g => g.value
    ``(Lampe.Tp.tuple none $(←makeListLit generics))
  | _ => do
    let structIdent := makeStructDefIdent (←makeNoirIdent structName)
    let generics := (←makeGenericVals genericsList).map fun g => g.value
    ``(Lampe.Struct.tp $structIdent $(←makeHListLit generics))
| `(noir_type|${ $i }) => pure i
| `(noir_type|λ( $param_types,* ) -> $ret:noir_type)
| `(noir_type|λ( $param_types,* ) → $ret:noir_type) => do
  let paramTypes ← makeListLit (←param_types.getElems.toList.mapM makeNoirType)
  let returnType ← makeNoirType ret
  ``(Lampe.Tp.fn $paramTypes $returnType)
| `(noir_type|@ $aliasName < $generics,* >) => do
  let generics ← makeGenericVals generics.getElems.toList
  let genericVals ← makeHListLit $ generics.map fun g => g.value
  let aliasFunc := makeTypeAliasIdent (←makeNoirIdent aliasName)
  ``($aliasFunc $genericVals)
| `(noir_type|_) => ``(_)
| t => throwError "Unsupported type syntax {t}"

end

/--
Builds the term corresponding to the builtin with the given `name`, throwing an error if invalid.
-/
def makeBuiltin [MonadUtil m] (name : String) : m (TSyntax `term) :=
  ``($(mkIdent $ (Name.mkSimple "Builtin") ++ (Name.mkSimple name)))

/-- Generates the term corresponding to a function parameter or errors if invalid. -/
def makeFuncParam [MonadUtil m]
    (param : TSyntax `noir_func_param)
  : m FuncParam := match param with
| `(noir_func_param|$name:ident : $type) => do pure ⟨name, ←makeNoirType type, False⟩
| `(noir_func_param|_ : $type) => do pure ⟨mkIdent $ Name.mkSimple "_", ←makeNoirType type, False⟩
| `(noir_func_param|mut $name:ident : $type) => do pure ⟨name, ←makeNoirType type, True⟩
| p => throwError "Encountered invalid function parameter {p}"

/-- Generates the chain of member accesses for projecting a member from a struct or tuple. -/
def makeMember [MonadUtil m] : (index : ℕ) → m (TSyntax `term)
| 0 => ``(Lampe.Builtin.Member.head)
| n + 1 => do ``(Lampe.Builtin.Member.tail $(←makeMember n))

def makeTraitDefGenericKindsIdent (traitName : Lean.Ident) : Lean.Ident :=
  mkIdent $ traitName.getId ++ (.mkSimple "#genericKinds")

def makeTraitDefAssociatedTypesKindsIdent (traitName : Lean.Ident) : Lean.Ident :=
  mkIdent $ traitName.getId ++ (.mkSimple "#associatedTypesKinds")

def makeTraitFunDefGenericKindsIdent (traitName fnName : Lean.Ident) : Lean.Ident :=
  mkIdent $ traitName.getId ++ fnName.getId ++ (.mkSimple "#genericKinds")

def makeTraitFunDefInputsIdent (traitName fnName : Lean.Ident) : Lean.Ident :=
  mkIdent $ traitName.getId ++ fnName.getId ++ (.mkSimple "#inputs")

def makeTraitFunDefOutputIdent (traitName fnName : Lean.Ident) : Lean.Ident :=
  mkIdent $ traitName.getId ++ fnName.getId ++ (.mkSimple "#output")

def makeTraitFunDefIdent (traitName fnName : Lean.Ident) : Lean.Ident :=
  mkIdent $ traitName.getId ++ fnName.getId

end Lampe

/-- Optionally matches on a `HList` literal, and returns the list of `Lean.Expr` elements -/
partial def Lean.Expr.hListLit? (e : Lean.Expr) : Option $ List Lean.Expr :=
  let rec loop (e : Lean.Expr) (acc : List Lean.Expr) :=
    if e.isAppOfArity' ``HList.nil 2 then
      some acc.reverse
    else if e.isAppOfArity' ``HList.cons 6 then
      loop e.appArg!' (e.appFn!'.appArg!' :: acc)
    else
      none
  loop e []
