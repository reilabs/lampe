import Lean
import Lampe.Data.Meta
import Lampe.Hoare.SepTotal
import Lampe.Syntax.Elab

open Lean PrettyPrinter Delaborator SubExpr

register_option Lampe.pp.Expr : Bool := {
  defValue := false
  descr := "Pretty print Lampe.Expr using the Lampe syntax"
}

register_option Lampe.pp.STHoare : Bool := {
  defValue := false
  descr := "Pretty print Lampe.STHoare using the Lampe syntax"
}

namespace Lampe

/-- Switch whether the `Expr` delaborator fires based off the `Lampe.pp.Expr` option -/
abbrev whenDelabExprOption : DelabM α → DelabM α := whenDelabOptionSet `Lampe.pp.Expr

/-- Helper function to delaborate struct types of the form «struct#Name».tp h![⋯] -/
def delabStructTp (expr : Lean.Expr) : DelabM <| (TSyntax `noir_ident) × Lean.Expr :=
  whenFullyApplied expr do
    let struct := expr.getArg! 0
    let generics := expr.getArg! 1
    let some (name , _) := struct.const? | failure
    let nameStr := name.getString!
    return (←`(noir_ident|$(⟨mkIdent $ .mkSimple nameStr⟩)), generics)

partial def ppTp (expr : Lean.Expr) : DelabM <| TSyntax `noir_type := do
  match_expr expr with
  | Tp.u n =>
    let u := mkIdent <| .mkSimple s!"u{← ppExpr n}"
    return ← `(noir_type|$(⟨u⟩):noir_type)
  | Tp.i n =>
    let i := mkIdent <| .mkSimple s!"i{← ppExpr n}"
    return ← `(noir_type|$(⟨i⟩):noir_type)
  | Tp.field => return ⟨mkIdent `Field⟩
  | Tp.bool => return ⟨mkIdent `bool⟩
  | Tp.unit => return ⟨mkIdent `Unit⟩
  | Tp.vector tp => return ←`(noir_type|$(⟨mkIdent `Vector⟩):noir_ident<$(⟨← ppTp tp⟩)>)
  | Tp.array tp n => return ←`(noir_type|$(⟨mkIdent `Array⟩):noir_ident<$(⟨←ppTp tp⟩), $(⟨← delab n⟩)>)
  | Tp.tuple _name fields => do
      let some (_, fields) := fields.listLit? | throwError "fields in `Tp.tuple` expected to be a list lit, got {← ppExpr fields}"
      let fields ← fields.mapM fun tp => ppTp tp
      let fields ← fields.toArray.mapM fun tp => `(noir_gen_val|$tp:noir_type)
      let tupleType ←`(noir_type|$(⟨mkIdent `Tuple⟩):noir_ident <$fields,*>)

      return tupleType
  | Tp.fn argTps outTp =>
    let some (_, argTps) := argTps.listLit? | throwError "argTps in `Tp.fn` expected to be a list lit, got {← ppExpr argTps}"
    let argTps ← argTps.mapM fun tp => ppTp tp
    `(noir_type|λ($(argTps.toArray),*) → $(←ppTp outTp))
  | Tp.str n => return ←`(noir_type|String<$(⟨← delab n⟩)>)
  | Tp.fmtStr n tp =>
    let n ← delab n
    let tp ← ppTp tp
    return ←`(noir_type| FmtString<$(⟨n⟩), $(⟨tp⟩)>)
  | Tp.ref tp => `(noir_type| & $(←ppTp tp))
  | _ =>
    try
      let (head, generics) ← delabStructTp expr
      let some generics := generics.hListLit? | throwError "generics in `Tp.struct` expected to be a HList lit, got {← ppExpr generics}"
      let generics ← generics.toArray.mapM fun g => ppTp g
      return ←`(noir_type|$(⟨head⟩):noir_ident<$(⟨generics⟩),*>)
    catch
      | _ => return ←`(noir_type| $(⟨← delab expr⟩))

syntax "⸨" noir_expr "⸩" : term

/-- Because of the choice to index Lampe.Expr terms with `Prop` types rather than `Bool`s we need to
match on the `decide True` and `decide False` cases to display booleans correctly in the delaborator -/
def ppLampeBool (stx : Syntax) : DelabM <| TSyntax `noir_expr := do
  match stx with
    | `(decide True) =>
      return ←`(noir_expr| $(⟨mkIdent $ .mkSimple "#_true"⟩))
    | `(decide False) =>
      return ←`(noir_expr| $(⟨mkIdent $ .mkSimple "#_false"⟩))
    | `($v) =>
      return ←`(noir_expr|$(⟨v⟩))

/-- Extract the inner Lampe expression from a block or enclosing `⸨⋯⸩` block -/
def extractInnerLampeExpr (stx : TSyntax `term) : TSyntax `noir_expr :=
  let e := match stx with
  | `(⸨ $e ⸩) => e
  | `($e) => ⟨e⟩
  match e with
  | `(noir_expr|{$e}) => e
  | `(noir_expr|$e) => e

/-- Used to avoid situations with multiple enclosing blocks in the delaborator -/
def ensureOneBracket (stx : TSyntax `noir_expr) : DelabM <| TSyntax `noir_expr := do
  match stx with
  | `(noir_expr|{{$e;*}}) =>
    return ←`(noir_expr|{$e;*})
  | `(noir_expr|{$e;*}) =>
    return ←`(noir_expr|{$e;*})
  | `(noir_expr|$e) =>
    return ←`(noir_expr|{$e})

def extractBlock? (stx : TSyntax `noir_expr) : Option <| TSyntaxArray `noir_expr :=
  match stx with
  | `(noir_expr|{ $e;* }) => some e
  | _ => none

@[app_delab Lampe.Expr.skip]
def delabSkip : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    return ←``(⸨#_skip⸩)

@[app_delab Lampe.Expr.var]
def delabVar : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let tp := expr.getArg! 1
    if tp.isAppOf ``Lampe.Tp.unit then
      return ← ``(⸨#_skip⸩)
    else
      let val := expr.getArg! 2
      let var ← `(noir_expr|$(⟨← delab val⟩))
      return ←``(⸨$var⸩)


inductive LensStep
  | tuple (idx : Nat)
  | array (idx : TSyntax `noir_expr)
  | vector (idx : TSyntax `noir_expr)

/-- Descends through a `Member.head/tail` access pattern to determine the projection indexes -/
partial def getProjNum (stx : Syntax) (acc : Nat := 0) : DelabM <| Option Nat := do
  let headIdent := mkIdent `Builtin.Member.head
  let tailIdent := mkIdent `tail
  if stx[2] == tailIdent then
    return ← getProjNum stx[0] (acc + 1)
  else if stx == headIdent then
    return some acc
  else
    return none

partial def deconstructLens (lens : Lean.Expr) (acc : List LensStep := []) : DelabM $ List LensStep := do
  match_expr lens with
  | Lens.nil _ _ => pure acc
  | Lens.cons _ _ _ _ lens access =>
    match_expr access with
    | Access.tuple _ _ _ _ mem =>
      let some idx ← getProjNum (← delab mem) | failure
      deconstructLens lens (.tuple idx :: acc)
    | Access.array _ _ _ idx =>
      let idx := extractInnerLampeExpr (← delab idx)
      deconstructLens lens (.array idx :: acc)
    | Access.vector _ _ idx =>
      let idx := extractInnerLampeExpr (← delab idx)
      deconstructLens lens (.vector idx :: acc)
    | _ => throwError "Invalid lens access, got {← ppExpr access}"
  | _ => throwError "Invalid lens access, got {← ppExpr lens}"

/-- Helper function to build a `noir_lval` to build a lens access syntax term -/
def buildLVal (lval : TSyntax `noir_lval) (lensSteps : List LensStep) (type : TSyntax `noir_type)
    : DelabM $ TSyntax `noir_lval := do
  match lensSteps with
  | [] => pure lval
  | LensStep.tuple idx :: rest => do
    let lval ← buildLVal lval rest type
    let idxStx := Syntax.mkNatLit idx
    `(noir_lval|($lval . $idxStx : $type))
  | LensStep.array idx :: rest => do
    let lval ← buildLVal lval rest type
    `(noir_lval|($lval[$idx] : $type))
  | LensStep.vector idx :: rest => do
    let lval ← buildLVal lval rest type
    `(noir_lval|($lval[[$idx]]: $type))

@[app_delab Lampe.Expr.letIn]
def delabLetIn : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let bindingType := expr.getArg! 1
    let val := expr.getArg! 3
    let binding := expr.getArg! 4

    let (var, body) ← match (← delab binding) with
      | `(fun $var => $body) =>
        pure (var, body)
      | _ => throwError "letIn binding expected to be a lambda, got {← ppExpr binding}"

    let body := extractInnerLampeExpr body
    let morebody := extractBlock? body

    let letBinding ←
      if val.isAppOf ``Lampe.Expr.modifyLens then
        whenFullyApplied val do
          let modifiedVal ← delab <| val.getArg! 3
          let newVal ← delab <| val.getArg! 4

          let lens := val.getArg! 5
          let lensSteps ← deconstructLens lens
          let lval ← if lensSteps.isEmpty then
            `(noir_lval|$(⟨modifiedVal⟩) )
          else
            buildLVal ⟨modifiedVal⟩ lensSteps.reverse (← ppTp (val.getArg! 2))

          `(noir_expr|$lval:noir_lval = $(⟨newVal⟩))
      else if val.isAppOf ``Lampe.Expr.loop then
        whenFullyApplied val do
          `(noir_expr|$(extractInnerLampeExpr (← delab val)))
      else if val.isAppOf ``Lampe.Expr.ite then
        whenFullyApplied val do
        if bindingType.isAppOf ``Lampe.Tp.unit then
          `(noir_expr|$(extractInnerLampeExpr (← delab val)))
        else
          `(noir_expr|let $(⟨var⟩) = $(extractInnerLampeExpr (← delab val)))
      else
        `(noir_expr| let $(⟨var⟩) = $(extractInnerLampeExpr (← delab val)))
    let wholeBlock ← if let some morebody := morebody then
      `(noir_expr| {$letBinding; $morebody;*})
    else
      `(noir_expr| {$letBinding; $body})
    ``(⸨$wholeBlock⸩)

@[app_delab Lampe.FuncRef.lambda]
def delabFuncRefLambda : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let name ← delab <| expr.getArg! 2
    let some (_, argTypes) := expr.getArg! 0 |>.listLit? |
      throwError "arguments to Lambda not a list, got {← ppExpr <| expr.getArg! 0}"
    let argTypes ← argTypes.mapM (fun n => do ppTp n)
    let outType ← ppTp <| expr.getArg! 1
    let funcRef ← `(noir_funcref|($(⟨name⟩) as λ($(⟨argTypes.toArray⟩),*) → $(⟨outType⟩)))
    return ←``(⸨$(funcRef):noir_funcref⸩)

def generateGenerics (kinds generics : Lean.Expr): DelabM <| List Syntax := do
  let some (_, kinds) := kinds.listLit?
    | throwError "expected list lit generating generics, got {← ppExpr kinds}"
  let some generics := generics.hListLit?
    | throwError "expected HList lit error in generating generics, got {← ppExpr generics}"

  return ← kinds.zip generics |>.mapM fun (kind, gen) =>
    do `(noir_gen_def|$(⟨← delab gen⟩):ident : $(⟨← delab kind⟩):noir_kind)

@[app_delab Lampe.FuncRef.decl]
def delabFuncRefDecl : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let nameExpr := expr.getArg! 2
    let .strVal nameStr := nameExpr.litValue!
      | throwError "expected a string literal for function name, got {← ppExpr nameExpr}"
    let name := mkIdent $ .mkSimple nameStr
    let some (_, argTypes) := expr.getArg! 0 |>.listLit?
      | throwError "expected list lit for arg types in FuncRef.decl, got {← ppExpr <| expr.getArg! 0}"
    let argTypes ← argTypes.mapM (fun n => do ppTp n)
    let outType ← ppTp (expr.getArg! 1)

    let kinds := expr.getArg! 3
    let generics := expr.getArg! 4

    let funcGenerics ← generateGenerics kinds generics

    let funcRef ← `(noir_funcref|($(⟨name⟩)<$(⟨funcGenerics.toArray⟩),* > as λ($(argTypes.toArray),*) → $(⟨outType⟩)))
    return ←``(⸨$(funcRef):noir_funcref⸩)

@[app_delab Lampe.FuncRef.trait]
def delabFuncRefTrait : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let argTps := expr.getArg! 0
    let outTp := expr.getArg! 1
    let selfTp := expr.getArg! 2
    let traitName := expr.getArg! 3
    let traitKinds := expr.getArg! 4
    let traitGens := expr.getArg! 5
    let fnName := expr.getArg! 6
    let fnKinds := expr.getArg! 7
    let fnGens := expr.getArg! 8

    let .strVal traitName := traitName.litValue!
      | throwError "expected a string literal for trait name, got {← ppExpr traitName}"
    let traitName := mkIdent $ .mkSimple traitName

    let .strVal fnName := fnName.litValue!
      | throwError "expected a string literal for function name, got {← ppExpr fnName}"
    let fnName := mkIdent $ .mkSimple fnName

    let selfTp ← ppTp selfTp

    let some (_, argTypes) := argTps |>.listLit?
      | throwError "expected list lit for arg types in FuncRef.trait, got {← ppExpr argTps}"
    let argTypes ← argTypes.mapM (fun n => do ppTp n)
    let funcTp ← `(noir_type|λ($(argTypes.toArray),*) -> $(←ppTp outTp))

    let traitGenerics ← generateGenerics traitKinds traitGens
    let fnGenerics ← generateGenerics fnKinds fnGens

    let funcRef ← `(noir_funcref|(($selfTp as
    $(⟨traitName⟩)<$(⟨traitGenerics.toArray⟩),*>)::$(⟨fnName⟩)<$(⟨fnGenerics.toArray⟩),*> as $funcTp))
    return ←``(⸨$funcRef:noir_funcref⸩)

@[app_delab Lampe.Expr.lam]
def delabLam : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let argTps := expr.getArg! 1
    let outTp := expr.getArg! 2
    let data := expr.getArg! 3

    let some (_ , argTps) := argTps.listLit?
      | throwError "expected list lit for arg types in Lampe.Expr.lam, got {← ppExpr argTps}"
    let (args, body) ← match (←delab data) with
    | `(fun $_args:funBinder ↦ match $_args:term with | h![$args,*] => $body) => do
      pure (args, body)
    | _ => throwError "unable to parse args of Lambda"

    let funArgs ← args.getElems.zip argTps.toArray |>.mapM fun (arg, tp) => do
      `(noir_lam_param|$(⟨arg⟩):noir_pat : $(← ppTp tp))

    return ← ``(⸨fn($funArgs,*) : $(←ppTp outTp) := $(⟨extractInnerLampeExpr body⟩)⸩)

@[app_delab Lampe.Expr.fn]
def delabFn : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let funcRef := expr.getArg! 3
    delab funcRef

@[app_delab Lampe.Expr.call]
def delabCall : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let funcRef := expr.getArg! 3
    let args := expr.getArg! 4
    let args := match (← delab args) with
      | `(h![$funcArgs,*]) => funcArgs.getElems
      | _ => ⟨[]⟩
    let args ← args.mapM fun arg => do `(noir_expr|$(⟨arg⟩))
    let funcRef ← delab funcRef
    let callExpr ← `(noir_expr| $(⟨funcRef⟩):noir_funcref($args,*))
    return ←``(⸨$callExpr⸩)

@[app_delab Lampe.Expr.litNum]
def delabLitNum : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let args := expr.getAppArgs
    let tp := args[1]!
    let num ← delab args[2]!
    match num with
      | `(-$n:num) =>
        return ←``(⸨-$n:num : $(⟨← ppTp tp⟩):noir_type⸩)
      | `($n:num) =>
        return ←``(⸨$n:num : $(⟨← ppTp tp⟩):noir_type⸩)
      | `($n) =>
        return ←``(⸨$(⟨n⟩)⸩)

@[app_delab Lampe.Expr.callBuiltin]
def delabBuiltinCall : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let outTp := expr.getArg! 2
    let builtin := expr.getArg! 3
    let args := expr.getArg! 4
    let args := match (← delab args) with
      | `(h![$args,*]) => args.getElems
      | _ => ⟨[]⟩
    let args ← args.mapM fun arg => do `(noir_expr|$(⟨arg⟩))
    let builtin ← delab builtin
    let builtinName := mkIdent <| builtin.raw.getId.components.reverse.head!
    let callExpr ← `(noir_expr| (#_$(⟨builtinName⟩):ident returning $(←ppTp outTp))($args,*))
    return ←``(⸨$callExpr⸩)

@[app_delab Lampe.Expr.loop]
def delabLoop : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let lowerBound ← delab <| expr.getArg! 3
    let upperBound ← delab <| expr.getArg! 4

    let (var, body) ← match (← delab <| expr.getArg! 5) with
      | `(fun $var => $body) =>
        pure (var, body)
      | _ => throwError "Malformed Lampe.Expr.loop, body is not a lambda, got {← ppExpr <| expr.getArg! 5}"

    let loop
      ← `(noir_expr| for $(⟨var⟩) in
        $(extractInnerLampeExpr lowerBound) .. $(⟨upperBound⟩) do
          $(extractInnerLampeExpr body))
    return ←``(⸨$loop⸩)

@[app_delab Expr.modifyLens]
def delabModifyLens : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let modifiedVal ← delab <| expr.getArg! 3
    let newVal ← delab <| expr.getArg! 4
    return ←``(⸨$(⟨modifiedVal⟩):noir_lval = $(⟨newVal⟩)⸩)

@[app_delab Lampe.Expr.ite]
def delabIte : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let cond ← delab <| expr.getArg! 2
    let thenBranch ← delab <| expr.getArg! 3
    let elseBranch ← delab <| expr.getArg! 4

    let ite ← `(noir_expr|
      if $(← ppLampeBool cond) then $(← ensureOneBracket <| extractInnerLampeExpr thenBranch)
        else $(← ensureOneBracket <| extractInnerLampeExpr elseBranch))

    return ←``(⸨$ite⸩)

@[app_delab Expr.getMember]
def delabGetMember : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let elem := expr.getArg! 4
    let member := expr.getArg! 5

    let some idx ← getProjNum (← delab member)
      | throwError "can't find projection number for {← ppExpr member}"
    let idxSTx := Syntax.mkNatLit idx

    let acces ← `(noir_expr| $(⟨←delab elem⟩).$(idxSTx))
    return ←``(⸨$acces⸩)

@[app_delab Lampe.Expr.constFp]
def delabLampeConstFp : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let const ← delab <| expr.getArg! 2
    if let some num := Syntax.isNatLit? const then
      let const ← `(noir_expr|$(⟨.mkNatLit num⟩):num : Field)
      return ←``(⸨$const⸩)
    else
      let constName := expr.getArg! 2
      let delabedConstName ← delab constName
      let const ← `(noir_expr|fConst!($(⟨delabedConstName⟩) : $(⟨mkIdent `Field⟩)))
      return ←``(⸨$const⸩)

@[app_delab Lampe.Expr.constU]
def delabLampeConstU : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let const ← delab <| expr.getArg! 2
    let width := Syntax.isNatLit? (← delab <| expr.getArg! 1) |>.get!
    let width := mkIdent <| .mkSimple s!"u{width}"
    if let some num := Syntax.isNatLit? const then
      let const ← `(noir_expr|$(⟨.mkNatLit num⟩):num : $(width):ident)
      return ←``(⸨$const⸩)
    else
      let constName := expr.getArg! 2
      let delabedConstName ← delab constName
      let const ← `(noir_expr|uConst!($(⟨delabedConstName⟩) : $(width):ident))
      return ←``(⸨$const⸩)

@[app_delab Lampe.Expr.litStr]
def delabLampeLitStr : Delab := whenDelabExprOption getExpr >>= fun expr => whenFullyApplied expr do
  let args := expr.getAppArgs
  let Expr.lit (Literal.strVal noirStr) := args[2]!.getAppArgs[0]!
    | throwError "Expected string literal as argument but none found"
  return ←``(⸨ $(⟨Syntax.mkStrLit noirStr⟩) ⸩)

section STHoare

declare_syntax_cat slp_cond
declare_syntax_cat sthoare

syntax "⦃" term "⦄" : slp_cond
syntax slp_cond ppLine term ppLine slp_cond : term

/-- Switch whether the `STHoare` delaborator fires based off the `Lampe.pp.STHoare` option -/
abbrev whenDelabSTHoareOption : DelabM α → DelabM α := whenDelabOptionSet `Lampe.pp.STHoare

@[app_delab Lampe.STHoare]
def delabSTHoare : Delab := whenDelabSTHoareOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let args := expr.getAppArgs
    let preCondition ← delab args[3]!
    let lampeExpr ← delab args[4]!
    let postCondition ← delab args[5]!
    return ←``(⦃$preCondition⦄ $lampeExpr ⦃$postCondition⦄)

end STHoare
end Lampe
