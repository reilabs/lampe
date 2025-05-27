import Lean
import Lampe.Syntax
import Lampe.Hoare.SepTotal
import Lampe.Tactic.Steps

open Lean PrettyPrinter Delaborator SubExpr

register_option Lampe.pp.Expr : Bool := {
  defValue := false
  descr := "Pretty print Lampe.Expr using the Lampe syntax"
}

def whenDelabExprOption (f : DelabM α) : DelabM α := do
  if (← getOptions).getBool `Lampe.pp.Expr true then f else failure

def whenFullyApplied (expr : Expr) (f : DelabM α) : DelabM α := do
  let numArgs := expr.getAppNumArgs
  let fType ← Meta.inferType expr.getAppFn
  let arity := fType.getNumHeadForalls
  let arity2 := fType.getNumHeadLambdas
  if numArgs == arity + arity2 then f else failure

syntax "⸨" nr_expr "⸩" : term

def extractInnerLampeExpr (stx : TSyntax `term) : TSyntax `nr_expr :=
  let e := match stx with
  | `(⸨ $e ⸩) => e
  | `($e) => ⟨e⟩
  match e with
  | `(nr_expr|{$e}) => e
  | `(nr_expr|$e) => e

def ensureOneBracket (stx : TSyntax `nr_expr) : DelabM <| TSyntax `nr_expr := do
  match stx with
  | `(nr_expr|{{$e;*}}) =>
    return ←`(nr_expr|{$e;*})
  | `(nr_expr|{$e;*}) =>
    return ←`(nr_expr|{$e;*})
  | `(nr_expr|$e) =>
    return ←`(nr_expr|{$e})

def extractBlock? (stx : TSyntax `nr_expr) : Option <| TSyntaxArray `nr_expr :=
  match stx with
  | `(nr_expr|{ $e;* }) => some e
  | _ => none

-- TODO: [#99] This isn't right
def delabNrConstNum (stx : Syntax) : DelabM <| TSyntax `nr_const_num := do
  match stx.getKind with
    | `num => return ←`(nr_const_num|$(⟨stx⟩))
    | `ident => return ←`(nr_const_num|$(⟨stx⟩))
    -- TODO: [#99] Need to deal with BitVec applications
    | _ => return ←`(nr_const_num|$(⟨stx⟩))

partial def ppLampeTp (stx : Syntax) : DelabM <| TSyntax `nr_type := do
  match stx with
    | `(Tp.u $n:num) =>
      let n := n.getNat
      return ⟨mkIdentFrom stx <| .mkSimple s!"u{n}"⟩
    | `(Tp.i $n:num) =>
      let n := n.getNat
      return ⟨mkIdentFrom stx <| .mkSimple s!"i{n}"⟩
    | `(Tp.bi) => return ⟨mkIdentFrom stx `bi⟩
    | `(Tp.bool) => return ⟨mkIdentFrom stx `bool⟩
    | `(Tp.field) => return ⟨mkIdentFrom stx `Field⟩
    | `(Tp.str $n) => return ←`(nr_type|str<$(← delabNrConstNum n)>)
    | `(Tp.fmtStr $n [$tps,*]) =>
      let n ← delabNrConstNum n
      let tps ← tps.getElems.mapM fun tp => ppLampeTp tp
      return ←`(nr_type| fmtstr<$n,($tps,*)>)
    | `(Tp.unit) => return ⟨mkIdentFrom stx `Unit⟩
    | `(Tp.slice $tp) => return ←`(nr_type|[$(←ppLampeTp tp)])
    | `(Tp.array $tp $n) => return ←`(nr_type|[$(←ppLampeTp tp); $(← delabNrConstNum n)])
    | `(Tp.tuple $_name [$fields,*]) =>
      let fields ← fields.getElems.mapM fun tp => ppLampeTp tp
      return ←`(nr_type|`($fields,*))
    | `(Tp.ref $tp) => `(nr_type| & $(←ppLampeTp tp))
    | `(Tp.fn [$argTps,*] $outTp) =>
      let argTps ← argTps.getElems.mapM fun tp => ppLampeTp tp
      `(nr_type|λ($argTps,*) → $(←ppLampeTp outTp))
    | `($id:ident) => `(nr_type|$(⟨id⟩)) -- Type variables?
    | _ => `(nr_type|$(⟨stx⟩)) -- TODO: [#99] Catch all for other types

def ppLampeNumericKind (stx : Syntax) : DelabM <| TSyntax `ident := do
  match stx with
    | `(Kind.u $n:num) =>
      let n := n.getNat
      return mkIdentFrom stx <| .mkSimple s!"u{n}"
    | `(Kind.field) => return mkIdentFrom stx `Field
    | _ => failure

def mkNrParamDecl (id : Syntax) (tp : TSyntax `nr_type): DelabM <| TSyntax `nr_param_decl := do
  let id := ⟨id⟩
  return ←`(nr_param_decl|$id:ident : $tp)

@[app_delab Lampe.Expr.litNum]
def delabLampeLitNum : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let args := expr.getAppArgs
    let tp ← delab args[1]!
    let num ← delab args[2]!
    match num with
      | `(-$n:num) =>
        return ←`(⸨-$n:num : $(⟨← ppLampeTp tp⟩):nr_type⸩)
      | `($n:num) =>
        return ←`(⸨$(⟨n⟩):num : $(⟨← ppLampeTp tp⟩):nr_type⸩)
      | `($n) =>
        return ←`(⸨$(⟨n⟩)⸩)

@[app_delab Lampe.Expr.litStr]
def delabLampeLitStr : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let args := expr.getAppArgs
    let charListRaw := args[2]!.getAppArgs[2]!
    let charList  ← delab charListRaw
    let str := charList.raw[1].getArgs |>.filter (fun x => x.getKind == `char)
                                      |>.foldl (init := "") fun acc x => acc.push x.isCharLit?.get!
    return ←`(⸨ $(⟨Syntax.mkStrLit str⟩) ⸩)

@[app_delab Lampe.Expr.constFp]
def delabLampeConstFp : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let const ← delab <| expr.getArg! 2
    if let some num := Syntax.isNatLit? const then
      let const ← `(nr_expr|$(⟨.mkNatLit num⟩):num : Field)
      return ←`(⸨$const⸩)
    else
      let constName := expr.getArg! 2
      let delabedConstName ← delab constName
      let const ← `(nr_expr|u@$(⟨delabedConstName⟩))
      return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.constU]
def delabLampeConstU : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let const ← delab <| expr.getArg! 2
    if let some num := Syntax.isNatLit? const then
      let width := Syntax.isNatLit? (← delab <| expr.getArg! 1) |>.get!
      let width := mkIdent <| .mkSimple s!"u{width}"
      let const ← `(nr_expr|$(⟨.mkNatLit num⟩):num : $(width):ident)
      return ←`(⸨$const⸩)
    else
      let constName := expr.getArg! 2
      let delabedConstName ← delab constName
      let const ← `(nr_expr|u@$(⟨delabedConstName⟩))
      return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.fmtStr]
def delabLampeFmtStr : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let _tps := expr.getArg! 2
    let string := expr.getArg! 3
    let fmtStr ← `(nr_expr| #format($(⟨← delab string⟩),))
    return ←`(⸨$fmtStr⸩)

def delabLampeGeneric (kind gen : TSyntax `term)  : DelabM <| TSyntax `nr_generic := do
  match kind with
    | `(Kind.type) =>
      return ←`(nr_generic|$(⟨←ppLampeTp gen⟩))
    | _ =>
      let kind ← ppLampeNumericKind kind
      return ←`(nr_generic|$(⟨gen⟩):num : $(⟨kind⟩))

-- TODO: [#99] Finish this
def delabLampeFuncRef (stx : Syntax) : DelabM <| TSyntax `nr_funcref := do
  match stx with
    | `(FuncRef.lambda $ref) => `(nr_funcref|@ $(⟨ref⟩))
    | `(FuncRef.decl $s:str [$kinds,*] h![$gens,*]) =>
      let generics ← kinds.getElems.zip gens.getElems |>.mapM delabLampeGeneric.uncurry
      let funcName := mkIdent <| .mkSimple s.getString
      let funcName : TSyntax `nr_ident := ⟨funcName⟩
      let generics := ⟨generics⟩
      return ←`(nr_funcref|@ $funcName <$generics,*>)
    | `(FuncRef.trait $selfTp
      $traitName:str [$traitKinds,*] h![$traitGenerics,*]
        $fnName:str [$fnKinds,*] h![$fnGenerics,*]) =>
      let selfTp ← match selfTp with
      | `(none) => `(nr_type|_)
      | `(some $selfTp) => ppLampeTp selfTp
      | _ => failure

      let traitName := mkIdent <| .mkSimple traitName.getString
      let traitGenerics ← traitKinds.getElems.zip traitGenerics.getElems |>.mapM
        delabLampeGeneric.uncurry
      let traitGenerics := ⟨traitGenerics⟩

      let fnName := mkIdent <| .mkSimple fnName.getString
      let fnGenerics ← fnKinds.getElems.zip fnGenerics.getElems |>.mapM
        delabLampeGeneric.uncurry
      let fnGenerics := ⟨fnGenerics⟩

      return ←`(nr_funcref|($selfTp:nr_type as $(⟨traitName⟩) <$traitGenerics,*>):: $(⟨fnName⟩) <$fnGenerics,*>)
    | `($v) => return ←`(nr_funcref|$(⟨v⟩)) -- Is this how we should handle already declared refs?

@[app_delab Lampe.Expr.fn]
def delabLampeFn : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let argTps := expr.getArg! 1
    let outTp := expr.getArg! 2
    let funcRef := expr.getArg! 3

    let argTps ← match (← delab argTps) with
      | `([$tps,*]) =>
        tps.getElems.mapM fun tp => ppLampeTp tp
      | _ => pure #[]
    let outTp ← ppLampeTp (← delab outTp)

    let funcType ← `(nr_type|λ($argTps,*) → $outTp)
    -- TODO: [#99] This needs to be expanded, probably in its own function
    let funcRef ← delabLampeFuncRef (← delab funcRef)

    return ←`(⸨$funcRef:nr_funcref as $funcType:nr_type⸩)

@[app_delab Lampe.Expr.var]
def delabLampeVar : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let tp := expr.getArg! 1
    if tp.isAppOf ``Lampe.Tp.unit then
      return ← `(⸨skip⸩)
    else
      let val := expr.getArg! 2
      let var ← `(nr_expr|$(⟨← delab val⟩))
      return ←`(⸨$var⸩)

@[app_delab Lampe.Expr.call]
def delabLampeCall : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let funcRef := expr.getArg! 3
    let args := expr.getArg! 4
    let args := match (← delab args) with
      | `(h![$argsss,*]) => argsss.getElems
      | _ => ⟨[]⟩
    let args ← args.mapM fun arg => do `(nr_expr|$(⟨arg⟩))
    let funcRef ← delabLampeFuncRef (← delab funcRef)
    let callExpr ← `(nr_expr| $(⟨funcRef⟩)($args,*))
    return ←`(⸨$callExpr⸩)

@[app_delab Lampe.Expr.callBuiltin]
def delabLampeBuiltinCall : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let outTp := expr.getArg! 2
    let builtin := expr.getArg! 3
    let args := expr.getArg! 4
    let args := match (← delab args) with
      | `(h![$args,*]) => args.getElems
      | _ => ⟨[]⟩
    let args ← args.mapM fun arg => do `(nr_expr|$(⟨arg⟩))
    let builtin ← delab builtin
    let builtinName := mkIdent <| builtin.raw.getId.components.reverse.head!
    let callExpr ← `(nr_expr| # $(⟨builtinName⟩)($args,*) : $(← ppLampeTp (← delab outTp)) )
    return ←`(⸨$callExpr⸩)

def ppLampeBool (stx : Syntax) : DelabM <| TSyntax `nr_expr := do
  match stx with
    | `(decide True) =>
      return ←`(nr_expr| $(⟨mkIdentFrom stx `true⟩))
    | `(decide False) =>
      return ←`(nr_expr| $(⟨mkIdentFrom stx `false⟩))
    | `($v) =>
      return ←`(nr_expr|$(⟨v⟩))

@[app_delab Lampe.Expr.ite]
def delabLampeIte : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let cond ← delab <| expr.getArg! 2
    let thenBranch ← delab <| expr.getArg! 3
    let elseBranch ← delab <| expr.getArg! 4

    let ite ← `(nr_expr|
      if $(← ppLampeBool cond) $(← ensureOneBracket <| extractInnerLampeExpr thenBranch)
        else $(← ensureOneBracket <| extractInnerLampeExpr elseBranch))

    return ←`(⸨$ite⸩)

@[app_delab Lampe.Expr.skip]
def delabLampeSkip : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    return ←`(⸨skip⸩)

@[app_delab Lampe.Expr.loop]
def delabLampeLoop : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let lowerBound ← delab <| expr.getArg! 3
    let upperBound ← delab <| expr.getArg! 4

    let (var, body) ← match (← delab <| expr.getArg! 5) with
      | `(fun $var => $body) =>
        pure (var, body)
      | _ => failure

    let loop
      ← `(nr_expr| for $(⟨var⟩) in
        $(extractInnerLampeExpr lowerBound) .. $(⟨upperBound⟩)
          $(extractInnerLampeExpr body))
    return ←`(⸨$loop⸩)

def delabLambda : DelabM <| TSyntax `nr_expr := do
  whenDelabExprOption getExpr >>= fun expr =>
    whenFullyApplied expr do
      let argTps ← delab <| expr.getArg! 1
      let outTp ← delab <| expr.getArg! 2
      let body := expr.getArg! 3
      let argTps ← match argTps with
        | `([$tps,*]) =>
          tps.getElems.mapM fun tp => ppLampeTp tp
        | _ => pure #[]
      let outTp ← ppLampeTp outTp

      let body ← Meta.lambdaTelescope body fun _ body => pure body

      -- TODO: [#99] No way this is the right way to do this
      let (args, body) ← match ← delab body with
        | `(match $_:term with | h![$args,*] => $body) =>
          pure (args.getElems, body)
        | _ => failure

      let params ← args.zip argTps |>.mapM fun (arg, tp) => do
        return ←`(nr_param_decl|$(⟨arg⟩):ident : $tp)

      `(nr_expr||$params,*|-> $outTp $(← ensureOneBracket <| extractInnerLampeExpr body))

@[app_delab Lampe.Expr.lam]
def delabLampeLam : Delab := delabLambda >>= fun lambda =>
    return ←`(⸨$lambda⸩)

@[app_delab Lampe.FuncRef.asLambda]
def delabFuncRefAsLambda : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let ref ← delab <| expr.getArg! 2
  return ←`($ref)

@[app_delab Lampe.Lambda.mk]
def delabLampeLambdaMk : Delab := delabLambda >>= fun lambda =>
    return ←`(⸨$lambda⸩)

partial def getProjNum (stx : Syntax) (acc : Nat := 0) : DelabM <| Option Nat := do
  let headIdent := mkIdent `Builtin.Member.head
  let tailIdent := mkIdent `tail
  if stx[2] == tailIdent then
    return ← getProjNum stx[0] (acc + 1)
  else if stx == headIdent then
    return some acc
  else
    return none

-- TODO: [#99] Need to handle patterns in the let binding
@[app_delab Lampe.Expr.letIn]
def delabLampeLetIn : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let bindingType := expr.getArg! 1
    let val := expr.getArg! 3
    let binding := expr.getArg! 4

    let (var, body) ← match (← delab binding) with
      | `(fun $var => $body) =>
        pure (var, body)
      | _ => failure

    let body := extractInnerLampeExpr body
    let morebody := extractBlock? body

    -- TODO: [#99] Should split this into separate functions
    let letBinding ←
      if val.isAppOf ``Lampe.Expr.ref then
        whenFullyApplied val do
          let val ← delab <| val.getArg! 2
          `(nr_expr|let mut $(⟨var⟩) = $(extractInnerLampeExpr val))
      else if val.isAppOf ``Lampe.Expr.modifyLens then
        whenFullyApplied val do
          let modifiedVal ← delab <| val.getArg! 3
          let newVal ← delab <| val.getArg! 4
          `(nr_expr|$(⟨modifiedVal⟩) = $(⟨newVal⟩))
      -- TODO: [#99] This whole section is cursed
      else if val.isAppOf ``Lampe.Expr.getLens then
        whenFullyApplied val do
          let getType := (← delab <| val.getArg! 1).raw[0]
          match getType with
            | `(Tp.tuple) =>
              let name := (←delab <| val.getArg! 1).raw[1][0]
              let noneIdent := mkIdent `none
              if name == noneIdent then
                let accessData := (← delab <| val.getArg! 4).raw[1][0][1][0]
                let projNum ← getProjNum accessData
                let val ← delab <| val.getArg! 3
                if let some projNum := projNum then
                  `(nr_expr| let $(⟨var⟩) = $(⟨val⟩) . $(⟨Syntax.mkNatLit projNum⟩))
                else
                  failure -- TODO: [#99] Handle this case, I think it's a nested accessor case?
              else
                let fieldAccessor := (← delab <| val.getArg! 4).raw[1][0][1][0][0].getId.toString
                let fieldAccessor := fieldAccessor.stripPrefix "«"
                                                |>.stripSuffix "»"
                                                |>.split (fun c => c == '#')
                let fieldName := mkIdent <| .mkSimple fieldAccessor[2]!
                let tupleName := mkIdent <| .mkSimple fieldAccessor[1]!
                let val ← delab <| val.getArg! 3
                `(nr_expr|let $(⟨var⟩) = ($(extractInnerLampeExpr val) as $(⟨tupleName⟩)<_>).$fieldName)
            | _ =>
              let accessType := (← delab <| val.getArg! 4).raw[1][0][0]
              let accessNum := (← delab <| val.getArg! 4).raw[1][0][1]
              match accessType with
                | `(Access.array) =>
                  let val ← delab <| val.getArg! 3
                  `(nr_expr|let $(⟨var⟩) = $(⟨val⟩)[$(⟨accessNum[0]⟩)])
                | `(Access.slice) =>
                  let val ← delab <| val.getArg! 3
                  `(nr_expr|let $(⟨var⟩) = $(⟨val⟩)[[$(⟨accessNum[0]⟩)]])
                | _ => failure
      else if val.isAppOf ``Lampe.Expr.readRef then
        whenFullyApplied val do
          let val := val.getArg! 3
          `(nr_expr|let $(⟨var⟩) = $(extractInnerLampeExpr (← delab val)))
      else if val.isAppOf ``Lampe.Expr.ite then
        whenFullyApplied val do
        if bindingType.isAppOf ``Lampe.Tp.unit then
          `(nr_expr|$(extractInnerLampeExpr (← delab val)))
        else
          `(nr_expr|let $(⟨var⟩) = $(extractInnerLampeExpr (← delab val)))
      else if val.isAppOf ``Lampe.Expr.loop then
        whenFullyApplied val do
          `(nr_expr|$(extractInnerLampeExpr (← delab val)))
      else
        `(nr_expr|let $(⟨var⟩) = $(extractInnerLampeExpr ⟨← delab val⟩))

    let wholeBlock ← if let some morebody := morebody then
      `(nr_expr| {$letBinding; $morebody;*})
    else
      `(nr_expr| {$letBinding; $body})
    `(⸨$wholeBlock⸩)

@[app_delab Lampe.Expr.mkArray]
def delabLampeMkArray : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    match ← delab <| expr.getArg! 3 with
      | `(h![$vals,*]) =>
        let vals ← vals.getElems.mapM fun val => do
          return ←`(nr_expr|$(⟨val⟩))
        `(⸨[$vals,*]⸩)
      | _ => failure

@[app_delab Lampe.Expr.mkRepArray]
def delabLampeMkRepArray : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let repNum ← delab <| expr.getArg! 2
    let repVal ← delab <| expr.getArg! 4
    `(⸨[$(⟨repVal⟩);$(⟨repNum⟩)]⸩)

@[app_delab Lampe.Expr.mkSlice]
def delabLampeMkSlice : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    match ← delab <| expr.getArg! 3 with
      | `(h![$vals,*]) =>
        let vals ← vals.getElems.mapM fun val => do
          return ←`(nr_expr|$(⟨val⟩))
        `(⸨&[$vals,*]⸩)
      | _ => failure

@[app_delab Lampe.Expr.mkRepSlice]
def delabLampeMkRepSlice : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let repNum ← delab <| expr.getArg! 2
    let repVal ← delab <| expr.getArg! 4
    `(⸨&[$(⟨repVal⟩);$(⟨repNum⟩)]⸩)

@[app_delab Lampe.Expr.mkTuple]
def delabLampeMkTuple : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let name? ← delab <| expr.getArg! 2
    let args ← delab <| expr.getArg! 3
    let args ← match args with
      | `(h![$args,*]) => args.getElems.mapM fun arg => do
        return ←`(nr_expr|$(⟨arg⟩))
      | _ => failure

    match name? with
      | `(some $name:str) =>
        let name := mkIdent <| .mkSimple name.getString
        return ←`(⸨$name:ident <_> { $args,* }⸩ ) -- Don't have information to fill in generics
      | `(none) => `(⸨`($args,*)⸩)
      | _ => failure

section STHoare

declare_syntax_cat slp_cond
declare_syntax_cat sthoare

syntax "⦃" term "⦄" : slp_cond
syntax slp_cond ppLine ppLine term ppLine ppLine slp_cond : term

register_option Lampe.pp.STHoare : Bool := {
  defValue := false
  descr := "Pretty print Lampe.STHoare using the Lampe syntax"
}

def whenDelabSTHoareOption (f : DelabM α) : DelabM α := do
  if (← getOptions).getBool `Lampe.pp.STHoare true then f else failure

@[app_delab Lampe.STHoare]
def delabSTHoare : Delab := whenDelabSTHoareOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let args := expr.getAppArgs
    let preCondition ← delab args[3]!
    let lampeExpr ← delab args[4]!
    let postCondition ← delab args[5]!
    return ←`(⦃$preCondition⦄ $lampeExpr ⦃$postCondition⦄)

end STHoare
