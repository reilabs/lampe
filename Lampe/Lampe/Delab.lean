import Lean
import Lampe.Syntax
import Lampe.Hoare.SepTotal
import Lampe.Tactic.Steps -- TODO: remove this import after done testing

open Lean PrettyPrinter Delaborator SubExpr

register_option Lampe.pp.Expr : Bool := {
  defValue := true
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

-- TODO: This isn't right
def delabNrConstNum (stx : Syntax) : DelabM <| TSyntax `nr_const_num := do
  match stx.getKind with
    | `num => return ←`(nr_const_num|$(⟨stx⟩))
    | `ident => return ←`(nr_const_num|$(⟨stx⟩))
    -- TODO: Need to deal with BitVec applications
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
    | `(Tp.tuple $name [$fields,*]) =>
      let fields ← fields.getElems.mapM fun tp => ppLampeTp tp
      return ←`(nr_type|`($fields,*))
    | `(Tp.ref $tp) => `(nr_type| & $(←ppLampeTp tp))
    | `(Tp.fn [$argTps,*] $outTp) =>
      let argTps ← argTps.getElems.mapM fun tp => ppLampeTp tp
      `(nr_type|λ($argTps,*) → $(←ppLampeTp outTp))
    | `($id:ident) => `(nr_type|$(⟨id⟩)) -- Type variables?
    | _ => `(nr_type|$(⟨stx⟩)) -- TODO: Catch all for other types

def ppLampeNumericKind (stx : Syntax) : DelabM <| TSyntax `ident := do
  match stx with
    | `(Kind.u $n:num) =>
      let n := n.getNat
      return mkIdentFrom stx <| .mkSimple s!"u{n}"
    | `(Kind.field) => return mkIdentFrom stx `Field
    | _ => unreachable!

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
      | `($n) =>
        return ←`(⸨$(⟨n⟩):num : $(⟨← ppLampeTp tp⟩):nr_type⸩)

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
    let constName := expr.getArg! 2
    let delabedConstName ← delab constName
    let const ← `(nr_expr|f@$(⟨delabedConstName⟩))
    return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.constU]
def delabLampeConstU : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
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

-- TODO: Finish this
def delabLampeFuncRef (stx : Syntax) : DelabM <| TSyntax `nr_funcref := do
  match stx with
    | `(FuncRef.lambda $ref) => failure
    | `(FuncRef.decl $s:str [$kinds,*] h![$gens,*]) =>
      let generics ← kinds.getElems.zip gens.getElems |>.mapM delabLampeGeneric.uncurry
      let funcName := mkIdent <| .mkSimple s.getString
      let funcName : TSyntax `nr_ident := ⟨funcName⟩
      let generics := ⟨generics⟩
      return ←`(nr_funcref|@ $funcName <$generics,*>)
    | `(FuncRef.trait $selfTp $traitName $traitKinds $traitGenerics $fnName $fnKinds $fnGenerics) =>
      failure
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
    -- TODO: This needs to be expanded, probably in its own function
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

@[app_delab Lampe.Expr.ite]
def delabLampeIte : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let cond ← delab <| expr.getArg! 2
    let thenBranch ← delab <| expr.getArg! 3
    let elseBranch ← delab <| expr.getArg! 4

    let ite ← `(nr_expr|
      if $(extractInnerLampeExpr cond) $(← ensureOneBracket <| extractInnerLampeExpr thenBranch)
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

    let (var, body) := match (← delab <| expr.getArg! 5) with
      | `(fun $var => $body) =>
        (var, body)
      | _ => unreachable!

    let loop
      ← `(nr_expr| for $(⟨var⟩) in
        $(extractInnerLampeExpr lowerBound) .. $(extractInnerLampeExpr upperBound)
          $(extractInnerLampeExpr body))
    return ←`(⸨$loop⸩)

@[app_delab Lampe.Expr.lam]
def delabLampeLam : Delab := whenDelabExprOption getExpr >>= fun expr =>
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

    -- TODO: No way this is the right way to do this
    let (args, body) ← match ← delab body with
      | `(match $_:term with | h![$args,*] => $body) =>
        pure (args.getElems, body)
      | _ => failure

    let params ← args.zip argTps |>.mapM fun (arg, tp) => do
       return ←`(nr_param_decl|$(⟨arg⟩):ident : $tp)

    let lambda ← `(nr_expr||$params,*|-> $outTp $(← ensureOneBracket <| extractInnerLampeExpr body))
    return ←`(⸨$lambda⸩)

@[app_delab Lampe.Expr.letIn]
def delabLampeLetIn : Delab := whenDelabExprOption getExpr >>= fun expr =>
  whenFullyApplied expr do
    let bindingType := expr.getArg! 1
    let val := expr.getArg! 3
    let binding := expr.getArg! 4

    let (var, body) := match (← delab binding) with
      | `(fun $var => $body) =>
        (var, body)
      | _ => unreachable!

    let body := extractInnerLampeExpr body
    let morebody := extractBlock? body

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

section STHoare

declare_syntax_cat slp_cond
declare_syntax_cat sthoare

syntax "⦃" term "⦄" : slp_cond
syntax slp_cond ppLine ppLine term ppLine ppLine slp_cond : term

register_option Lampe.pp.STHoare : Bool := {
  defValue := true
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

-- section testing

-- open Lampe

-- nr_def simple_lambda<>(x : Field, y : Field) -> Field {
--   let add = |a : Field, b : Field| -> Field { #fAdd(a, b) : Field };
--   add(x, y);
-- }

-- example {p Γ} {x y : Tp.denote p Tp.field} :
--     STHoare p Γ ⟦⟧ (simple_lambda.fn.body _ h![] |>.body h![x, y])
--     fun v => v = x + y := by
--   simp only [simple_lambda]
--   steps

--   apply STHoare.letIn_intro (Q := fun v => v = x + y)
--   . apply STHoare.ramified_frame_top (H₁ := (∃∃h, [λadd.asLambda h ↦ _]) ⋆ ⟦⟧) (Q₁ := fun v => (∃∃h, [λadd.asLambda h ↦ _]) ⋆ v = x + y)
--     apply STHoare.callLambda_intro
--     case h_ent =>
--       sl_norm
--       rw [←SLP.exists_star]
--       apply SLP.exists_intro_l
--       intro hp
--       apply SLP.exists_intro_r
--       rw [SLP.star_comm]
--       apply SLP.star_mono_l'
--       apply SLP.forall_right
--       intro
--       apply SLP.wand_intro
--       sl_norm
--       apply SLP.star_mono_l
--       apply SLP.entails_top
--     steps
--     assumption
--   · intro
--     steps
--     simp_all

-- set_option trace.Meta.debug true

-- nr_def simple_muts<>(x : Field) -> Field {
--   let mut y = x;
--   let mut z = x;
--   z = 2 : Field;
--   y = 3 : Field;
--   y
-- }

-- example : STHoare p Γ ⟦⟧ (simple_muts.fn.body _ h![] |>.body h![x]) fun v => v = x := by
--   simp only [simple_muts]
--   steps
--   simp_all

-- nr_def fmttest<>(x : Field, y : str<5>) -> fmtstr<12, (Field, u8)> {
--   let x = 3 : u8;
--   let y = -4 : Field;

--   let z = #format("hi {} bye {}", y, x);
--   z
-- }

-- nr_def testing<>(x : Field) -> Field {
--   let x = 3 : u8;
--   let y = "fun";

--   let s = (@fmttest<> as λ(Field, str<5>) → fmtstr<12, (Field, u8)>)(1 : Field, "abcde");

--   5 : Field
-- }

-- nr_def const_test<@N : u8>(x : Field) -> Field {
--   let mut res = x;
--   for _? in 0 : u8 .. u@N {
--     res = #fMul(res, 2 : Field) : Field;
--   };
--   res;
-- }

-- nr_def simple<>() -> Field {
--   let x = -13 : Field;
--   #fAdd(x, 1 : Field) : Field
-- }

-- example : STHoare p Γ ⟦⟧ (testing.fn.body _ h![] |>.body h![x]) fun v => v = x := by
--   simp only [testing]
--   steps
--   simp_all

-- end testing
