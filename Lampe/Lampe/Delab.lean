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
  match stx with
  | `(⸨ $e ⸩) => e
  | `($e) => ⟨e⟩

def extractBlock? (stx : TSyntax `nr_expr) : Option <| TSyntaxArray `nr_expr :=
  match stx with
  | `(nr_expr|{ $e;* }) => some e
  | _ => none

-- TODO: This isn't right??
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
    | `(Tp.bool) => return ⟨mkIdentFrom stx `bool⟩
    | `(Tp.field) => return ⟨mkIdentFrom stx `Field⟩
    | `(Tp.str $n) => return ←`(nr_type|str<$(← delabNrConstNum n)>)
    | `(Tp.fmtStr $n [$tps,*]) =>
      let n ← delabNrConstNum n
      let tps ← tps.getElems.mapM fun tp => ppLampeTp tp
      return ←`(nr_type| fmtstr<$n,($tps,*)>)
    | `(Tp.slice $tp) => return ←`(nr_type|[$(←ppLampeTp tp)])
    | `(Tp.array $tp $n) => return ←`(nr_type|[$(←ppLampeTp tp); $(← delabNrConstNum n)])
    -- | `(Tp.tuple $name $fields) => sorry
    -- | `(Tp.ref $tp) => sorry
    | `(Tp.fn [$argTps,*] $outTp) =>
      let argTps ← argTps.getElems.mapM fun tp => ppLampeTp tp
      `(nr_type|λ($argTps,*) → $(←ppLampeTp outTp))
    | `($id:ident) => `(nr_type|$(⟨id⟩)) -- Type variables?
    | _ => unreachable!

def ppLampeKind (stx : Syntax) : DelabM <| TSyntax `nr_kind := do
  match stx with
    | `(Kind.u $n:num) =>
      let n := n.getNat
      return ⟨mkIdentFrom stx <| .mkSimple s!"u{n}"⟩
    | `(Kind.field) => return ⟨mkIdentFrom stx `Field⟩
    -- | `(Kind.type) => sorry -- TODO: What do I do here?
    | _ => unreachable!

@[app_delab Lampe.Expr.litNum]
def delabLampeLitNum : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let args := expr.getAppArgs
  let tp ← delab args[1]!
  let num ← delab args[2]!
  return ←`(⸨$(⟨num⟩):num : $(⟨← ppLampeTp tp⟩):nr_type⸩)

@[app_delab Lampe.Expr.litStr]
def delabLampeLitStr : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let args := expr.getAppArgs
  let charListRaw := args[2]!.getAppArgs[2]!
  let charList  ← delab charListRaw
  let str := charList.raw[1].getArgs |>.filter (fun x => x.getKind == `char)
                                     |>.foldl (init := "") fun acc x => acc.push x.isCharLit?.get!
  return ←`(⸨ $(⟨Syntax.mkStrLit str⟩) ⸩)

@[app_delab Lampe.Expr.constFp]
def delabLampeConstFp : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let constName := expr.getArg! 2
  let delabedConstName ← delab constName
  let const ← `(nr_expr|f@$(⟨delabedConstName⟩))
  return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.constU]
def delabLampeConstU : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let constName := expr.getArg! 2
  let delabedConstName ← delab constName
  let const ← `(nr_expr|u@$(⟨delabedConstName⟩))
  return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.fmtStr]
def delabLampeFmtStr : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let _tps := expr.getArg! 2
  let string := expr.getArg! 3
  let fmtStr ← `(nr_expr| #format($(⟨← delab string⟩),))
  return ←`(⸨$fmtStr⸩)

@[app_delab Lampe.Expr.fn]
def delabLampeFn : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let argTps := expr.getArg! 1
  let outTp := expr.getArg! 2
  let funcRef := expr.getArg! 3

  let argTps ← match (← delab argTps) with
    | `([$tps,*]) =>
      tps.getElems.mapM fun tp => ppLampeTp tp
    | _ => pure #[]
  let outTp ← ppLampeTp (← delab outTp)


  let asdf ← `(nr_type|λ($argTps,*) → $outTp)
  -- TODO: This needs to be expanded, probably in its own function
  let funcName := match (← delab funcRef) with
    | `(FuncRef.decl $s:str [$kinds,*] h![$gens,*]) =>
      -- let kinds ← kinds.getElems.mapM fun kind => ppLampeKind kind
      -- let gens ← gens.getElems.mapM fun gen => ppLampeKind gen
      let funcName := mkIdent <| .mkSimple s.getString
      let funcName : TSyntax `nr_ident := ⟨funcName⟩
      funcName
    | _ => unreachable!

  return ←`(⸨@$funcName<> as $asdf⸩)

@[app_delab Lampe.Expr.var]
def delabLampeVar : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let val := expr.getArg! 2
  let var ← `(nr_expr|$(⟨← delab val⟩))
  return ←`(⸨$var⸩)

@[app_delab Lampe.Expr.letIn]
def delabLampeLetIn : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let val := expr.getArg! 3
  let binding := expr.getArg! 4

  let (var, body) := match (← delab binding) with
    | `(fun $var => $body) =>
       (var, body)
    | _ => unreachable!

  let body := extractInnerLampeExpr body
  let morebody := extractBlock? body

  let asdf ← if let some morebody := morebody then
    `(nr_expr| {let $(⟨var⟩) = $(extractInnerLampeExpr ⟨← delab val⟩); $morebody;*})
  else
    `(nr_expr| {let $(⟨var⟩) = $(extractInnerLampeExpr ⟨← delab val⟩); $body})
  `(⸨$asdf⸩)

@[app_delab Lampe.Expr.call]
def delabLampeCall : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let funcRef := expr.getArg! 3
  let args := expr.getArg! 4
  let args := match (← delab args) with
    | `(h![$argsss,*]) => argsss.getElems
    | _ => ⟨[]⟩
  let args ← args.mapM fun arg => do `(nr_expr|$(⟨arg⟩))
  let funcName ← delab funcRef
  let callExpr ← `(nr_expr| $(⟨funcName⟩)($args,*))
  return ←`(⸨$callExpr⸩)

@[app_delab Lampe.Expr.callBuiltin]
def delabLampeBuiltinCall : Delab := whenDelabExprOption getExpr >>= fun expr => do
  let outTp := expr.getArg! 2
  let builtin := expr.getArg! 3
  let args := expr.getArg! 4
  let args := match (← delab args) with
    | `(h![$argsss,*]) => argsss.getElems
    | _ => ⟨[]⟩
  let args ← args.mapM fun arg => do `(nr_expr|$(⟨arg⟩))
  let builtin ← delab builtin
  let builtinName := mkIdent <| builtin.raw.getId.components.reverse.head!
  let callExpr ← `(nr_expr| # $(⟨builtinName⟩)($args,*) : $(← ppLampeTp (← delab outTp)) )
  return ←`(⸨$callExpr⸩)

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
def delabSTHoare : Delab := whenDelabSTHoareOption getExpr >>= fun expr => do
  let args := expr.getAppArgs
  let preCondition ← delab args[3]!
  let lampeExpr ← delab args[4]!
  let postCondition ← delab args[5]!
  return ←`(⦃$preCondition⦄ $lampeExpr ⦃$postCondition⦄)

end STHoare

-- section testing

-- open Lampe

-- set_option trace.Meta.debug true

-- nr_def fmttest<>(x : Field, y : str<5>) -> fmtstr<12, (Field, u8)> {
--   let x = 3 : u8;
--   let y = 4 : Field;

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
--   let x = 3 : Field;
--   let y = 4 : Field;
--   #fAdd(x, y) : Field
-- }

-- example : STHoare p Γ ⟦⟧ (simple.fn.body _ h![] |>.body h![]) fun v => v = x := by
--   simp only [simple]
--   steps
--   simp_all

-- end testing
