import Lean
import Lampe.Syntax
import Lampe.Hoare.SepTotal
import Lampe.Tactic.Steps -- TODO: remove this import after done testing

open Lean PrettyPrinter Delaborator SubExpr

register_option Lampe.pp.Expr : Bool := {
  defValue := true
  descr := "Pretty print Lampe.Expr using the Lampe syntax"
}

syntax "⸨" nr_expr "⸩" : term

def extractInnerLampeExpr (stx : Syntax) : Syntax :=
  match stx with
  | `(⸨ $e ⸩) => e
  | _ => unreachable!

def delabNrConstNum (stx : Syntax) : DelabM <| TSyntax `nr_const_num := do
  sorry

partial def ppLampeTp (stx : Syntax) : DelabM <| TSyntax `nr_type := do
  match stx with
    | `(Tp.u $n:num) =>
      let n := n.getNat
      return ⟨mkIdentFrom stx <| .mkSimple s!"u{n}"⟩
    | `(Tp.bool) => return ⟨mkIdentFrom stx `bool⟩
    | `(Tp.field) => return ⟨mkIdentFrom stx `Field⟩
    | `(Tp.str $n) => return ←`(nr_type|str<$(← delabNrConstNum n)>)
    -- | `(Tp.fmtStr $n $tps) => sorry
    | `(Tp.slice $tp) => return ←`(nr_type|[$(←ppLampeTp tp)])
    | `(Tp.array $tp $n) => return ←`(nr_type|[$(←ppLampeTp tp); $(← delabNrConstNum n)])
    -- | `(Tp.tuple $name $fields) => sorry
    -- | `(Tp.ref $tp) => sorry
    -- | `(Tp.fn $argTps $outTp) => sorry
    | _ => unreachable!

def ppLampeKind (stx : Syntax) : DelabM <| TSyntax `nr_kind := do
  match stx with
    | `(Kind.u $n:num) =>
      let n := n.getNat
      return ⟨mkIdentFrom stx <| .mkSimple s!"u{n}"⟩
    | `(Kind.field) => return ⟨mkIdentFrom stx `Field⟩
    -- | `(Kind.type) => sorry
    | _ => unreachable!

@[app_delab Lampe.Expr.litNum]
def delabLampeLitNum : Delab := do
  let expr ← getExpr
  let args := expr.getAppArgs
  let tp ← delab args[1]!
  let num ← delab args[2]!
  return ←`(⸨$(⟨num⟩):num : $(⟨← ppLampeTp tp⟩):nr_type⸩)

@[app_delab Lampe.Expr.litStr]
def delabLampeLitStr : Delab := do
  let expr ← getExpr
  let args := expr.getAppArgs
  let charListRaw := args[2]!.getAppArgs[2]!
  let charList  ← delab charListRaw
  let str := charList.raw[1].getArgs |>.filter (fun x => x.getKind == `char)
                                     |>.foldl (init := "") fun acc x => acc.push x.isCharLit?.get!
  return ←`(⸨ $(⟨Syntax.mkStrLit str⟩) ⸩)

@[app_delab Lampe.Expr.constFp]
def delabLampeConstFp : Delab := do
  let expr ← getExpr
  let constName := expr.getArg! 2
  let delabedConstName ← delab constName
  let const ← `(nr_expr|f@$(⟨delabedConstName⟩))
  return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.constU]
def delabLampeConstU : Delab := do
  let expr ← getExpr
  let constName := expr.getArg! 2
  let delabedConstName ← delab constName
  let const ← `(nr_expr|u@$(⟨delabedConstName⟩))
  return ←`(⸨$const⸩)

@[app_delab Lampe.Expr.fmtStr]
def delabLampeFmtStr : Delab := do
  sorry

section STHoare

declare_syntax_cat slp_cond
declare_syntax_cat sthoare

syntax "⦃" term "⦄" : slp_cond
syntax slp_cond ppLine ppLine term ppLine ppLine slp_cond : term

register_option Lampe.pp.STHoare : Bool := {
  defValue := true
  descr := "Pretty print Lampe.STHoare using the Lampe syntax"
}

@[app_delab Lampe.STHoare]
def delabSTHoare : Delab := do
  let expr ← getExpr
  let args := expr.getAppArgs
  let preCondition ← delab args[3]!
  let lampeExpr ← delab args[4]!
  let postCondition ← delab args[5]!
  return ←`(⦃$preCondition⦄ $lampeExpr ⦃$postCondition⦄)

end STHoare

section testing

open Lampe

set_option trace.Meta.debug true

nr_def testing<>(x : Field) -> Field {
  let x = 3 : u8;
  let y = "fun";

  for i in 0 : u8 .. 1 : u8 {
    let t = 0 : u8;
  };
  5 : Field
}

nr_def const_test<@N : u8>(x : Field) -> Field {
  let mut res = x;
  for _? in 0 : u8 .. u@N {
    res = #fMul(res, 2 : Field) : Field;
  };
  res;
}

example : STHoare p Γ ⟦⟧ (const_test.fn.body _ h![N] |>.body h![x]) fun v => v = x := by
  simp only [const_test]
  steps
  simp_all

end testing
