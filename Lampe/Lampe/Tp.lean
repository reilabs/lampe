import Lean
import Lampe.Data.Integers
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Data.Strings
import Lampe.Data.Meta

namespace Lampe

structure Ref where
  val : Nat
deriving DecidableEq

variable (p : Prime)

inductive Tp where
| u (size : Nat)
| i (size : Nat)
| bi -- BigInt
| bool
| unit
| str (size: U 32)
| fmtStr (size : U 32) (argTps : List Tp)
| field
| slice (element : Tp)
| array (element: Tp) (size: U 32)
| tuple (name : Option String) (fields : List Tp)
| ref (tp : Tp)
| fn (argTps : List Tp) (outTp : Tp)

inductive Kind where
| u (size : Nat)
| field
| type

mutual

def tpsDecEq (a b : List Tp) : Decidable (a = b) := match a, b with
| [], [] => isTrue rfl
| [], _ :: _ => isFalse (by simp)
| _ :: _, [] => isFalse (by simp)
| tp₁ :: tps₁, tp₂ :: tps₂ => match tpDecEq tp₁ tp₂, tpsDecEq tps₁ tps₂ with
  | isTrue _, isTrue _ => isTrue (by subst_vars; rfl)
  | isFalse _, _ => isFalse (by simp_all)
  | _, isFalse _ => isFalse (by simp_all)

def tpDecEq (a b : Tp) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals try { right; rfl }
  all_goals try { left; simp_all }
  all_goals try {
    rename_i n₁ n₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases h
    . left
      simp_all
    . right
      tauto
  }
  all_goals try {
    rename_i tp₁ tp₂
    cases (tpDecEq tp₁ tp₂)
    . left
      simp_all
    . right
      tauto
  }
  case array.array =>
    rename_i tp₁ n₁ tp₂ n₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases (tpDecEq tp₁ tp₂) <;> cases h
    all_goals try {left; simp_all}
    right
    subst_vars
    rfl
  case tuple.tuple =>
    rename_i n₁ tps₁ n₂ tps₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases (tpsDecEq tps₁ tps₂) <;> cases h
    all_goals try { left; simp_all; }
    right; subst_vars; rfl
  case fmtStr.fmtStr => -- TODO: Is there a way of combining this with the above?
    rename_i n₁ tps₁ n₂ tps₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases (tpsDecEq tps₁ tps₂) <;> cases h
    all_goals try { left; simp_all; }
    right; subst_vars; rfl
  case fn.fn =>
    rename_i args₁ out₁ args₂ out₂
    cases (tpDecEq out₁ out₂) <;> cases (tpsDecEq args₁ args₂)
    all_goals try { left; simp_all; }
    right; subst_vars; rfl

end

instance : DecidableEq Tp := tpDecEq

@[reducible]
def Kind.denote : Kind → Type
| .u w  => U w
| .field => Int
| .type => Tp

inductive FuncRef (argTps : List Tp) (outTp : Tp) where
| lambda (r : Ref)
| decl (fnName : String) (kinds : List Kind) (generics : HList Kind.denote kinds)
| trait (selfTp : Option Tp)
  (traitName : String) (traitKinds : List Kind) (traitGenerics : HList Kind.denote traitKinds)
  (fnName : String) (fnKinds : List Kind) (fnGenerics : HList Kind.denote fnKinds)

def FuncRef.isLambda : FuncRef a o → Bool
| FuncRef.lambda _ => true
| _ => false

def FuncRef.asLambda {a o} (f : FuncRef a o) (h : FuncRef.isLambda f) : Ref :=
  match h' : f with
  | FuncRef.lambda r => r
  | FuncRef.decl _ _ _ => by cases h
  | FuncRef.trait _ _ _ _ _ _ _ => by cases h

/-- TODO: Actually implement this at some point -/
def FormatString (_len : U 32) (_argTps : List Tp) := String

mutual

@[reducible]
def Tp.denoteArgs : List Tp → Type
| [] => Unit
| tp :: tps => denote tp × denoteArgs tps

@[reducible]
def Tp.denote : Tp → Type
| .u n => U n
| .i n => I n
| .bi => Int
| .bool => Bool
| .unit => Unit
| .str n => FixedLenStr n.toNat
| .fmtStr n tps => FormatString n tps
| .field => Fp p
| .slice tp => List (denote tp)
| .array tp n => List.Vector (denote tp) n.toNat
| .ref _ => Ref
| .tuple _ fields => Tp.denoteArgs fields
| .fn argTps outTp => FuncRef argTps outTp

end

section Delab

open Lean PrettyPrinter Delaborator SubExpr

register_option pp.Tp : Bool := {
  defValue := true
  descr := "Pretty print applications of `Tp.denote`"
}

abbrev whenDelabTp : DelabM α → DelabM α := whenDelabOptionSet ``Lampe.pp.Tp

/-- Delaborate `Tp.denote` to its defeq concrete Lean type. This improves the readability of goal
states involving `Tp.denote` -/
partial def delabTpDenoteAux (expr : Lean.Expr) (depth maxDepth : Nat) : DelabM Term := do
  let reducedExpr := (← Meta.unfold expr `Lampe.Tp.denote).expr
  if reducedExpr.isAppOf `Lampe.Tp.denote then
    failure
  else if maxDepth ≤ depth then
    return (← delab (← Meta.reduceAll reducedExpr))
  else
    return ←delabTpDenoteAux reducedExpr depth.succ maxDepth

@[app_delab Lampe.Tp.denote]
def delabTpDenote : Delab := whenDelabTp getExpr >>= fun expr =>
  whenFullyApplied expr <| delabTpDenoteAux expr 0 10

end Delab

@[reducible]
def HList.toTuple (hList : HList (Tp.denote p) tps) (name : Option String) : Tp.denote p <| .tuple name tps := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toTuple args name⟩

mutual

def Tp.zeroArgs (args : List Tp) : HList (Tp.denote p) args :=
  match args with
  | [] => h![]
  | a :: b => .cons a.zero (Tp.zeroArgs b)

def Tp.zero (tp : Tp) : Tp.denote p tp :=
match tp with
| .u _ | .i _ | .bi | .field => 0
| .bool => False
| .unit => ()
| .str n => List.Vector.replicate n.toNat '\x00'
| .fmtStr _ _ => ""
| .slice _ => []
| .array tp n => List.Vector.replicate n.toNat tp.zero
| .ref _ => ⟨0⟩
| .tuple name fields => HList.toTuple p (Tp.zeroArgs fields) name
| .fn _ _ => .lambda ⟨0⟩

end

end Lampe
