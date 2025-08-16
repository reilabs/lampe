import Lean
import Lampe.Data.Integers
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Data.Strings
import Lampe.Data.Meta

-- Note: This option needs to be defined outside of any namespace for it to register correctly
register_option Lampe.pp.Tp : Bool := {
  defValue := true
  descr := "Pretty print applications of `Tp.denote`"
}

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
| fmtStr (size : U 32) (argTps : Tp)
| field
| slice (element : Tp)
| array (element: Tp) (size: U 32)
| tuple (name : Option String) (fields : List Tp)
| ref (tp : Tp)
| fn (argTps : List Tp) (outTp : Tp)
deriving BEq

inductive Kind where
| u (size : Nat)
| field
| type
deriving BEq, Nonempty

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
    cases (tpDecEq tps₁ tps₂) <;> cases h
    all_goals try { left; simp_all; }
    right; subst_vars; rfl
  case fn.fn =>
    rename_i args₁ out₁ args₂ out₂
    cases (tpDecEq out₁ out₂) <;> cases (tpsDecEq args₁ args₂)
    all_goals try { left; simp_all; }
    right; subst_vars; rfl

end

instance : DecidableEq Tp := tpDecEq

instance : DecidableEq $ List Tp := tpsDecEq

@[reducible]
def Kind.denote : Kind → Type
| .u w  => U w
| .field => Int
| .type => Tp

def kindDecEq (a b : Kind) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals try {right; rfl}
  all_goals try {left; simp_all}
  simp only [Kind.u.injEq]
  exact inferInstance

def kindsDecEq (a b : List Kind) : Decidable (a = b) := match a, b with
| [], [] => isTrue rfl
| [], _ :: _
| _ :: _, [] => isFalse (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true])
| a :: as, b :: bs => match kindDecEq a b, kindsDecEq as bs with
  | isTrue h, isTrue hs => isTrue (by simp only [h, hs])
  | isFalse h, _ => isFalse (by simp [h])
  | _, isFalse h => isFalse (by simp [h])

instance : DecidableEq Kind := kindDecEq

instance : DecidableEq $ List Kind := kindsDecEq

inductive FuncRef (argTps : List Tp) (outTp : Tp) where
| lambda (r : Ref)
| decl (fnName : String) (kinds : List Kind) (generics : HList Kind.denote kinds)
| trait (selfTp : Tp)
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
def FormatString (_len : U 32) (_argTps : Tp) := String

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
open Meta (mkAppM)

abbrev whenDelabTp : DelabM α → DelabM α := whenDelabOptionSet `Lampe.pp.Tp

/-- convert `[A, B, C, ...]` to the product `A.denote × B.denote × C.denote × ... -/
def delabDenoteArgsAux (p : Expr) (tps : List Expr) : MetaM Expr := do
  let rec loop (acc : Expr) : List Expr → MetaM Expr
  | [] => return acc
  | tp :: tps => do
    let tp ← mkAppM `Lampe.Tp.denote #[p, tp]
    loop (← mkAppM `Prod #[tp, acc]) tps
  let base ← mkAppM `Unit #[]
  loop base tps

/-- Delaborate `Tp.denote` to its defeq concrete Lean type. This improves the readability of goal
states involving `Tp.denote` -/
@[app_delab Lampe.Tp.denote]
def delabTpDenote : Delab := whenDelabTp getExpr >>= fun expr => whenFullyApplied expr do
  let_expr Tp.denote p tpExpr := expr | failure
  let tpExpr ← match_expr tpExpr with
  | Tp.field => mkAppM `Lampe.Fp #[p]
  | Tp.u n => mkAppM `Lampe.U #[n]
  | Tp.i n => mkAppM `Lampe.I #[n]
  | Tp.bi => mkAppM `Int #[]
  | Tp.bool => mkAppM `Bool #[]
  | Tp.unit => mkAppM `Unit #[]
  | Tp.str n =>
    let len ← mkAppM `BitVec.toNat #[n]
    mkAppM `FixedLenStr #[len]
  | Tp.fmtStr n tps => mkAppM `Lampe.FormatString #[n, tps]
  | Tp.slice tp => mkAppM `List #[← mkAppM `Lampe.Tp.denote #[p, tp]]
  | Tp.array tp n =>
    let len ← mkAppM `BitVec.toNat #[n]
    mkAppM `List.Vector #[← mkAppM `Lampe.Tp.denote #[p, tp], len]
  | Tp.ref _ => mkAppM `Lampe.Ref #[]
  | Tp.tuple _ fields =>
    let (_, tps) ← liftOption fields.listLit?
    delabDenoteArgsAux p tps
  | Tp.fn argTps outTp =>
    mkAppM `Lampe.FuncRef #[argTps, outTp]
  | _ => failure
  return ← delab tpExpr

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

/- In this section we provide unification hints to assist with the ergonomics of stating theorems -/
section unificationHints

/-- This is slightly dangerous, as it could conflict with the unification with `Tp.i n` -/
unif_hint (p : Prime) (n : Nat) (tp : Tp) where
  Tp.u n =?= tp
  ⊢ Tp.denote p tp =?= BitVec n

unif_hint (p : Prime) (tp : Tp) where
  Tp.bool =?= tp
  ⊢ Tp.denote p tp =?= Bool

unif_hint (p q : Prime) (tp : Tp) where
  p =?= q
  Tp.field =?= tp
  ⊢ Tp.denote p tp =?= Fin (q.val + 1)

end unificationHints

end Lampe
