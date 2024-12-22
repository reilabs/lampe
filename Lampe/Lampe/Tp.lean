import Mathlib

import Lampe.Data.Integers
import Lampe.Data.Field
import Lampe.Data.HList

namespace Lampe

structure Ref where
  val : Nat
  deriving DecidableEq

variable (p : Prime)

inductive Kind where
| nat
| type

inductive Tp where
| u (size : Nat)
| i (size : Nat)
| bi -- BigInt
| bool
| unit
| str (size : U 32)
| field
| slice (element : Tp)
| array (element : Tp) (size : U 32)
| tuple (name : Option String) (fields : List Tp)
| ref (tp : Tp)
| func

inductive FnRef
| builtin (name : String)
| decl (name : String) (gs : List Tp)
| lambda (r : Nat)
| trait (traitName : String) (fnName : String) (gs : List Tp)

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
| .str n => Mathlib.Vector Char n.toNat
| .field => Fp p
| .slice tp => List (denote tp)
| .array tp n => Mathlib.Vector (denote tp) n.toNat
| .ref _ => Ref
| .tuple _ fields => denoteArgs fields
| .func => FnRef

end

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => Tp

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

def indexTpl (tpl : Tp.denoteArgs p tps) (mem : Member tp tps) : Tp.denote p tp := match tps with
| tp :: _ => match tpl, mem with
  | (h, _), .head => h
  | (_, rem), .tail m => indexTpl rem m

def exampleTuple {p} : Tp.denoteArgs p [.bool, .field, .field] := (true, 4, 5)

example : indexTpl p exampleTuple Member.head = true := rfl
example : indexTpl p exampleTuple Member.head.tail = 4 := rfl
example : indexTpl p exampleTuple Member.head.tail.tail = 5 := rfl

lemma List.replicate_head (hl : x :: xs = List.replicate n a) : x = a := by
  unfold List.replicate at hl
  aesop

lemma List.replicate_cons (hl : x :: xs = List.replicate n a) : xs = List.replicate (n-1) a := by
  unfold List.replicate at hl
  cases xs <;> aesop

@[reducible]
def HList.toList (l : HList rep tps) (_ : tps = List.replicate n tp) : List (rep tp) := match l with
| .nil => []
| .cons x xs => match tps with
  | [] => []
  | _ :: _ => ((List.replicate_head (by tauto)) ▸ x) :: (HList.toList xs (List.replicate_cons (by tauto)))

lemma HList.toList_cons :
  HList.toList (n := n + 1) (HList.cons head rem) h₁ = head :: (HList.toList (n := n) rem h₂) := by
  rfl

lemma HList.toList_length_is_n (h_same : tps = List.replicate n tp) :
  (HList.toList l h_same).length = n := by
  subst h_same
  induction n
  cases l
  tauto
  cases l
  rw [HList.toList_cons]
  simp_all
  rfl

@[reducible]
def HList.toVec (l : HList rep tps) (h_same : tps = List.replicate n tp) : Mathlib.Vector (rep tp) n :=
  ⟨HList.toList l h_same, by apply HList.toList_length_is_n⟩

end Lampe
