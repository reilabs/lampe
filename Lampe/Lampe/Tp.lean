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
| str (size: U 32)
| field
| slice (element : Tp)
| array (element: Tp) (size: U 32)
| tuple (name : Option String) (fields : List Tp)
| ref (tp : Tp)

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
| .tuple _ fields => Tp.denoteArgs fields

end

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => Tp

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

@[reducible]
def indexTpl (tpl : Tp.denoteArgs p tps) (mem : Member tp tps) : Tp.denote p tp := match tps with
| tp :: _ => match tpl, mem with
  | (h, _), .head => h
  | (_, rem), .tail m => indexTpl rem m

def exampleTuple {p} : Tp.denoteArgs p [.bool, .field, .field] := (true, 4, 5)

example : indexTpl p exampleTuple Member.head = true := rfl
example : indexTpl p exampleTuple Member.head.tail = 4 := rfl
example : indexTpl p exampleTuple Member.head.tail.tail = 5 := rfl

@[reducible]
def newMember (tps : List Tp) (n : Fin tps.length) : Member (tps.get n) tps := match n with
| Fin.mk .zero _ => match tps with | _ :: _ => Member.head
| Fin.mk (.succ n') _ => match tps with | _ :: tps' => Member.tail $ newMember tps' (Fin.mk n' _)

example : newMember [.bool, .field, .field] ⟨0, (by tauto)⟩ = Member.head := rfl
example : newMember [.bool, .field, .field] ⟨1, (by tauto)⟩ = Member.head.tail := rfl
example : newMember [.bool, .field, .field] ⟨2, (by tauto)⟩ = Member.head.tail.tail := rfl

end Lampe
