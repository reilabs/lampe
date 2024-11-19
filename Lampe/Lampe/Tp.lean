import Mathlib

import Lampe.Data.Integers
import Lampe.Data.Field
import Lampe.Data.HList

namespace Lampe

structure Ref where
val : Nat
deriving DecidableEq

variable (P : Prime)

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
| struct (fields : List Tp)
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
| .field => Fp P
| .slice tp => List (denote tp)
| .array tp n => Mathlib.Vector (denote tp) n.toNat
| .ref _ => Ref
| .struct fields => Tp.denoteArgs fields

end

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => Tp

end Lampe
