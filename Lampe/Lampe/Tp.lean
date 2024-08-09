import Mathlib

import Lampe.Data.Integers
import Lampe.Data.Field

namespace Lampe

structure Ref where
val : Nat

variable (P : Prime)

inductive Kind where
| nat
| type

inductive Tp where
| u (size : Nat)
| bool
| unit
| field
| slice (element : Tp)
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
| .bool => Bool
| .unit => Unit
| .field => Fp P
| .slice tp => List (denote tp)
| .ref _ => Ref
| .struct fields => Tp.denoteArgs fields

end

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => Tp

end Lampe
