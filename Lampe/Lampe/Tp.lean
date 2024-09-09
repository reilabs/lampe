import Mathlib

import Lampe.Data.Integers

namespace Lampe

variable (P : Nat)

inductive Kind where
| nat
| type

inductive Tp where
| u (size : Nat)
| bool
| unit
| field
| slice (element : Tp)

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
| .field => ZMod P
| .slice tp => List (denote tp)

end

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => Tp

end Lampe
