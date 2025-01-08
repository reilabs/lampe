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
| fn (argTps : List Tp) (outTp : Tp)

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => Tp

inductive FuncRef (argTps : List Tp) (outTp : Tp) where
| lambda (r : Ref)
| decl (fnName : String) (kinds : List Kind) (generics : HList Kind.denote kinds)
| trait (selfTp : Tp)
  (traitName : String) (traitKinds : List Kind) (traitGenerics : HList Kind.denote traitKinds)
  (fnName : String) (fnKinds : List Kind) (fnGenerics : HList Kind.denote fnKinds)

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
| .str n => List.Vector Char n.toNat
| .field => Fp p
| .slice tp => List (denote tp)
| .array tp n => List.Vector (denote tp) n.toNat
| .ref _ => Ref
| .tuple _ fields => Tp.denoteArgs fields
| .fn argTps outTp => FuncRef argTps outTp

end

end Lampe
