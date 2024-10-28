import Mathlib

import Lampe.Data.Integers
import Lampe.Data.Field

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
| field
| slice (element : Tp)
| struct (fields : List Tp)
| ref (tp : Tp)

-- mutual

-- def Tp.decidableListEq : (a: List Tp) → (b: List Tp) → Decidable (a = b)
-- | [], [] => isTrue rfl
-- | a :: as, b :: bs => match Tp.decidableEq a b with
--   | isTrue h => match Tp.decidableListEq as bs with
--     | isTrue h' => isTrue (by cases h; cases h'; rfl)
--     | isFalse h' => isFalse (by intro h''; cases h''; contradiction)
--   | isFalse h => isFalse (by intro h'; cases h'; contradiction)
-- | [], b :: bs => isFalse (by intro h; cases h)
-- | a :: as, [] => isFalse (by intro h; cases h)

-- def Tp.decidableEq : (a: Tp) → (b: Tp) → Decidable (a = b)
-- | .u s, .u s' => if h : s = s' then isTrue (by cases h; rfl) else isFalse (by intro h'; cases h'; contradiction)
-- | .bool, .bool => isTrue rfl
-- | .unit, .unit => isTrue rfl
-- | .field, .field => isTrue rfl
-- | .slice tp, .slice tp' => match Tp.decidableEq tp tp' with
--   | isTrue h => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro h'; cases h'; contradiction)
-- | .ref tp, .ref tp' => match Tp.decidableEq tp tp' with
--   | isTrue h => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro h'; cases h'; contradiction)
-- | .struct fields, .struct fields' => match Tp.decidableListEq fields fields' with
--   | isTrue h => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro h'; cases h'; contradiction)

-- end


-- instance : DecidableEq Tp :=
--   fun a b => match a, b with
--   | .u s, .u s' => if h : s = s' then isTrue (by cases h; rfl) else isFalse (by intro h'; cases h'; contradiction)
--   | .bool, .bool => isTrue rfl
--   | .unit, .unit => isTrue rfl
--   | .field, .field => isTrue rfl
--   | .slice tp, .slice tp' => if h : tp = tp' then isTrue (by cases h; rfl) else isFalse (by intro h'; cases h'; contradiction)




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
