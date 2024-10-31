import Mathlib

namespace Lampe

abbrev U (n : Nat) := BitVec (n)
abbrev I (n : Nat) := BitVec (n)

instance : DecidableEq (U n) := inferInstanceAs (DecidableEq (BitVec _))

instance : DecidableEq (I n) := inferInstanceAs (DecidableEq (BitVec _))

instance : Repr (U n) where
  reprPrec := fun a _ => a.toNat.repr

#eval ((BitVec.ofInt 8 (-128)).sdiv (BitVec.ofInt 8 (-1))).toInt

instance : Repr (I n) where
  reprPrec := fun a _ => a.toInt.repr

/-- A proposition that checks whether the integer `val` can be represented by a `w`-width bit vector in 2s complement -/
abbrev bitsCanRepresent (w : Nat) (val : Int) := val < 2^(w-1) ∧ val ≥ -2^(w-1)

end Lampe
