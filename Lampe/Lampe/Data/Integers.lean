import Mathlib

namespace Lampe

abbrev U (n : Nat) := BitVec (n)
abbrev I (n : Nat) := BitVec (n)

instance : DecidableEq (U n) := inferInstanceAs (DecidableEq (BitVec _))

instance : DecidableEq (I n) := inferInstanceAs (DecidableEq (BitVec _))

instance : Repr (U n) where
  reprPrec := fun a _ => a.toNat.repr

instance : Repr (I n) where
  reprPrec := fun a _ => a.toInt.repr

end Lampe
