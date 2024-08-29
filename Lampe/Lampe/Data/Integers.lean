import Mathlib

namespace Lampe

abbrev U (n : Nat) := Fin (2^n)

instance : DecidableEq (U n) := inferInstanceAs (DecidableEq (Fin _))

end Lampe
