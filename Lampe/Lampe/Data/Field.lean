import Mathlib
import Lampe.Data.Integers

namespace Lampe.Field

-- variable (P : Nat) [Fact (Nat.Prime P)]

def numBits (P : ℕ) : ℕ := Nat.log2 P + 1

def toLeBytes {P} : ZMod P → List (U 8) := fun x => go P x.val where
  go : ℕ → ℕ → List (U 8)
  | 0, _ => []
  | (k + 1), v => (v % 256) :: go ((k + 1) / 256) (v / 256)

def padEnd : ℕ → List (U 8) → List (U 8) := fun tgtLen xs => xs ++ (List.replicate (tgtLen - xs.length) 0)

end Lampe.Field
