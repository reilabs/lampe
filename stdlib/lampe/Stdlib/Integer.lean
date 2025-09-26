import Lampe

namespace Lampe.Stdlib.Integer

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

def min (a b : BitVec n) : BitVec n := if a < b then a else b

@[simp]
theorem min_ofNatLE 
  : min (BitVec.ofNatLT a ha) (BitVec.ofNatLT b hb) = BitVec.ofNatLT (a.min b) (by simp_all) := by
  unfold min
  split <;> simp_all [BitVec.lt_def, Nat.min_def, Nat.le_of_lt]

@[simp]
theorem compare_ofNatLT 
  : compare (BitVec.ofNatLT a ha) (BitVec.ofNatLT b hb) = compare a b := by
  simp [compare, compareOfLessAndEq, BitVec.lt_def, BitVec.ofNatLT]

