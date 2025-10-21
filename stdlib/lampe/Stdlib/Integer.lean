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

def two_pow_64 : BitVec 128 := 0x10000000000000000

def split64 (a : BitVec 128) : (BitVec 64 × BitVec 64 × Unit) :=
  let lo := a.truncate 64
  let hi := (a / two_pow_64).truncate 64
  (lo, hi, ())

def combine64 (a : BitVec 64 × BitVec 64 × Unit) : BitVec 128 :=
  (a.1.zeroExtend 128) + (a.2.1.zeroExtend 128) * two_pow_64

lemma combine64_split64_id (a : BitVec 128) : combine64 (split64 a) = a := by
  simp_all only [split64, combine64, two_pow_64]
  bv_decide

lemma split64_combine64_id (a : BitVec 64 × BitVec 64 × Unit) : split64 (combine64 a) = a := by
  simp only [split64, combine64, two_pow_64]
  rcases a with ⟨fst, snd, _⟩
  simp only [Prod.mk.injEq]
  bv_decide

lemma split64_fst_toNat {a : BitVec 128} : (split64 a).1.toNat = a.toNat % 2^64 := by
  simp [split64]

lemma split64_snd_toNat {a : BitVec 128} : (split64 a).2.1.toNat = a.toNat / 2^64 := by
  have : a.toNat / 2^64 < 2^64 := by omega
  simp_all [split64, two_pow_64]

-- TODO Remove after updating to 4.22.0 or later.
theorem BitVec.ofNat_sub_ofNat_of_le (x y : Nat) (hy : y < 2 ^ w) (hlt : y ≤ x):
    BitVec.ofNat w x - BitVec.ofNat w y = BitVec.ofNat w (x - y) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hy, show 2 ^ w - y + x = 2 ^ w + (x - y) by omega, Nat.add_mod_left]

