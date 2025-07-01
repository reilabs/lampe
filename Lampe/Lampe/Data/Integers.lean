import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

namespace Lampe

abbrev U (n : Nat) := BitVec (n)
abbrev I (n : Nat) := BitVec (n)

instance : DecidableEq (U n) := inferInstanceAs (DecidableEq (BitVec _))

instance : DecidableEq (I n) := inferInstanceAs (DecidableEq (BitVec _))

instance : Repr (U n) where
  reprPrec := fun a _ => a.toNat.repr

example : (BitVec.ofInt 8 (-128)).sdiv (BitVec.ofInt 8 (-1)) = -128 := by rfl

instance : Repr (I n) where
  reprPrec := fun a _ => a.toInt.repr

/-- A proposition that checks whether the integer `val` can be represented by a `w`-width bit vector in 2s complement -/
abbrev bitsCanRepresent (w : Nat) (val : Int) := val < 2^(w-1) ∧ val ≥ -2^(w-1)

end Lampe

instance : Fintype (BitVec 1) where
  elems := ⟨[0#1, 1#1], by simp⟩
  complete := by
    intro v
    rcases v with ⟨v⟩
    fin_cases v <;> simp

lemma BitVec.ofNat_1_eq_mod :  BitVec.ofNat 1 (x % 2) = BitVec.ofNat 1 x := by
  unfold BitVec.ofNat
  apply congrArg
  unfold Fin.ofNat
  simp

lemma BitVec.ofNat_1_eq_0_iff : 0#1 = BitVec.ofNat 1 x ↔ x % 2 = 0 := by
  apply Iff.intro
  · unfold BitVec.ofNat
    intro h
    injection h with h
    simp [Fin.ofNat] at h
    assumption
  · intro h
    unfold BitVec.ofNat
    apply BitVec.eq_of_toFin_eq
    simp only
    simp [Fin.ofNat, h]

lemma BitVec.ofNat_1_eq_1_iff : 1#1 = BitVec.ofNat 1 x ↔ x % 2 = 1 := by
  apply Iff.intro
  · unfold BitVec.ofNat
    intro h
    injection h with h
    simp [Fin.ofNat] at h
    assumption
  · intro h
    unfold BitVec.ofNat
    apply BitVec.eq_of_toFin_eq
    simp only
    simp [Fin.ofNat, h]
