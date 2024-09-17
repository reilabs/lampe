import Mathlib
import Lampe.Data.Integers

namespace Lampe

def Prime : Type := {P : ℕ // Nat.Prime (P+1)}

def Prime.natVal (P : Prime) : ℕ := P.val + 1

def Fp (P : Prime) := ZMod P.natVal

-- def Fp.mk {P : Prime} (x : Nat) (hp : x < P.val) : Fp P := by
--   unfold Fp
--   rw [←Nat.succ_pred (Nat.Prime.ne_zero P.prop)]
--   apply Fin.mk x
--   have := Nat.Prime.ne_zero P.prop
--   simp only [Nat.add_one]
--   rw [Nat.succ_pred (by assumption)]
--   assumption

-- theorem fp_is_fin : Fp P = Fin P.val := by
--   unfold Fp
--   rw [←Nat.succ_pred (Nat.Prime.ne_zero P.prop)]
--   simp only [ZMod]

instance : DecidableEq (Fp P) := inferInstanceAs (DecidableEq (ZMod P.natVal))

instance : Field (Fp P) :=
  let _ := Fact.mk P.prop
  inferInstanceAs (Field (ZMod (P.val + 1)))

instance : NeZero (Prime.natVal P) := ⟨Nat.Prime.ne_zero P.prop⟩

-- def Fp.casesOn {P : Prime} {motive : Fp P → Sort u} (x : Fp P)
--   (fp : (val : Nat) → (prop : val < P.val) → motive (Fp.mk val prop)): motive x := by
--   rw [fp_is_fin] at *




-- variable (P : Prime)

-- @[simp]
-- theorem zero_lt_prime : 0 < P.val := Nat.zero_lt_of_ne_zero (Nat.Prime.ne_zero P.prop)

-- @[simp]
-- theorem one_lt_prime : 1 < P.val := Nat.Prime.one_lt P.prop

-- @[simp]
-- theorem mod_prime_lt : x % P.val < P.val := by
--   apply Nat.mod_lt
--   have := Nat.Prime.ne_zero P.prop
--   apply Nat.zero_lt_of_ne_zero (Nat.Prime.ne_zero P.prop)

-- instance : Zero (Fp P) where
--   zero := ⟨0, by simp⟩

-- instance : One (Fp P) where
--   one := ⟨1, by simp⟩



-- instance (P : Prime) : Field (Fp P) where
--   add := fun x y => ⟨(x.val + y.val) % P.val, mod_prime_lt _⟩
--   add_assoc := by
--     intro a b c
--     cases a; cases b; cases c
--     conv_lhs => whnf
--     conv_rhs => whnf
--     congr 1
--     conv in (occs := *) (Fp.val (_ + _)) => all_goals (arg 1; whnf)
--     simp [add_assoc]
--   zero := ⟨0, zero_lt_prime _⟩
--   zero_add := by
--     rintro ⟨_, _⟩
--     conv_lhs => whnf; enter [1,1,1]; whnf
--     congr 1;
--     simp only [Nat.zero_add]
--     apply Nat.mod_eq_of_lt
--     assumption
--   add_zero := by
--     rintro ⟨_, _⟩
--     conv_lhs => whnf; enter [1,1,2]; whnf
--     congr 1;
--     simp only [Nat.add_zero]
--     apply Nat.mod_eq_of_lt
--     assumption
--   nsmul := nsmulRec




def numBits (P : ℕ) : ℕ := Nat.log2 P + 1

def toLeBytes {P} : ZMod P → List (U 8) := fun x => go P x.val where
  go : ℕ → ℕ → List (U 8)
  | 0, _ => []
  | (k + 1), v => (v % 256) :: go ((k + 1) / 256) (v / 256)

def padEnd : ℕ → List (U 8) → List (U 8) := fun tgtLen xs => xs ++ (List.replicate (tgtLen - xs.length) 0)

end Lampe
