import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Vector.Snoc
import Lampe.Data.Integers

namespace Lampe

def Prime : Type := {P : ℕ // Nat.Prime (P+1)}

def Prime.natVal (P : Prime) : ℕ := P.val + 1

def Fp (P : Prime) := ZMod P.natVal

instance : DecidableEq (Fp P) := inferInstanceAs (DecidableEq (ZMod P.natVal))

instance : Field (Fp P) :=
  let _ := Fact.mk P.prop
  inferInstanceAs (Field (ZMod (P.val + 1)))

instance : NeZero (Prime.natVal P) := ⟨Nat.Prime.ne_zero P.prop⟩

def numBits (P : ℕ) : ℕ := Nat.log2 P + 1

def toBaseLE (B n v : Nat): List.Vector Nat n := match n with
  | 0 => List.Vector.nil
  | n+1 => List.Vector.cons (v % B) (toBaseLE B n (v / B))

theorem toBaseLE_succ_snoc : toBaseLE B (n + 1) v = (toBaseLE B n v).snoc ((v / B^n) % B) := by
  induction n generalizing v with
  | zero =>
    simp [toBaseLE]
  | succ n ih =>
    rw [toBaseLE, ih, toBaseLE]
    simp
    congr 2
    simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem toBaseLE_take : (toBaseLE B n v).take m = toBaseLE B (min m n) v := by
  induction m generalizing v with
  | zero =>
    apply List.Vector.eq
    simp [Nat.zero_min]

theorem toBaseLE_drop : (toBaseLE B n v).drop m = toBaseLE B (n - m) (v / B^m) := by
  have : ∀B m₁ m₂ n, m₁ = m₂ → (toBaseLE B m₁ n).toList = (toBaseLE B m₂ n).toList := by
    intros B m₁ m₂ n h
    rw [h]
  by_cases h : m ≤ n
  · apply List.Vector.eq
    have : n = m + (n - m) := by simp [h]
    rw [this]
    generalize n - m = d
    clear this h n
    rw [add_comm]
    rw [this _ _ _ _ (Nat.add_sub_cancel _ _)]
    induction m generalizing v with
    | zero =>
      simp
    | succ m ih =>
      rw [←add_assoc]
      simp at ih
      simp [toBaseLE, ih, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · have t₁ : n - m = 0 := by rw [Nat.sub_eq_zero_of_le]; linarith
    apply List.Vector.eq
    rw [this _ _ _ _ t₁]
    simp
    linarith

def ofBaseLE {n} (B : Nat) (v : List.Vector Nat n) : Nat :=
  v.toList.foldr (fun bit rest => bit + B * rest) 0

@[simp]
theorem ofBaseLE_cast (h : n₁ = n₂) (v : List.Vector Nat n₁) : ofBaseLE B (h ▸ v) = ofBaseLE B v  := by
  cases h
  rfl

theorem ofBaseLE_toBaseLE: ofBaseLE B (toBaseLE B D N) = N % B^D := by
  induction D generalizing N with
  | zero => simp [Nat.mod_one, toBaseLE, ofBaseLE]
  | succ D ih =>
    simp [ofBaseLE] at ih
    simp [toBaseLE, ofBaseLE]
    rw [ih, add_comm, Nat.pow_succ]
    conv => rhs; rw [mul_comm, Nat.mod_mul, add_comm]

theorem ofBaseLE_toBaseLE_of_lt (h : N < B^D): ofBaseLE B (toBaseLE B D N) = N := by
  rw [ofBaseLE_toBaseLE, Nat.mod_eq_of_lt h]

def Fp.toBitsLE {P} n: ZMod P → List.Vector (U 1) n := fun x =>
  toBaseLE 2 n x.val |>.map (↑)

def _root_.List.Vector.chunks {n} d : List.Vector α (n * d) → List.Vector (List.Vector α d) n := match n with
| 0 => fun v => List.Vector.nil
| n + 1 => fun v =>
  have hh : min d ((n+1) * d) = d := by simp [Nat.succ_mul];
  have ht : (n + 1) * d - d = n * d := by simp [Nat.succ_mul];
  List.Vector.cons (hh ▸ v.take d) (List.Vector.chunks d (ht ▸ v.drop d))

@[simp]
theorem _root_.List.Vector.cast_toList {n m} (h : n = m) (v : List.Vector α n) : (h ▸ v).toList = v.toList := by
  cases h
  rfl

theorem toBaseLE_pow {B D K N} : toBaseLE (B^D) K N = (toBaseLE B (K*D) N |>.chunks D |>.map (ofBaseLE B)) := by
  induction K generalizing N with
  | zero =>
    simp [toBaseLE, List.Vector.chunks]
  | succ K ih =>
    simp only [toBaseLE, ih, List.Vector.chunks, List.Vector.map_cons]
    congr 1
    · have : min D ((K+1)*D) = D := by simp [Nat.succ_mul]
      rw [toBaseLE_take]
      simp
      rw [this, ofBaseLE_toBaseLE]
    · rw [toBaseLE_drop]
      congr
      have : (K + 1) * D - D = K * D := by simp [Nat.succ_mul]
      have congr: ∀B m₁ m₂ n, m₁ = m₂ → (toBaseLE B m₁ n).toList = (toBaseLE B m₂ n).toList := by
        intros B m₁ m₂ n h
        rw [h]
      apply List.Vector.eq
      simp [congr _ _ _ _ this]

def toLeBytes {P} : ZMod P → List (U 8) := fun x => go P x.val where
  go : ℕ → ℕ → List (U 8)
  | 0, _ => []
  | (k + 1), v => (v % 256) :: go ((k + 1) / 256) (v / 256)

end Lampe
