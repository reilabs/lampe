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

def toBaseLE (B n v : Nat): List Nat := match n with
  | 0 => []
  | n+1 => v % B :: toBaseLE B n (v / B)

@[simp]
lemma toBaseLE_len : (toBaseLE B n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp [toBaseLE, ih]

theorem toBaseLE_succ_snoc : toBaseLE B (n + 1) v = toBaseLE B n v ++ [(v / B^n) % B] := by
  induction n generalizing v with
  | zero =>
    simp [toBaseLE]
  | succ n ih =>
    rw [toBaseLE, ih, toBaseLE]
    simp
    congr 1
    simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem toBaseLE_take : (toBaseLE B n v).take m = toBaseLE B (min m n) v := by
  induction m generalizing v n with
  | zero =>
    simp [Nat.zero_min, toBaseLE]
  | succ m ih =>
    cases n
    · simp [toBaseLE]
    · simp [toBaseLE, Nat.succ_min_succ, ih]

theorem toBaseLE_drop : (toBaseLE B n v).drop m = toBaseLE B (n - m) (v / B^m) := by
  by_cases h : m ≤ n
  · have : n = m + (n - m) := by simp [h]
    rw [this]
    generalize n - m = d
    clear this h n
    rw [add_comm]
    induction m generalizing v with
    | zero =>
      simp
    | succ m ih =>
      rw [←add_assoc]
      simp at ih
      simp [toBaseLE, ih, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · have t₁ : n - m = 0 := by rw [Nat.sub_eq_zero_of_le]; linarith
    simp [t₁, toBaseLE]
    linarith

def ofBaseLE (B : Nat) (v : List Nat) : Nat :=
  v.foldr (fun bit rest => bit + B * rest) 0

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
  ⟨toBaseLE 2 n x.val |>.map (↑), by simp⟩

def Fp.toBytesLE {P} n : ZMod P → List.Vector (U 8) n := fun x =>
  ⟨toBaseLE 256 n x.val |>.map (↑), by simp⟩

def Fp.ofBytesLE {P} : List (U 8) → ZMod P := fun bytes =>
  ofBaseLE 256 (bytes.map BitVec.toNat)

def _root_.List.Vector.chunks {n} d : List.Vector α (n * d) → List.Vector (List.Vector α d) n := match n with
| 0 => fun v => List.Vector.nil
| n + 1 => fun v =>
  have hh : min d ((n+1) * d) = d := by simp [Nat.succ_mul];
  have ht : (n + 1) * d - d = n * d := by simp [Nat.succ_mul];
  List.Vector.cons (hh ▸ v.take d) (List.Vector.chunks d (ht ▸ v.drop d))

def _root_.List.chunksExact {n α} d (l : List α) (h : List.length l = n * d): List (List α) := match n with
| 0 => []
| n + 1 =>
  l.take d :: List.chunksExact (n := n) d (l.drop d) (by simp [h, Nat.succ_mul])

@[simp]
theorem _root_.List.Vector.cast_toList {n m} (h : n = m) (v : List.Vector α n) : (h ▸ v).toList = v.toList := by
  cases h
  rfl

theorem toBaseLE_pow {B D K N} : toBaseLE (B^D) K N = (toBaseLE B (K*D) N |>.chunksExact D (by simp; exact Or.inl rfl) |>.map (ofBaseLE B)) := by
  induction K generalizing N with
  | zero =>
    simp [toBaseLE, List.chunksExact]
  | succ K ih =>
    simp only [toBaseLE, ih, List.Vector.map_cons, Nat.succ_mul]
    congr 1
    · simp [toBaseLE_take, ofBaseLE_toBaseLE]
    · congr
      simp [toBaseLE_drop]

end Lampe
