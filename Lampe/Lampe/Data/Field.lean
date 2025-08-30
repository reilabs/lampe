import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Vector.Snoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lampe.Data.Integers


def List.chunksExact {n α} d (l : List α) (h : List.length l = n * d): List (List α) := match n with
| 0 => []
| n + 1 =>
  l.take d :: List.chunksExact (n := n) d (l.drop d) (by simp [h, Nat.succ_mul])

@[simp]
lemma List.chunksExact_length {h : List.length l = k*d} : (List.chunksExact d l h).length = k := by
  induction k generalizing l with
  | zero => simp [chunksExact]
  | succ k ih =>
    simp [chunksExact, ih]

lemma List.getElem_chunksExact {l : List α} {h : l.length = k*d} {hi}: (List.chunksExact d l h)[i]'hi = List.ofFn fun (j : Fin d) =>
  l[d*i + j.val]'(by
    simp [h];
    simp at hi;
    cases j;
    simp;
    apply lt_of_lt_of_le (Nat.add_lt_add_left (by assumption) _)
    rw [←Nat.mul_succ, mul_comm]
    apply Nat.mul_le_mul_right
    linarith
  ) := by
  simp at hi
  induction i generalizing l k with
  | zero =>
    have : k = k - 1 + 1 := by omega
    unfold chunksExact
    split
    · contradiction
    · apply List.ext_get
      · simp
        rename l.length = (_ + 1) * d => hl
        rw [hl]
        simp [Nat.succ_mul]
      · intro n _ _
        simp
  | succ n ih =>
    unfold chunksExact
    · split
      · contradiction
      · simp
        rw [ih]
        simp [Nat.mul_succ]
        ext
        congr 1
        ring
        linarith

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
    simp [toBaseLE]
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

def Fp.toBitsLE {P} n: Fp P → List.Vector (U 1) n := fun x =>
  ⟨toBaseLE 2 n x.val |>.map (↑), by simp⟩

def Fp.toBytesLE {P} n : Fp P → List.Vector (U 8) n := fun x =>
  ⟨toBaseLE 256 n x.val |>.map (↑), by simp⟩

def Fp.ofBytesLE {P} : List (U 8) → Fp P := fun bytes =>
  ofBaseLE 256 (bytes.map BitVec.toNat)

theorem toBaseLE_pow {B D K N} : toBaseLE (B^D) K N = (toBaseLE B (K*D) N |>.chunksExact D (by simp; exact Or.inl rfl) |>.map (ofBaseLE B)) := by
  induction K generalizing N with
  | zero =>
    simp [toBaseLE, List.chunksExact]
  | succ K ih =>
    simp only [toBaseLE, ih, Nat.succ_mul]
    congr 1
    · simp [toBaseLE_take, ofBaseLE_toBaseLE]
    · congr
      simp [toBaseLE_drop]

lemma toBaseLE_elem_lt {B n i j : Nat} [hnz:NeZero B] {h} : (toBaseLE B n i)[j]'h < B := by
  induction n generalizing i j with
  | zero =>
    simp [toBaseLE]
    contradiction
  | succ n ih =>
    simp [toBaseLE]
    cases j
    · simp
      apply Nat.mod_lt
      apply Nat.zero_lt_of_ne_zero
      exact hnz.ne
    · simp [ih]

lemma ofBaseLE_append : ofBaseLE B (a ++ b) = ofBaseLE B a + B^a.length * ofBaseLE B b := by
  induction a with
  | nil => simp [ofBaseLE]
  | cons h t ih =>
    simp only [ofBaseLE] at ih
    simp only [ofBaseLE, List.cons_append, List.foldr_cons, ih, List.length_cons, pow_succ]
    ring

theorem Fp.cast_self {P} {p : Fp P} : (p.cast : Fp P) = p := by
  unfold ZMod.cast
  simp only [Prime.natVal]
  apply ZMod.natCast_zmod_val

lemma Fp.eq_of_val_eq {P} {x y: Fp P}: x.val = y.val → x = y := by
  simp [ZMod.val, Prime.natVal]
  exact Fin.eq_of_val_eq

end Lampe
