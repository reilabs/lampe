import Lampe.Data.Integers
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Vector.Snoc
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

/--
The representation of the field prime for use in Lampe's model of Noir's semantics.

In particular, this is ℕ constrained to being prime and _also_ being greater than 2 as we think that
there is no sane usage of Noir with a prime so low. Additionally, we represent it internally as
`P + 1` in order to take advantage of `ZMod p` being defeq to `Fin p` if `p` is `Succ`.
-/
def Prime : Type := {P : ℕ // Nat.Prime (P + 1) ∧ P + 1 > 2}

namespace Prime

/--
Gets the value of the prime as a Nat, ensuring correctness under the representation.

Do not use `Prime.val` as this will provide a nat that is equal to `P - 1` due to our choice of
representation.
-/
def natVal (P : Prime) : ℕ := P.val + 1

/--
A helper to construct a concrete prime while handling the details of the prime representation.

It is recommended to use this function instead of trying to manually work with the details of the
`P + 1` representation we use internally.
-/
@[reducible]
def ofNat (p : ℕ) (is_prime : Nat.Prime p) (is_gt_two : p > 2) : Prime := ⟨p - 1, by
  have h1 : 1 ≤ p := by
    simp only [gt_iff_lt] at is_gt_two

    have hi : 1 < 2 := by norm_num
    have lt : 1 < p := by apply lt_trans hi is_gt_two

    apply Nat.le_of_lt
    simp_all

  have h2 : p - 1 + 1 = p := by
    simp [Nat.sub_add_cancel h1]

  apply And.intro <;> (rw [h2]; simp_all)
  ⟩

lemma prime_ne_two_pow_bits {prime : Prime} {bits : ℕ} (gt : prime.natVal > 2^bits)
  : prime.natVal ≠ 2^bits := by
  by_contra
  induction bits <;> linarith

lemma two_pow_bits_lt_prime {prime : Prime} {bits : ℕ} (gt : prime.natVal > 2^bits)
  : 2^bits < prime.natVal := by apply LE.le.lt_of_ne (by linarith) (by linarith)

/--
Certain operations in Noir are only correct when the prime has _at least_ a certain number of bits
in its representation.

Theorems that rely on this behavior should have a type-class constraint of `BitsGT p N` in their
signature, so they can only be used correctly if such an instance exists.

Note that this class is defined such that if a theorem relies on `BitsGT p M` but calls a theorem
that relies on `BitsGT p N` where `M > N`, the former instance will be sufficient.
-/
class BitsGT (prime : Prime) (bits : ℕ) where
  prime_gt : prime.natVal > 2^bits
  ne_two_pow_bits : prime.natVal ≠ 2 ^ bits := prime_ne_two_pow_bits prime_gt
  lt_prime : 2^bits < prime.natVal := two_pow_bits_lt_prime prime_gt

instance {p : Prime} : BitsGT p 0 where
  prime_gt := by
    have : p.natVal > 2 := p.prop.right
    linarith

instance {n : ℕ} {p : Prime} [BitsGT p (n + 1)] : BitsGT p n where
  prime_gt := by
    rename_i n_succ
    simp only [gt_iff_lt]
    have : 2^n ≤ 2^(n + 1) := by apply Nat.pow_le_pow_right (by linarith) (by linarith)
    linarith [n_succ.prime_gt]

end Prime

def Fp (P : Prime) := ZMod P.natVal

instance : DecidableEq (Fp P) := inferInstanceAs (DecidableEq (ZMod P.natVal))

instance : Field (Fp P) :=
  let _ := Fact.mk P.prop.left
  inferInstanceAs (Field (ZMod (P.val + 1)))

instance : NeZero (Prime.natVal P) := ⟨Nat.Prime.ne_zero P.prop.left⟩

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
    simp only [toBaseLE, ih, List.Vector.map_cons, Nat.succ_mul]
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
    simp only [ofBaseLE, List.map, List.cons_append, List.foldr_cons, ih, List.length_cons, pow_succ]
    ring

theorem Fp.cast_self {P} {p : Fp P} : (p.cast : Fp P) = p := by
  unfold ZMod.cast
  simp only [Prime.natVal]
  apply ZMod.natCast_zmod_val

lemma Fp.eq_of_val_eq {P} {x y: Fp P}: x.val = y.val → x = y := by
  simp [ZMod.val, Prime.natVal]
  exact Fin.eq_of_val_eq

end Lampe
