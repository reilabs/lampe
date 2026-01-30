import Lampe.Data.Digits
import Lampe.Data.Integers
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

def Fp.toBitsLE {P} n: Fp P → List.Vector (U 1) n := fun x =>
  let r : Radix := (2 : Radix)
  let v := x.val % r.val ^ n
  have hv : v < r.val ^ n := by
    exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < r.val))
  (RadixVec.toDigitsLE (r := r) (d := n) ⟨v, hv⟩).map BitVec.ofFin

lemma Fp.toBitsLE_eq_toDigitsLE {P} {n} {x : Fp P} :
    Fp.toBitsLE n x =
      (RadixVec.toDigitsLE (r := (2 : Radix)) (d := n)
        ⟨x.val % (2 : Radix).val ^ n,
          by exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < (2 : Radix).val))⟩).map
        BitVec.ofFin := by
  simp [Fp.toBitsLE]

lemma Fp.toBitsLE_eq_toDigitsLE_of_lt {P} {n} {x : Fp P} (h : x.val < (2 : Radix).val ^ n) :
    Fp.toBitsLE n x =
      (RadixVec.toDigitsLE (r := (2 : Radix)) (d := n) ⟨x.val, h⟩).map BitVec.ofFin := by
  simpa [Nat.mod_eq_of_lt h] using (Fp.toBitsLE_eq_toDigitsLE (x := x) (n := n))

def Fp.toBytesLE {P} n : Fp P → List.Vector (U 8) n := fun x =>
  let r : Radix := R256
  let v := x.val % r.val ^ n
  have hv : v < r.val ^ n := by
    exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < r.val))
  (RadixVec.toDigitsLE (r := r) (d := n) ⟨v, hv⟩).map BitVec.ofFin

lemma Fp.toBytesLE_eq_toDigitsLE {P} {n} {x : Fp P} :
    Fp.toBytesLE n x =
      (RadixVec.toDigitsLE (r := R256) (d := n)
        ⟨x.val % R256.val ^ n, by exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < R256.val))⟩).map
        BitVec.ofFin := by
  simp [Fp.toBytesLE]

lemma Fp.toBytesLE_eq_toDigitsLE_of_lt {P} {n} {x : Fp P} (h : x.val < R256.val ^ n) :
    Fp.toBytesLE n x =
      (RadixVec.toDigitsLE (r := R256) (d := n) ⟨x.val, h⟩).map BitVec.ofFin := by
  simpa [Nat.mod_eq_of_lt h] using (Fp.toBytesLE_eq_toDigitsLE (x := x) (n := n))

def Fp.ofBytesLE {P} : List (U 8) → Fp P := fun bytes =>
  RadixVec.ofLimbsLE' 256 (bytes.map BitVec.toNat)

theorem Fp.cast_self {P} {p : Fp P} : (p.cast : Fp P) = p := by
  unfold ZMod.cast
  simp only [Prime.natVal]
  apply ZMod.natCast_zmod_val

lemma Fp.eq_of_val_eq {P} {x y: Fp P}: x.val = y.val → x = y := by
  simp [ZMod.val, Prime.natVal]
  exact Fin.eq_of_val_eq

end Lampe
