import Lampe.Data.Field
import Lampe.Crypto.Bn254
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tonelli–Shanks square root over the BN254 scalar field

`sqrt : Fp p → Option (Fp p)` for `p` carrying the BN254 scalar-prime
instance `[Lampe.Crypto.Bn254.Prime p]`. Returns `some y` with
`y * y = a` when `a` is a quadratic residue, `none` otherwise.

Plain Tonelli–Shanks specialised to BN254 (where `r - 1 = 2^28 · q'`
with `q'` odd). Proved correct: TS produces a square root on
QR inputs; the Euler gate short-circuits to `none` on
non-residues.

References:
- Tonelli, *Bemerkung über die Auflösung quadratischer Congruenzen*, 1891.
- Shanks, *Five number-theoretic algorithms*, 1972.
- https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm
-/

namespace Lampe.Crypto.Bn254.Sqrt

open Lampe

/-! ### BN254 scalar-field constants

The BN254 scalar-field prime is

```
r := 21888242871839275222246405745257275088548364400416034343698204186575808495617
```

with `r - 1 = 2^28 * q'` and `q'` odd; The smallest quadratic non-residue is `5`. -/

/-- 2-adic valuation of `r_scalar - 1`. -/
def twoAdicity : Nat := 28

/-- The odd part of `r - 1`, i.e. `q' = (r - 1) / 2^28`. -/
def oddPart : Nat :=
  81540058820840996586704275553141814055101440848469862132140264610111

/-- A quadratic non-residue modulo `r`. -/
def nonResidue : Nat := 5

/-- Verification: `q'` is odd. -/
theorem oddPart_odd : oddPart % 2 = 1 := by
  unfold oddPart
  decide

/-! ### Square-and-multiply exponentiation

Fast modular exponentiation on `ZMod n` via repeated squaring, with a
bounded `fuel` argument. The hot path in `tonelliCandidate` (and the
`nonResidue_euler` verification below) uses this so the kernel sees an
`O(log exp)` structural recursion on `fuel` instead of the
`O(exp)` recursion of `Monoid.npow`.

Defined generically over `ZMod n` rather than over `Fp p`: every
`Fp p`-typed argument works via the definitional equality
`Fp p := ZMod p.natVal`, and `nonResidue_euler` (which doesn't have a
`Lampe.Prime` in scope) can use the same definition. -/

/-- Recursive square-and-multiply, structural on `fuel`. Provably equal
to `base ^ exp` whenever `exp < 2^fuel`. -/
def fpowR {n : Nat} (base : ZMod n) (exp fuel : Nat) : ZMod n :=
  match fuel with
  | 0 => 1
  | fuel + 1 =>
      let half := fpowR (base * base) (exp / 2) fuel
      if exp % 2 = 1 then base * half else half

/-- When `fuel` exceeds the bit-length of the exponent, `fpowR` agrees
with the monoid power `base ^ exp`. -/
theorem fpowR_eq_pow {n : Nat} (base : ZMod n) :
    ∀ (exp fuel : Nat), exp < 2 ^ fuel → fpowR base exp fuel = base ^ exp := by
  intro exp fuel
  induction fuel generalizing base exp with
  | zero =>
      intro h
      have : exp = 0 := by
        have : exp < 1 := by simpa using h
        omega
      subst this
      simp [fpowR]
  | succ fuel ih =>
      intro h
      have hhalf : exp / 2 < 2 ^ fuel := by
        have hpow : (2 : Nat) ^ (fuel + 1) = 2 * 2 ^ fuel := by
          rw [pow_succ, Nat.mul_comm]
        rw [hpow] at h
        exact Nat.div_lt_of_lt_mul h
      have ih' := ih (base * base) (exp / 2) hhalf
      unfold fpowR
      rw [ih']
      have hsq : (base * base) ^ (exp / 2) = base ^ (2 * (exp / 2)) := by
        rw [show (base * base) = base ^ 2 from by ring, ← pow_mul, Nat.mul_comm]
      rw [hsq]
      by_cases hpar : exp % 2 = 1
      · have hexp : exp = 2 * (exp / 2) + 1 := by
          have := Nat.div_add_mod exp 2
          omega
        simp [hpar]
        conv_rhs => rw [hexp]
        rw [pow_succ, mul_comm (base ^ _) base]
      · have hexp : exp = 2 * (exp / 2) := by
          have := Nat.div_add_mod exp 2
          have : exp % 2 = 0 := by omega
          omega
        simp [hpar]
        conv_rhs => rw [hexp]

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 1024 in
/-- Verification: 5 is a quadratic non-residue mod `r`. Rewritten via
`fpowR` so the kernel sees a 512-step structural recursion instead of
the 2^253-step `Monoid.npow` recursion. Each step is ~254-bit `ZMod`
arithmetic. -/
theorem nonResidue_euler :
    (nonResidue : ZMod r_scalar) ^ ((r_scalar - 1) / 2) = -1 := by
  rw [← fpowR_eq_pow (nonResidue : ZMod r_scalar) _ 512
        (by have h1 : (r_scalar - 1) / 2 < 2 ^ 254 := by unfold r_scalar; decide
            have h2 : (2 : Nat) ^ 254 ≤ 2 ^ 512 :=
              Nat.pow_le_pow_right (by decide) (by decide)
            omega)]
  unfold nonResidue r_scalar
  decide

/-! ### Tonelli–Shanks: candidate root computation

We express Tonelli–Shanks as a structurally-recursive function on
`fuel`. The outer fuel is at most `twoAdicity = 28` (each iteration strictly
decreases `M`). The inner search for the smallest `i ∈ [1, M)` with
`t^(2^i) = 1` is also expressed recursively. -/

/-- Inner search: given a current power `acc = t^(2^i)`, find the
smallest `j ≥ i` with `t^(2^j) = 1`, bounded by `M`. Returns
`M` if no such `j` exists in `[i, M)`. -/
def findOrder {p : Lampe.Prime} (acc : Fp p) (i M fuel : Nat) : Nat :=
  match fuel with
  | 0 => M
  | fuel + 1 =>
      if i ≥ M then M
      else if acc = 1 then i
      else findOrder (acc * acc) (i + 1) M fuel

/-- One outer iteration of the Tonelli–Shanks loop. Given `(M, c, t, R)`
with `t ≠ 1`, computes the next quadruple. If no admissible inner
index exists (no `i ∈ [1, M)` with `t^(2^i) = 1`), returns the input
unchanged; the `sqrt` post-verification rules out false positives. -/
def tsStep {p : Lampe.Prime} (M : Nat) (c t R : Fp p) :
    Nat × Fp p × Fp p × Fp p :=
  let iFound := findOrder (t * t) 1 M M
  if iFound ≥ M then (M, c, t, R)
  else
    -- b = c^(2^(M - iFound - 1))
    let b : Fp p := fpowR c (2 ^ (M - iFound - 1)) (M + 1)
    let M' := iFound
    let c' := b * b
    let t' := t * (b * b)
    let R' := R * b
    (M', c', t', R')

/-- Tonelli–Shanks main loop. Each outer iteration strictly decreases
`M`, so `twoAdicity = 28` iterations suffice. -/
def tonelliLoop {p : Lampe.Prime} (a : Fp p) (fuel : Nat) (M : Nat) (c t R : Fp p) : Fp p :=
  match fuel with
  | 0 => R
  | fuel + 1 =>
      if t = 1 then R
      else
        let (M', c', t', R') := tsStep M c t R
        tonelliLoop a fuel M' c' t' R'

/-- Tonelli–Shanks candidate. Computes the initial state, then runs
`tonelliLoop` for `twoAdicity = 28` iterations. -/
def tonelliCandidate {p : Lampe.Prime} [Lampe.Crypto.Bn254.Prime p] (a : Fp p) : Fp p :=
  let c0 : Fp p := fpowR ((nonResidue : Fp p)) oddPart 512
  let t0 : Fp p := fpowR a oddPart 512
  let R0 : Fp p := fpowR a ((oddPart + 1) / 2) 512
  tonelliLoop a twoAdicity twoAdicity c0 t0 R0

/-! ### Euler's criterion (Mathlib bridge)

For a finite field `F` of odd characteristic, `a` is a square iff
`a ^ (Fintype.card F / 2) = 1` (`FiniteField.isSquare_iff`). We
specialise that to `Fp p` with `[Lampe.Crypto.Bn254.Prime p]`, using the fact that
`r_scalar` is odd to turn `Fintype.card F / 2 = r_scalar / 2` into the
exponent `(r_scalar - 1) / 2` that classical references use. -/

/-- `r_scalar` is odd; needed to align `r / 2` with `(r - 1) / 2`. -/
theorem r_scalar_odd : r_scalar % 2 = 1 := by
  unfold r_scalar
  decide

/-- `r_scalar` is not equal to `2`; needed to conclude
`ringChar (Fp p) ≠ 2` from `p.natVal = r_scalar`. -/
theorem r_scalar_ne_two : r_scalar ≠ 2 := by
  unfold r_scalar
  decide

/-- For a non-zero `a : Fp p` with `[Lampe.Crypto.Bn254.Prime p]`, the existence of
a square root implies the Euler character `a ^ ((r_scalar - 1)/2) = 1`. -/
theorem euler_one_of_exists_sqrt {p : Lampe.Prime} [hBn : Lampe.Crypto.Bn254.Prime p]
    {a : Fp p} (ha : a ≠ 0) (h : ∃ y : Fp p, y * y = a) :
    a ^ ((r_scalar - 1) / 2) = 1 := by
  have hcard : Fintype.card (Fp p) = r_scalar := by
    have : Fintype.card (Fp p) = p.natVal := by
      simp [ZMod.card p.natVal]
    rw [this, hBn.natVal_eq_r_scalar]
  have hchar : ringChar (Fp p) ≠ 2 := by
    have : ringChar (Fp p) = p.natVal := by
      simpa using ZMod.ringChar_zmod_n p.natVal
    rw [this, hBn.natVal_eq_r_scalar]
    exact r_scalar_ne_two
  have hsq : IsSquare a := by
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy.symm⟩
  have hpow : a ^ (Fintype.card (Fp p) / 2) = 1 :=
    (FiniteField.isSquare_iff (F := Fp p) hchar ha).mp hsq
  have hodd_div : r_scalar / 2 = (r_scalar - 1) / 2 := by
    have hodd := r_scalar_odd
    omega
  have hexp : Fintype.card (Fp p) / 2 = (r_scalar - 1) / 2 := by
    rw [hcard]; exact hodd_div
  rw [hexp] at hpow
  exact hpow

/-! ### Public `sqrt`

`sqrt` gates Tonelli–Shanks behind an Euler-criterion check so that
non-quadratic-residue inputs return `none` in `O(log r)` field
operations. On QR inputs, Tonelli–Shanks is *proved* to return a
correct square root, so the post-verification `R * R = a` always
succeeds. -/

/-- Tonelli–Shanks square root with an Euler-criterion gate.

Returns `some y` with `y * y = a` whenever `a` is a quadratic
residue (including `a = 0`), and `none` otherwise.

Algorithmic structure:
1. If `a = 0`, return `some 0`.
2. Compute `χ := a ^ ((r - 1) / 2)` via fast exponentiation. If
   `χ ≠ 1`, return `none` (Euler's criterion: `a` is not a QR).
3. Otherwise run Tonelli–Shanks and verify the candidate by squaring.
4. If verification fails (mathematically impossible on a QR input),
   return `none`. -/
def sqrt {p : Lampe.Prime} [Lampe.Crypto.Bn254.Prime p] (a : Fp p) : Option (Fp p) :=
  if a = 0 then
    some 0
  else
    let chi := fpowR a ((r_scalar - 1) / 2) 512
    if chi ≠ 1 then
      none
    else
      let R := tonelliCandidate a
      if R * R = a then
        some R
      else
        none

theorem fpowR_euler_eq_pow {p : Lampe.Prime} (a : Fp p) :
    fpowR a ((r_scalar - 1) / 2) 512 = a ^ ((r_scalar - 1) / 2) := by
  apply fpowR_eq_pow
  have h1 : (r_scalar - 1) / 2 < 2 ^ 254 := by unfold r_scalar; decide
  have h2 : (2 : Nat) ^ 254 ≤ 2 ^ 512 := by
    apply Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact lt_of_lt_of_le h1 h2

/-! ### Correctness -/

/-- Soundness of `sqrt`: a `some` result squares to the input.
Model-fidelity assurance for the `sqrt` definition; has no
downstream consumers by design. -/
theorem sqrt_correct {p : Lampe.Prime} [Lampe.Crypto.Bn254.Prime p] {a y : Fp p}
    (h : sqrt a = some y) : y * y = a := by
  unfold sqrt at h
  by_cases hz : a = 0
  · simp [hz] at h
    simp [hz, ← h]
  · simp [hz] at h
    by_cases hEuler : fpowR a ((r_scalar - 1) / 2) 512 = 1
    · simp [hEuler] at h
      by_cases hv : tonelliCandidate a * tonelliCandidate a = a
      · simp [hv] at h
        rw [← h]
        exact hv
      · simp [hv] at h
    · simp [hEuler] at h

/-! ### Completeness: the Tonelli–Shanks correctness proof

This is the heart of the file. We show that on a QR input,
`tonelliCandidate a * tonelliCandidate a = a`. The proof goes via
a loop invariant `TSInv` that is preserved by `tsStep` and witnesses
the desired equation at termination. -/

/-- The Tonelli–Shanks loop invariant.

At every iteration with state `(M, c, t, R)` for input `a`, we have:

- `R * R = a * t` (the candidate squared, modulo `t`)
- `t^(2^(M-1)) = 1`  (so `ord t` divides `2^(M-1)`)
- `c^(2^(M-1)) = -1` (so `c` has order exactly `2^M`)
- `1 ≤ M`

The fourth conjunct keeps the third meaningful (otherwise `M - 1`
underflows in `Nat`). -/
structure TSInv {p : Lampe.Prime} (a : Fp p) (M : Nat) (c t R : Fp p) : Prop where
  Msq : R * R = a * t
  tpow : t ^ (2 ^ (M - 1)) = 1
  cpow : c ^ (2 ^ (M - 1)) = -1
  Mge : 1 ≤ M

/-! ### Initial state: TSInv holds at `(twoAdicity, c0, t0, R0)`

We need:
- `R0 * R0 = a * t0`  where `R0 = a^((q'+1)/2)`, `t0 = a^q'`. Since
  `q' + 1` is even, `(q'+1)/2 + (q'+1)/2 = q'+1`, and `R0² = a^(q'+1) = a · a^q' = a · t0`.
- `t0^(2^(twoAdicity-1)) = 1`. This is the Euler condition: `t0^(2^(twoAdicity-1)) = a^(q' · 2^(twoAdicity-1)) = a^((r-1)/2)`, which equals `1` because `a` is a QR.
- `c0^(2^(twoAdicity-1)) = -1`. This is `nonResidue^(q' · 2^(twoAdicity-1)) = nonResidue^((r-1)/2) = -1` by `nonResidue_euler`.
-/

/-- Key identity: `q' · 2^(twoAdicity - 1) = (r_scalar - 1) / 2`. -/
theorem oddPart_mul_two_pow_eq : oddPart * 2 ^ (twoAdicity - 1) = (r_scalar - 1) / 2 := by
  unfold oddPart twoAdicity r_scalar
  decide

/-- `nonResidue_euler` transported to `Fp p` when `p.natVal = r_scalar`.

Done by viewing the goal as an equality between `Eq.mpr`-cast versions of
the corresponding `ZMod r_scalar` statement. -/
theorem nonResidue_euler_fp {p : Lampe.Prime} [hBn : Lampe.Crypto.Bn254.Prime p] :
    (nonResidue : Fp p) ^ ((r_scalar - 1) / 2) = -1 := by
  have hp : p.natVal = r_scalar := hBn.natVal_eq_r_scalar
  have hzn : (nonResidue : ZMod r_scalar) ^ ((r_scalar - 1) / 2) = -1 := nonResidue_euler
  have hpsym : r_scalar = p.natVal := hp.symm
  have hcast : (ZMod p.natVal) = (ZMod r_scalar) := by rw [hp]
  revert hzn
  rw [hpsym]
  intro hzn
  exact hzn

theorem c0_inv_pow {p : Lampe.Prime} [hBn : Lampe.Crypto.Bn254.Prime p] :
    ((nonResidue : Fp p) ^ oddPart) ^ (2 ^ (twoAdicity - 1)) = -1 := by
  rw [← pow_mul, oddPart_mul_two_pow_eq]
  exact nonResidue_euler_fp

theorem t0_pow_eq_one {p : Lampe.Prime} [hBn : Lampe.Crypto.Bn254.Prime p]
    {a : Fp p} (ha : a ≠ 0) (hQR : ∃ y : Fp p, y * y = a) :
    (a ^ oddPart) ^ (2 ^ (twoAdicity - 1)) = 1 := by
  rw [← pow_mul, oddPart_mul_two_pow_eq]
  exact euler_one_of_exists_sqrt ha hQR

theorem R0_sq {p : Lampe.Prime} (a : Fp p) :
    (a ^ ((oddPart + 1) / 2)) * (a ^ ((oddPart + 1) / 2)) = a * (a ^ oddPart) := by
  rw [← pow_add]
  have heven : (oddPart + 1) % 2 = 0 := by
    have hq := oddPart_odd
    omega
  have hsum : (oddPart + 1) / 2 + (oddPart + 1) / 2 = oddPart + 1 := by
    have := Nat.div_add_mod (oddPart + 1) 2
    omega
  rw [hsum, pow_succ, mul_comm]

theorem tsInv_init {p : Lampe.Prime} [hBn : Lampe.Crypto.Bn254.Prime p]
    {a : Fp p} (ha : a ≠ 0) (hQR : ∃ y : Fp p, y * y = a) :
    TSInv a twoAdicity
      ((nonResidue : Fp p) ^ oddPart)
      (a ^ oddPart)
      (a ^ ((oddPart + 1) / 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact R0_sq a
  · exact t0_pow_eq_one ha hQR
  · exact c0_inv_pow
  · unfold twoAdicity; decide

/-! ### Step preservation

The hardest piece: one iteration of `tsStep` preserves `TSInv` and
strictly decreases `M`. The key lemma is that from `t ≠ 1` and
`t^(2^(M-1)) = 1`, we can find a least `i ∈ [1, M)` with `t^(2^i) = 1`.
This `i` is the new `M'`.
-/

/-- Specification of `findOrder`: given `acc = t^(2^i)`, `findOrder acc i M fuel`
returns some `j ∈ [i, M]` such that, if `j < M`, then `t^(2^j) = 1`, and `j`
is the smallest such index. Requires `fuel ≥ M - i`. -/
theorem findOrder_spec {p : Lampe.Prime} (t : Fp p) :
    ∀ (fuel : Nat) (i M : Nat), M ≤ i + fuel → i ≤ M →
      let j := findOrder (t ^ (2 ^ i)) i M fuel
      i ≤ j ∧ j ≤ M ∧
        (j < M → t ^ (2 ^ j) = 1) ∧
        (∀ k, i ≤ k → k < j → t ^ (2 ^ k) ≠ 1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i M hfuel hStart
      simp only [findOrder]
      have hi_eq : i = M := by omega
      refine ⟨hStart, le_refl _, ?_, ?_⟩
      · intro h; omega
      · intro k hk hkM; omega
  | succ fuel ih =>
      intro i M hfuel hStart
      simp only [findOrder]
      by_cases hiM : i ≥ M
      · rw [if_pos hiM]
        refine ⟨hStart, le_refl _, ?_, ?_⟩
        · intro h; omega
        · intro k hk hkM; omega
      · rw [if_neg hiM]
        by_cases hacc : t ^ (2 ^ i) = 1
        · rw [if_pos hacc]
          refine ⟨le_refl _, by omega, ?_, ?_⟩
          · intro _; exact hacc
          · intro k hk hkM; omega
        · rw [if_neg hacc]
          have hi1 : i + 1 ≤ M := by omega
          have hfuel' : M ≤ (i + 1) + fuel := by omega
          have hpow : (t ^ (2 ^ i)) * (t ^ (2 ^ i)) = t ^ (2 ^ (i + 1)) := by
            rw [← pow_add, pow_succ]
            congr 1
            ring
          rw [hpow]
          have ih' := ih (i + 1) M hfuel' hi1
          simp only at ih'
          obtain ⟨hi1j, hjM, hjfound, hjmin⟩ := ih'
          refine ⟨by omega, hjM, hjfound, ?_⟩
          intro k hk hkM
          by_cases hki : k = i
          · subst hki; exact hacc
          · have hkge : i + 1 ≤ k := by omega
            exact hjmin k hkge hkM

theorem findOrder_init_spec {p : Lampe.Prime} (t : Fp p) (M : Nat) (hM : 1 ≤ M) :
    let j := findOrder (t * t) 1 M M
    1 ≤ j ∧ j ≤ M ∧
      (j < M → t ^ (2 ^ j) = 1) ∧
      (∀ k, 1 ≤ k → k < j → t ^ (2 ^ k) ≠ 1) := by
  have heq : t * t = t ^ (2 ^ 1) := by
    show t * t = t ^ 2
    ring
  rw [heq]
  exact findOrder_spec t M 1 M (by omega) hM

/-- If `t ≠ 1`, `t^(2^(M-1)) = 1`, `c^(2^(M-1)) = -1`, and `M ≥ 1`, then the
inner search finds a `j ∈ [1, M)`. -/
theorem findOrder_found_of_tsInv {p : Lampe.Prime}
    {a : Fp p} {M : Nat} {c t R : Fp p} (inv : TSInv a M c t R)
    (ht : t ≠ 1) :
    let j := findOrder (t * t) 1 M M
    1 ≤ j ∧ j < M ∧ t ^ (2 ^ j) = 1 ∧
      (∀ k, 1 ≤ k → k < j → t ^ (2 ^ k) ≠ 1) := by
  have hspec := findOrder_init_spec t M inv.Mge
  obtain ⟨h1, hM, hfound, hmin⟩ := hspec
  -- We need to rule out j = M.
  -- If j = M, then we never found, meaning all k ∈ [1, M) satisfy t^(2^k) ≠ 1.
  -- But t^(2^(M-1)) = 1 from invariant.
  -- If M = 1, then t^(2^0) = t = 1, contradiction with t ≠ 1.
  -- If M ≥ 2, then M - 1 ∈ [1, M), so the search must find at most M - 1.
  by_cases hM1 : M = 1
  · subst hM1
    -- TSInv has t^(2^0) = 1, i.e., t = 1, contradiction.
    have : t = 1 := by
      have := inv.tpow
      simpa using this
    exact absurd this ht
  · have hM2 : M ≥ 2 := by omega
    have hMm1 : M - 1 < M := by omega
    have hMm1_pos : 1 ≤ M - 1 := by omega
    -- Suppose findOrder returns M.
    -- Then for all k ∈ [1, M), t^(2^k) ≠ 1, contradicting t^(2^(M-1)) = 1.
    set j := findOrder (t * t) 1 M M with hjdef
    have hjM : j ≤ M := hM
    by_cases hjeqM : j = M
    · -- contradiction: hmin says no k < M = j satisfies, but inv.tpow does
      have := hmin (M - 1) hMm1_pos (by omega)
      exact absurd inv.tpow this
    · have hjltM : j < M := lt_of_le_of_ne hjM hjeqM
      exact ⟨h1, hjltM, hfound hjltM, hmin⟩

/-! ### Algebraic step lemmas

Given the invariants and the found index `j = M' < M`, we now check
that the new state `(M', c', t', R')` produced by `tsStep` satisfies
`TSInv`. The arithmetic facts we need:

Let `b = c^(2^(M - j - 1))`. Then:
- `c' = b² = c^(2^(M - j))`. We show `c'^(2^(M' - 1)) = -1`, i.e.,
  `c^(2^(M - j) · 2^(M' - 1)) = c^(2^(M - 1)) = -1`. This holds because
  `(M - j) + (M' - 1) = (M - j) + (j - 1) = M - 1`.
- `t' = t · b²`. We show `t'^(2^(M' - 1)) = 1`, i.e.,
  `t^(2^(M' - 1)) · c^(2^(M - 1)) = 1`. We have `t^(2^(M' - 1)) = t^(2^(j - 1))`.
  Squaring this gives `t^(2^j) = 1`, so `t^(2^(j - 1))` is a square root of 1,
  i.e., ±1. We must rule out +1 by the minimality of `j`: `t^(2^(j-1)) ≠ 1`.
  So `t^(2^(j - 1)) = -1`, and the product is `(-1) · (-1) = 1`.
- `R' = R · b`. We show `R'² = R² · b² = (a · t) · b² = a · (t · b²) = a · t'`.
-/

private theorem t_half_sq_eq_one {p : Lampe.Prime} {t : Fp p} {j : Nat} (hj : 1 ≤ j)
    (ht : t ^ (2 ^ j) = 1) : (t ^ (2 ^ (j - 1))) ^ 2 = 1 := by
  rw [← pow_mul]
  have hpow : 2 ^ (j - 1) * 2 = 2 ^ j := by
    have : j = (j - 1) + 1 := by omega
    conv_rhs => rw [this]
    rw [pow_succ]
  rw [hpow]; exact ht

private theorem sq_eq_one_imp_pm_one {p : Lampe.Prime} {x : Fp p} (h : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  have hfact : (x - 1) * (x + 1) = 0 := by
    have hid : (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    rw [hid, h]; ring
  rcases mul_eq_zero.mp hfact with h1 | h2
  · left
    have : x = 1 := by
      have : x - 1 + 1 = 0 + 1 := by rw [h1]
      linear_combination h1
    exact this
  · right
    have : x = -1 := by linear_combination h2
    exact this

/-- `t^(2^(j-1))` is `-1` when `j` is the minimal positive index with `t^(2^j) = 1`
and `t ≠ 1`. (The case `j = 1` uses `t ≠ 1` to rule out the `+1` branch.) -/
private theorem t_half_eq_neg_one_of_min {p : Lampe.Prime} {t : Fp p} {j : Nat} (hj : 1 ≤ j)
    (ht1 : t ≠ 1) (ht : t ^ (2 ^ j) = 1) (hmin : ∀ k, 1 ≤ k → k < j → t ^ (2 ^ k) ≠ 1) :
    t ^ (2 ^ (j - 1)) = -1 := by
  have hsq := t_half_sq_eq_one hj ht
  rcases sq_eq_one_imp_pm_one hsq with h1 | hneg
  · -- t^(2^(j-1)) = 1; need contradiction.
    by_cases hj1 : j = 1
    · subst hj1
      -- t^(2^0) = t = 1, contradicts t ≠ 1
      simp at h1
      exact absurd h1 ht1
    · -- j ≥ 2: hmin (j-1) gives contradiction with h1
      have h1' : t ^ (2 ^ (j - 1)) ≠ 1 := hmin (j - 1) (by omega) (by omega)
      exact absurd h1 h1'
  · exact hneg

/-! ### Step preservation: one `tsStep` preserves `TSInv` and decreases `M`. -/

/-- The auxiliary `b` value used by `tsStep` equals `c ^ (2 ^ (M - j - 1))`. -/
private theorem tsStep_b_eq {p : Lampe.Prime} (c : Fp p) (M j : Nat) (hjlt : j < M) :
    fpowR c (2 ^ (M - j - 1)) (M + 1) = c ^ (2 ^ (M - j - 1)) := by
  apply fpowR_eq_pow
  -- 2 ^ (M - j - 1) < 2 ^ (M + 1): since M - j - 1 ≤ M - 1 < M + 1.
  apply Nat.pow_lt_pow_right (by decide : 1 < 2)
  omega

/-- Step preservation: `tsStep` preserves `TSInv` and gives a strictly smaller `M`. -/
theorem tsStep_preserves {p : Lampe.Prime}
    {a : Fp p} {M : Nat} {c t R : Fp p}
    (inv : TSInv a M c t R) (ht : t ≠ 1) :
    let (M', c', t', R') := tsStep M c t R
    TSInv a M' c' t' R' ∧ M' < M := by
  -- Unpack invariants.
  have hRsq := inv.Msq
  have htpow := inv.tpow
  have hcpow := inv.cpow
  have hMge := inv.Mge
  -- Find the inner index.
  have hfound := findOrder_found_of_tsInv inv ht
  set j := findOrder (t * t) 1 M M with hjdef
  obtain ⟨hj1, hjltM, htj, hjmin⟩ := hfound
  -- Compute tsStep with the found j.
  simp only [tsStep, ← hjdef]
  rw [if_neg (by omega : ¬ j ≥ M)]
  -- Define b.
  have hb_eq : fpowR c (2 ^ (M - j - 1)) (M + 1) = c ^ (2 ^ (M - j - 1)) :=
    tsStep_b_eq c M j hjltM
  rw [hb_eq]
  set b : Fp p := c ^ (2 ^ (M - j - 1)) with hbdef
  -- Now the state is (j, b*b, t*(b*b), R*b).
  -- Show TSInv a j (b*b) (t*(b*b)) (R*b).
  refine ⟨⟨?_, ?_, ?_, hj1⟩, hjltM⟩
  -- (1) R' * R' = a * t'.
  · -- (R*b) * (R*b) = (R*R) * (b*b) = a*t * (b*b) = a * (t * (b*b)).
    have : (R * b) * (R * b) = (R * R) * (b * b) := by ring
    rw [this, hRsq]
    ring
  -- (2) t'^(2^(j-1)) = 1.
  · -- t' = t * (b*b), t'^(2^(j-1)) = t^(2^(j-1)) * (b*b)^(2^(j-1))
    -- = t^(2^(j-1)) * c^(2^(M-1))
    -- = (-1) * (-1) = 1, since t^(2^(j-1)) = -1 by minimality and c^(2^(M-1)) = -1 by inv.
    have h_thalf : t ^ (2 ^ (j - 1)) = -1 :=
      t_half_eq_neg_one_of_min hj1 ht htj hjmin
    -- Compute (b*b)^(2^(j-1)) = c^(2^(M-1)) = -1.
    have hbb_pow : (b * b) ^ (2 ^ (j - 1)) = -1 := by
      -- (b*b)^(2^(j-1)) = b^(2 * 2^(j-1)) = b^(2^j) = c^(2^(M-j-1) * 2^j) = c^(2^(M-1))
      have hbb : b * b = b ^ 2 := by ring
      rw [hbb, ← pow_mul]
      have hexp : 2 * 2 ^ (j - 1) = 2 ^ j := by
        have hjsucc : j = (j - 1) + 1 := by omega
        conv_rhs => rw [hjsucc]
        rw [pow_succ, Nat.mul_comm]
      rw [hexp]
      -- Goal: b^(2^j) = -1, where b = c^(2^(M-j-1)).
      rw [hbdef, ← pow_mul]
      -- Goal: c^(2^(M-j-1) * 2^j) = -1.
      have hexp2 : 2 ^ (M - j - 1) * 2 ^ j = 2 ^ (M - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hexp2]
      exact hcpow
    -- Now expand t'^(2^(j-1)).
    have : (t * (b * b)) ^ (2 ^ (j - 1)) =
           t ^ (2 ^ (j - 1)) * (b * b) ^ (2 ^ (j - 1)) := by
      rw [mul_pow]
    rw [this, h_thalf, hbb_pow]
    ring
  -- (3) c'^(2^(j-1)) = -1.
  · -- c' = b*b, c'^(2^(j-1)) = b^(2 * 2^(j-1)) = b^(2^j) = c^(2^(M-1)) = -1.
    have hbb : b * b = b ^ 2 := by ring
    rw [hbb, ← pow_mul]
    have hexp : 2 * 2 ^ (j - 1) = 2 ^ j := by
      have hjsucc : j = (j - 1) + 1 := by omega
      conv_rhs => rw [hjsucc]
      rw [pow_succ, Nat.mul_comm]
    rw [hexp, hbdef, ← pow_mul]
    have hexp2 : 2 ^ (M - j - 1) * 2 ^ j = 2 ^ (M - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hexp2]
    exact hcpow

/-! ### Loop termination

The loop terminates within `twoAdicity` iterations and produces `R` with `R*R = a`. -/

/-- If `TSInv a M c t R` and `t = 1`, then `R * R = a`. -/
theorem tsInv_terminal {p : Lampe.Prime} {a : Fp p} {M : Nat} {c t R : Fp p}
    (inv : TSInv a M c t R) (ht : t = 1) : R * R = a := by
  have := inv.Msq
  rw [ht, mul_one] at this
  exact this

/-- The main loop preserves the invariant and terminates: after enough fuel,
the result `R` satisfies `R * R = a`. We do strong induction on `M` (which
decreases each non-terminal iteration). -/
theorem tonelliLoop_correct {p : Lampe.Prime} {a : Fp p} :
    ∀ (fuel : Nat) (M : Nat) (c t R : Fp p),
      TSInv a M c t R → M ≤ fuel →
      let R' := tonelliLoop a fuel M c t R
      R' * R' = a := by
  intro fuel
  induction fuel with
  | zero =>
      intro M c t R inv hM
      -- M ≤ 0 means M = 0, but M ≥ 1 from invariant. Contradiction.
      have : M ≥ 1 := inv.Mge
      omega
  | succ fuel ih =>
      intro M c t R inv hM
      simp only [tonelliLoop]
      by_cases ht : t = 1
      · rw [if_pos ht]
        exact tsInv_terminal inv ht
      · rw [if_neg ht]
        -- Apply tsStep_preserves.
        have hstep := tsStep_preserves inv ht
        -- Destructure the tsStep result.
        rcases hstep_eq : tsStep M c t R with ⟨M', c', t', R'⟩
        rw [hstep_eq] at hstep
        simp only at hstep
        obtain ⟨inv', hMlt⟩ := hstep
        have hM' : M' ≤ fuel := by omega
        exact ih M' c' t' R' inv' hM'

set_option exponentiation.threshold 1024 in
/-- Tonelli–Shanks candidate, applied to a QR input, squares to the input. -/
theorem tonelliCandidate_sq {p : Lampe.Prime} [Lampe.Crypto.Bn254.Prime p]
    {a : Fp p} (ha : a ≠ 0) (hQR : ∃ y : Fp p, y * y = a) :
    tonelliCandidate a * tonelliCandidate a = a := by
  unfold tonelliCandidate
  -- oddPart has ~226 bits; bridge via 2^254 to dodge the kernel's
  -- exponentiation threshold for `decide`.
  have h_bridge : (2 : Nat) ^ 254 ≤ 2 ^ 512 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hq : oddPart < 2 ^ 512 :=
    lt_of_lt_of_le (by unfold oddPart; decide) h_bridge
  have hq1 : (oddPart + 1) / 2 < 2 ^ 512 :=
    lt_of_lt_of_le (by unfold oddPart; decide : (oddPart + 1) / 2 < 2 ^ 254) h_bridge
  rw [fpowR_eq_pow _ _ _ hq, fpowR_eq_pow _ _ _ hq, fpowR_eq_pow _ _ _ hq1]
  exact tonelliLoop_correct twoAdicity twoAdicity _ _ _ (tsInv_init ha hQR) (le_refl _)

/-! ### Completeness -/

/-- Completeness of `sqrt`: every quadratic residue yields a `some`.
Model-fidelity assurance for the `sqrt` definition; has no downstream
consumers by design. -/
theorem sqrt_complete {p : Lampe.Prime} [Lampe.Crypto.Bn254.Prime p] {a : Fp p}
    (h : ∃ y : Fp p, y * y = a) : (sqrt a).isSome := by
  unfold sqrt
  by_cases hz : a = 0
  · simp [hz]
  · simp [hz]
    have hEuler : fpowR a ((r_scalar - 1) / 2) 512 = 1 := by
      rw [fpowR_euler_eq_pow]
      exact euler_one_of_exists_sqrt hz h
    simp [hEuler]
    have htc := tonelliCandidate_sq hz h
    simp [htc]

end Lampe.Crypto.Bn254.Sqrt
