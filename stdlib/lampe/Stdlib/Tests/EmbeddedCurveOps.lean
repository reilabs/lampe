import «std-1.0.0-beta.14».Extracted
import Lampe
import Lampe.Crypto.Bn254.Prime
import Stdlib.EmbeddedCurveOps
import Stdlib.Field.Bn254

/-!
# Canonical-decomposition validation vectors

Concrete `native_decide` tests on the `Scalar.canonicalDecomp` /
`Lampe.Crypto.EmbeddedCurve.scalarCanonical` machinery introduced for the Pedersen wrapper
deterministic corollaries. Tests cover edge cases (`f = 0`, `f = 1`,
`f = p - 1`, the boundary `pow128`, and the `(plo, phi)` collision
point that the uniqueness lemma rules out) plus a handful of
random-looking values.

The tests verify three properties for each chosen `f`:

1. `Scalar.canonicalDecomp f` satisfies `Lampe.Crypto.EmbeddedCurve.scalarCanonical`
   (limb-range canonicality: `lo.val < 2^128 ∧ hi.val < 2^126`).
2. `Scalar.canonicalDecomp f` recovers `f` via the limb identity
   `f = lo + 2^128 · hi`.
3. `canonicalDecomp` agrees with the explicit `(0, 0)` decomposition
   on `f = 0`, ruling out the spurious `(plo, phi)` alternative.

These exercise the machinery the Pedersen `_spec_canonical` corollaries
depend on (`Scalar.canonical_decomp_unique`,
`Scalar.canonicalDecomp_decomposes`, `Scalar.canonicalDecomp_Canonical`).
-/

namespace Tests.EmbeddedCurveOps

open Lampe (Fp Prime)
open Lampe.Stdlib.EmbeddedCurveOps

/-- BN254 scalar field prime — the field for embedded-curve scalars. -/
abbrev P : Lampe.Prime := bn254Prime

/-- `Lampe.Crypto.EmbeddedCurve.scalarCanonical` is two strict inequalities on `Nat`-valued
`.val` projections — decidable, but `Lean` needs the decidability
instance spelled out. -/
instance (s : Scalar.denote P) : Decidable (Lampe.Crypto.EmbeddedCurve.scalarCanonical s) := by
  unfold Lampe.Crypto.EmbeddedCurve.scalarCanonical
  infer_instance

/-! ### `Lampe.Crypto.EmbeddedCurve.scalarCanonical` holds on `canonicalDecomp` -/

/-- `canonicalDecomp 0 = (0, 0)` and is canonical. -/
example : Lampe.Crypto.EmbeddedCurve.scalarCanonical (Scalar.canonicalDecomp (0 : Fp P)) := by
  native_decide

/-- `canonicalDecomp 1 = (1, 0)` and is canonical. -/
example : Lampe.Crypto.EmbeddedCurve.scalarCanonical (Scalar.canonicalDecomp (1 : Fp P)) := by
  native_decide

/-- `canonicalDecomp (p - 1) = (plo - 1, phi)` and is canonical (high
limb is `phi`, just below the `2^126` bound; low limb is `plo - 1`,
just below the `2^128` bound). -/
example : Lampe.Crypto.EmbeddedCurve.scalarCanonical (Scalar.canonicalDecomp (-1 : Fp P)) := by
  native_decide

/-- `canonicalDecomp (pow128) = (0, 1)` — boundary between low- and
high-limb regimes. -/
example :
    Lampe.Crypto.EmbeddedCurve.scalarCanonical
      (Scalar.canonicalDecomp ((Lampe.pow128 : Nat) : Fp P)) := by
  native_decide

/-- `canonicalDecomp (pow128 - 1) = (pow128 - 1, 0)` — largest pure-low
value. -/
example :
    Lampe.Crypto.EmbeddedCurve.scalarCanonical
      (Scalar.canonicalDecomp ((Lampe.pow128 - 1 : Nat) : Fp P)) := by
  native_decide

/-- `canonicalDecomp (pow128 * phi) = (0, phi)` — top of the
canonical-range branch (a) boundary. -/
example :
    Lampe.Crypto.EmbeddedCurve.scalarCanonical
      (Scalar.canonicalDecomp
        ((Lampe.pow128 * Lampe.Crypto.Bn254.phi : Nat) : Fp P)) := by
  native_decide

/-- A random-looking value in the middle of the field. -/
example :
    Lampe.Crypto.EmbeddedCurve.scalarCanonical
      (Scalar.canonicalDecomp
        ((12345678901234567890123456789012345678901234567890123456789012345 : Nat) : Fp P)) := by
  native_decide

/-! ### `canonicalDecomp` recovers `f` via the limb identity -/

/-- The limb identity `f = lo + 2^128 · hi` holds on `f = pow128 + 7`. -/
example :
    let f : Fp P := ((Lampe.pow128 + 7 : Nat) : Fp P)
    let s := Scalar.canonicalDecomp f
    f = (Lampe.Crypto.EmbeddedCurve.scalarLo s) + ((Lampe.pow128 : Nat) : Fp P) * (Lampe.Crypto.EmbeddedCurve.scalarHi s) := by
  native_decide

/-- The limb identity holds on `f = p - 1` (the wraparound edge case). -/
example :
    let f : Fp P := (-1 : Fp P)
    let s := Scalar.canonicalDecomp f
    f = (Lampe.Crypto.EmbeddedCurve.scalarLo s) + ((Lampe.pow128 : Nat) : Fp P) * (Lampe.Crypto.EmbeddedCurve.scalarHi s) := by
  native_decide

/-! ### Uniqueness corner case: `f = 0` resolves to `(0, 0)`, not `(plo, phi)` -/

/-- On `f = 0`, `canonicalDecomp` picks the `(0, 0)` witness, not the
arithmetically-equivalent `(plo, phi)` witness. This is the
counterexample to "any canonical-range decomposition of a field
element is unique" — the `canonical_decomp_unique` lemma's
`hdisj` hypothesis breaks the tie. -/
example :
    (Lampe.Crypto.EmbeddedCurve.scalarLo (Scalar.canonicalDecomp (0 : Fp P))).val = 0 ∧
    (Lampe.Crypto.EmbeddedCurve.scalarHi (Scalar.canonicalDecomp (0 : Fp P))).val = 0 := by
  native_decide

/-- The spurious `(plo, phi)` witness is **not** what `canonicalDecomp`
returns on `f = 0`, even though it satisfies the limb identity
`plo + 2^128 · phi = p ≡ 0 (mod p)`. -/
example :
    (Lampe.Crypto.EmbeddedCurve.scalarLo (Scalar.canonicalDecomp (0 : Fp P))).val ≠
      Lampe.Crypto.Bn254.plo ∨
    (Lampe.Crypto.EmbeddedCurve.scalarHi (Scalar.canonicalDecomp (0 : Fp P))).val ≠
      Lampe.Crypto.Bn254.phi := by
  native_decide

end Tests.EmbeddedCurveOps
