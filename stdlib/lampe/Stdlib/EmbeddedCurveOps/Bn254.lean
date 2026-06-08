import Stdlib.EmbeddedCurveOps
import Stdlib.Field.Bn254

/-!
# BN254-specialized embedded curve specs

This file pins the embedded-curve stdlib to the concrete BN254
scalar-field prime (`bn254Prime`) and discharges the encoded-input
side hypotheses that the generic public specs in `Stdlib.EmbeddedCurveOps`
leave to the caller.

In particular this provides `fixed_base_scalar_mul_bn254_spec`: a
hypothesis-free version of `fixed_base_scalar_mul_spec`, where the
generator-encodes-to-`bn254GeneratorPoint` side condition has been
discharged via `native_decide` on the concrete prime.
-/

namespace Lampe.Stdlib.EmbeddedCurveOps.Bn254

open Lampe Lampe.Stdlib.Field.Bn254 Lampe.Crypto.EmbeddedCurve

private theorem bn254_generator_nonsingular :
    (affineCurve bn254Prime).Nonsingular 1
      (17631683881184975370165255887551781615748388533673675138860 : Fp bn254Prime) := by
  native_decide

/-- The Grumpkin generator as a Mathlib `WeierstrassCurve.Affine.Point`
over the BN254 scalar field. -/
def generatorPoint : (affineCurve bn254Prime).Point :=
  .some bn254_generator_nonsingular

@[simp] theorem generator_eq_encodeCurvePoint :
    (Lampe.Stdlib.EmbeddedCurveOps.Point.generator
      : Lampe.Stdlib.EmbeddedCurveOps.Point.denote bn254Prime) =
      encodeCurvePoint generatorPoint := rfl

/-- BN254-specialized canonical spec for `fixed_base_scalar_mul`:
the result is `scalarValueNat scalar • bn254GeneratorPoint`
encoded back into a Noir `EmbeddedCurvePoint`. The `h_gen` side
condition of the generic spec is discharged automatically by pinning
to `bn254Prime`. -/
theorem fixed_base_scalar_mul_bn254_spec
    {scalar : Lampe.Stdlib.EmbeddedCurveOps.Scalar.denote bn254Prime} :
    STHoare bn254Prime «std-1.0.0-beta.14».env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun r =>
        r = encodeCurvePoint
          (Lampe.Stdlib.EmbeddedCurveOps.scalarValueNat scalar • generatorPoint)) :=
  Lampe.Stdlib.EmbeddedCurveOps.fixed_base_scalar_mul_spec
    (Pgen := generatorPoint) generator_eq_encodeCurvePoint

end Lampe.Stdlib.EmbeddedCurveOps.Bn254
