import Lampe.Builtin.Basic
import Lampe.Crypto.EmbeddedCurve
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

open Lampe.Crypto.EmbeddedCurve

/--
Noir's `embedded_curve_add` foreign builtin. The result is Mathlib's
affine `+` on the Grumpkin curve `y² = x³ - 17`. On-curve obligation
is a precondition: both input tuples must lift through `curvePoint?`.
-/
def embeddedCurveAdd := newGenericPureBuiltin
  (fun (_ : Unit) => ⟨[pointTp, pointTp, .bool], .array pointTp 1⟩)
  (fun _ h![p1, p2, _] =>
    ⟨(curvePoint? p1).isSome ∧ (curvePoint? p2).isSome,
      fun ⟨h1, h2⟩ =>
        ⟨[encodeCurvePoint ((curvePoint? p1).get h1 + (curvePoint? p2).get h2)], by simp⟩⟩)

/--
Noir's `multi_scalar_mul_array_return` foreign builtin. The result is
`∑ᵢ (scalarValueNat sᵢ) • Pᵢ` computed via Mathlib's `+` and `nsmul`.
On-curve obligation is a precondition: every input point must lift
through `curvePoint?`.
-/
def multiScalarMul := newGenericPureBuiltin
  (fun n => ⟨[.array pointTp n, .array scalarTp n, .bool], .array pointTp 1⟩)
  (fun {p} n h![points, scalars, _] =>
    ⟨∀ i, (curvePoint? (points.get i)).isSome,
      fun h =>
        let acc : (affineCurve p).Point :=
          ∑ i, scalarValueNat (scalars.get i) • (curvePoint? (points.get i)).get (h i)
        ⟨[encodeCurvePoint acc], by simp⟩⟩)

end Lampe.Builtin
