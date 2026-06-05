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
Noir's `multi_scalar_mul_array_return` foreign builtin.

Two preconditions, both modelling actual circuit constraints emitted by
the Barretenberg MSM gadget:

- **On-curve**: every input point lifts through `curvePoint?`. The
  gadget's curve-relation constraint inside `cycle_group::batch_mul`
  enforces this on each input.
- **Canonical scalars**: every input scalar satisfies `scalarCanonical`
  (`lo.val < 2^128 ∧ hi.val < 2^126`). The gadget's
  `create_limbed_range_constraint` emits this on every input scalar via
  `straus_scalar_slice.cpp:59`, with `LO_BITS`/`HI_BITS` pinned in
  `cycle_scalar.hpp:38-44`.

The `predicate` parameter is ignored; the Noir surface wrapper
`multi_scalar_mul` (file `embedded_curve_ops.nr`) hardcodes
`predicate = true`.
-/
def multiScalarMul := newGenericPureBuiltin
  (fun n => ⟨[.array pointTp n, .array scalarTp n, .bool], .array pointTp 1⟩)
  (fun {p} n h![points, scalars, _] =>
    ⟨(∀ i, (curvePoint? (points.get i)).isSome)
      ∧ (∀ i, scalarCanonical (scalars.get i)),
      fun h =>
        let acc : (affineCurve p).Point :=
          ∑ i, scalarValueNat (scalars.get i) • (curvePoint? (points.get i)).get (h.1 i)
        ⟨[encodeCurvePoint acc], by simp⟩⟩)

end Lampe.Builtin
