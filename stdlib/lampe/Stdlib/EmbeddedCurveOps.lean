import «std-1.0.0-beta.14».Extracted
import Lampe

namespace Lampe.Stdlib.EmbeddedCurveOps

open «std-1.0.0-beta.14»

namespace Point

/-- A useful shorthand for the type of the embedded curve point. -/
@[reducible]
def type := «std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve point. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[reducible]
def mk {p} (x y : Fp p) (isInfinite : Bool) : Point.denote p := (x, y, isInfinite, ())

def x {p} (self : Point.denote p) : Fp p := self.1
def y {p} (self : Point.denote p) : Fp p := self.2.1
def isInfinite {p} (self : Point.denote p) : Bool := self.2.2.1

end Point

namespace Scalar

/-- A useful shorthand for the type of the embedded curve scalar. -/
@[reducible]
def type := «std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve scalar. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[reducible]
def mk {p} (lo hi : Fp p) : Scalar.denote p := (lo, hi, ())

def lo {p} (self : Scalar.denote p) : Fp p := self.1
def hi {p} (self : Scalar.denote p) : Fp p := self.2.1

end Scalar

/-! ## Method specs -/

/-- `EmbeddedCurvePoint::point_at_infinity()` returns `(0, 0, true)`. -/
theorem point_at_infinity_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::point_at_infinity».call h![] h![])
      (fun (r : Point.denote p) =>
        Point.x r = 0 ∧ Point.y r = 0 ∧ Point.isInfinite r = true) := by
  enter_decl
  steps
  sorry

/-- `EmbeddedCurvePoint::generator()` returns the standard generator point. -/
theorem generator_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::generator».call h![] h![])
      (fun (r : Point.denote p) =>
        Point.x r = 1 ∧ Point.isInfinite r = false) := by
  enter_decl
  steps
  sorry

/-- `EmbeddedCurvePoint::double(self)` is equivalent to `self + self`. -/
theorem double_spec {p self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun (_ : Point.denote p) => True) := by
  sorry

/-- `embedded_curve_add` adds two curve points (opaque builtin). -/
theorem embedded_curve_add_spec {p p1 p2} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add».call h![] h![p1, p2])
      (fun (_ : Point.denote p) => True) := by
  sorry

/-- `multi_scalar_mul` computes a multi-scalar multiplication (opaque builtin). -/
theorem multi_scalar_mul_spec {p N points scalars} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call h![N] h![points, scalars])
      (fun (_ : Point.denote p) => True) := by
  sorry

/-- `fixed_base_scalar_mul` multiplies the generator by a scalar. -/
theorem fixed_base_scalar_mul_spec {p scalar} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun (_ : Point.denote p) => True) := by
  sorry

/-- `EmbeddedCurveScalar::new(lo, hi)` constructs a scalar from lo/hi limbs. -/
theorem scalar_new_spec {p lo hi} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::new».call h![] h![lo, hi])
      (fun (r : Scalar.denote p) =>
        Scalar.lo r = lo ∧ Scalar.hi r = hi) := by
  enter_decl
  steps
  sorry

/-- `EmbeddedCurveScalar::from_field` decomposes a field element into lo/hi via `bn254::decompose`. -/
theorem scalar_from_field_spec {p scalar} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::from_field».call h![]
        h![scalar])
      (fun (_ : Scalar.denote p) => True) := by
  sorry

