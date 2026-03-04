import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.EmbeddedCurveOps

open «std-1.0.0-beta.12»

namespace Point

/-- A useful shorthand for the type of the embedded curve point. -/
@[reducible]
def type := «std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint».tp h![]

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
def type := «std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurveScalar».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve scalar. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[reducible]
def mk {p} (lo hi : Fp p) : Scalar.denote p := (lo, hi, ())

def lo {p} (self : Scalar.denote p) : Fp p := self.1
def hi {p} (self : Scalar.denote p) : Fp p := self.2.1

end Scalar

open Lampe

open «std-1.0.0-beta.12» (env)

set_option maxRecDepth 4096

theorem point_at_infinity_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint::point_at_infinity».call h![] h![])
      (fun r => r = Point.mk 0 0 true) := by
  enter_decl; steps; simp_all [Point.mk, HList.toTuple]

theorem generator_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint::generator».call h![] h![])
      (fun r => r = Point.mk 1 17631683881184975370165255887551781615748388533673675138860 false) := by
  enter_decl; steps; simp_all [Point.mk, HList.toTuple]

theorem scalar_new_spec {p} {lo hi : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurveScalar::new».call h![] h![lo, hi])
      (fun r => r = Scalar.mk lo hi) := by
  enter_decl; steps; simp_all [Scalar.mk, HList.toTuple]

theorem neg_spec {p} {self : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::ops::arith::Neg».neg h![] Point.type h![] h![] h![self])
      (fun r => r = Point.mk (Point.x self) (-(Point.y self)) (Point.isInfinite self)) := by
  resolve_trait; steps; subst_vars; obtain ⟨x, y, inf, _⟩ := self
  simp [Point.mk, Point.x, Point.y, Point.isInfinite, Builtin.indexTpl,
    «std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint»]

theorem eq_scalar_spec {p} {self other : Scalar.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::cmp::Eq».eq h![] Scalar.type h![] h![] h![self, other])
      (fun r : Bool => ⟦r ↔ Scalar.hi self = Scalar.hi other ∧ Scalar.lo self = Scalar.lo other⟧) := by
  resolve_trait; steps <;> try exact ()
  obtain ⟨lo₁, hi₁, _⟩ := self; obtain ⟨lo₂, hi₂, _⟩ := other
  simp_all [Scalar.hi, Scalar.lo, Builtin.indexTpl, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem eq_point_spec {p} {self other : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::cmp::Eq».eq h![] Point.type h![] h![] h![self, other])
      (fun r : Bool => ⟦r ↔
        (Point.isInfinite self ∧ Point.isInfinite other) ∨
        (Point.isInfinite self = Point.isInfinite other ∧
         Point.x self = Point.x other ∧ Point.y self = Point.y other)⟧) := by
  resolve_trait; steps <;> try exact ()
  obtain ⟨x₁, y₁, inf₁, _⟩ := self; obtain ⟨x₂, y₂, inf₂, _⟩ := other
  simp_all [Point.x, Point.y, Point.isInfinite, Builtin.indexTpl,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  tauto

theorem scalar_hash_spec {p H self state}
    (h_hash_field : ∀ (v : Fp p), STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] .field h![] h![H] h![v, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] Scalar.type h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps [h_hash_field]

theorem point_hash_spec {p H self state}
    {bool_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] .bool}
    {field_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] .field}
    (h_hash_bool : ∀ (v : Bool), STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] .bool h![] h![H] h![v, state])
      (fun _ => ⟦⟧))
    (h_hash_field : ∀ (v : Fp p), STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] .field h![] h![H] h![v, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] Point.type h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.ite_intro <;> intro <;> steps [h_hash_bool, h_hash_field]

theorem double_spec {p} {self : Point.denote p}
    (h_add : ∀ a b : Point.denote p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::embedded_curve_add».call h![] h![a, b])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun _ => ⟦⟧) := by
  enter_decl; steps [h_add]

theorem sub_spec {p} {self other : Point.denote p}
    {add_impl : «std-1.0.0-beta.12::ops::arith::Add».hasImpl env h![] Point.type}
    {neg_impl : «std-1.0.0-beta.12::ops::arith::Neg».hasImpl env h![] Point.type}
    (h_add : ∀ a b : Point.denote p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::ops::arith::Add».add h![] Point.type h![] h![] h![a, b])
      (fun _ => ⟦⟧))
    (h_neg : ∀ a : Point.denote p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::ops::arith::Neg».neg h![] Point.type h![] h![] h![a])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::ops::arith::Sub».sub h![] Point.type h![] h![] h![self, other])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps [h_neg, h_add]

theorem add_spec {p} {self other : Point.denote p}
    (h_add : ∀ a b : Point.denote p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::embedded_curve_add».call h![] h![a, b])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::ops::arith::Add».add h![] Point.type h![] h![] h![self, other])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps [h_add]

theorem from_field_spec {p} {scalar : Fp p}
    (h_decompose : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::decompose».call h![] h![scalar])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurveScalar::from_field».call h![] h![scalar])
      (fun _ => ⟦⟧) := by
  enter_decl; steps [h_decompose]

theorem add_not_nul_spec {p} {point1 point2 : Point.denote p}
    (h_add_unsafe : ∀ a b : Point.denote p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::embedded_curve_add_unsafe».call h![] h![a, b])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::embedded_curve_add_not_nul».call h![] h![point1, point2])
      (fun _ => ⟦⟧) := by
  enter_decl; steps [h_add_unsafe]; exact ()

theorem embedded_curve_add_spec {p} {point1 point2 : Point.denote p}
    (h_add_unsafe : ∀ a b : Point.denote p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::embedded_curve_add_unsafe».call h![] h![a, b])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::embedded_curve_ops::embedded_curve_add».call h![] h![point1, point2])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps <;> try exact ()
  apply STHoare.iteFalse_intro
  steps [h_add_unsafe] <;> try exact ()
  -- ite double_predicate inside letIn
  apply STHoare.letIn_intro (Q := fun _ =>
    [result ↦ ⟨«std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint».tp h![], «#v_25»⟩])
  · apply STHoare.ite_intro <;> intro <;> steps
  · intro; steps
    -- ite point1.isInfinite inside letIn
    apply STHoare.letIn_intro (Q := fun _ =>
      ∃∃ v, [result ↦ ⟨«std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint».tp h![], v⟩])
    · apply STHoare.ite_intro <;> intro <;> steps
    · intro; steps
      -- ite point2.isInfinite inside letIn
      apply STHoare.letIn_intro (Q := fun _ =>
        ∃∃ v, [result ↦ ⟨«std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint».tp h![], v⟩])
      · apply STHoare.ite_intro <;> intro <;> steps
      · intro; steps <;> try exact ()

end Lampe.Stdlib.EmbeddedCurveOps
