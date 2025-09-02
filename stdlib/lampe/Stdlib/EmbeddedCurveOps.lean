import «std-1.0.0-beta.11».Extracted.EmbeddedCurveOps
import «std-1.0.0-beta.11».Extracted.«std-1.0.0-beta.11»
import Lampe

namespace Lampe
namespace Stdlib

export «std-1.0.0-beta.11».Extracted (
  «std::embedded_curve_ops::EmbeddedCurvePoint::double»
  «std::embedded_curve_ops::EmbeddedCurvePoint::point_at_infinity»
  «std::embedded_curve_ops::EmbeddedCurvePoint::generator»
  «std::embedded_curve_ops::EmbeddedCurveScalar::new»
  «std::embedded_curve_ops::EmbeddedCurveScalar::from_field»
  «std::embedded_curve_ops::EmbeddedCurveScalar::from_bytes»
  «std::embedded_curve_ops::multi_scalar_mul»
  «std::embedded_curve_ops::fixed_base_scalar_mul»
  «std::embedded_curve_ops::embedded_curve_add»
  «std::embedded_curve_ops::embedded_curve_add_not_nul»
  «std::embedded_curve_ops::embedded_curve_add_unsafe»
  EmbeddedCurveOps.env
)

open «std-1.0.0-beta.11».Extracted
