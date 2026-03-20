import «std-1.0.0-beta.14».Extracted
import Lampe
namespace Lampe.Stdlib.String

open «std-1.0.0-beta.14»

theorem as_bytes_vec_spec {p N self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::string::as_bytes_vec».call h![N] h![self])
      (fun r => r = self.toList) := by
  sorry

set_option maxRecDepth 1500 in
theorem from_spec {p N a}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.14::convert::From».from h![(Tp.u 8).array N] (.str N) h![] h![] h![a])
    (fun r => r = Lampe.Builtin.arrayAsStr! a) := by
  resolve_trait
  steps
  simp_all

