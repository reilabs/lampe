import «std-1.0.0-beta.14».Extracted
import Lampe
namespace Lampe.Stdlib.String

open «std-1.0.0-beta.14»

-- Note: the extraction returns `Slice<u8>` (= `List (U 8)`), not `Vec<u8>`.
-- The Noir function `as_bytes_vec` returns `Vec<u8>`, but the Lampe extraction
-- does not wrap the result in a `#_makeData` call.
-- We state the spec in terms of the actual return type.
set_option maxRecDepth 1500 in
set_option linter.deprecated false in
theorem as_bytes_vec_spec {p N self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::string::as_bytes_vec».call h![N] h![self])
      (fun r => r = self.toList) := by
  enter_decl
  steps
  subst_vars
  rfl

set_option maxRecDepth 1500 in
theorem from_spec {p N a} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::convert::From».from h![(Tp.u 8).array N] (.str N) h![] h![] h![a])
      (fun r => r = Lampe.Builtin.arrayAsStr! a) := by
  resolve_trait
  steps
  simp_all
