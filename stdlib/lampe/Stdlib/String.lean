import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.String

open «std-1.0.0-beta.12»
open Lampe.Stdlib

-- TODO (#50) as_bytes_vec: depends on Vec being formalized

set_option maxRecDepth 1500 in
theorem from_spec {p N a}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::convert::From».from h![(Tp.u 8).array N] (.str N) h![] h![] h![a])
    (fun r => r = Lampe.Builtin.arrayAsStr! a) := by
  resolve_trait
  steps
  simp_all

