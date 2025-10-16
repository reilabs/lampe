import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Compat

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

theorem is_bn254_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::compat::is_bn254».call h![] h![])
    (fun r => r = true) := by
  enter_decl
  steps
  simp_all

