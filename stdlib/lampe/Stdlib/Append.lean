import «std-1.0.0-beta.12».Extracted
import Lampe

import Stdlib.Slice
import Stdlib.TraitMethods

namespace Lampe.Stdlib.Append

open «std-1.0.0-beta.12»
open Lampe.Stdlib

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

theorem slice_empty_spec {p T }
  : STHoare p env ⟦⟧
    (empty h![] (Tp.slice T) h![] h![] h![])
    (fun r => r = []) := by
  resolve_trait
  steps
  simp_all

theorem slice_append_spec {p T self other}
  : STHoare p env ⟦⟧
    (append h![] (Tp.slice T) h![] h![] h![self, other])
    (fun r => r = self ++ other) := by
  resolve_trait
  steps [Slice.append_spec]
  simp_all

