import Stdlib.Collections.BoundedVec.Core
import Stdlib.Collections.BoundedVec.Methods
import Stdlib.Collections.BoundedVec.HigherOrderMap
import Stdlib.Collections.BoundedVec.Traits

/-!
This module is the public entrypoint for `Stdlib.Collections.BoundedVec`.

We keep the implementation/proofs split across:
- `Stdlib.Collections.BoundedVec.Core`
- `Stdlib.Collections.BoundedVec.HigherOrderMap`
- `Stdlib.Collections.BoundedVec.Traits`

Re-exporting from this file preserves the original import path for downstream modules.
-/
