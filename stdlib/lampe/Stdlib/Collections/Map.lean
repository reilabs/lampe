import Stdlib.Collections.Map.Core
import Stdlib.Collections.Map.Slot
import Stdlib.Collections.Map.Methods
import Stdlib.Collections.Map.HigherOrderMap
import Stdlib.Collections.Map.Traits

/-!
This module is the public entrypoint for `Stdlib.Collections.Map`.

We keep the implementation/proofs split across:
- `Stdlib.Collections.Map.Core`       (semantic projections, well-formedness)
- `Stdlib.Collections.Map.Slot`       (Slot method specs)
- `Stdlib.Collections.Map.Methods`    (HashMap accessor and core method specs)
- `Stdlib.Collections.Map.HigherOrderMap` (iteration and higher-order mutation specs)
- `Stdlib.Collections.Map.Traits`     (Eq and Default trait specs)

Re-exporting from this file preserves the original import path for downstream modules.
-/
