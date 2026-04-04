import Stdlib.Collections.Map.Methods
import Stdlib.Cmp

namespace Lampe.Stdlib.Collections.Map

open «std-1.0.0-beta.14»

/-!
Trait-method specs for `HashMap`.

These specs are placeholders: the trait dispatch mechanism (`resolve_trait`) needs
the correct `hasImpl` instances, which depend on the full combined environment.
The BoundedVec Traits.lean uses `resolve_trait` followed by `steps`; the same
pattern applies here but requires additional setup for the Hash/BuildHasher constraints.

TODO:
- `eq_trait_spec`   (Eq::eq for HashMap, subset check in both directions)
- `default_trait_spec`  (Default::default, delegates to with_hasher)
-/

end Lampe.Stdlib.Collections.Map
