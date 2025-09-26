import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Tp

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

abbrev comparator (p : Prime) (t : Tp) : Type := t.denote p → t.denote p → Ordering
