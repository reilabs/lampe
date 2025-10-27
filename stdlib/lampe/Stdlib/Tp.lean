import Lampe

namespace Lampe.Stdlib.Tp

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

abbrev comparator (p : Prime) (t : Tp) : Type := t.denote p → t.denote p → Ordering

