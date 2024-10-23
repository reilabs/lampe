import Lampe.Tp
import Mathlib

namespace Lampe

def AnyValue (P : Prime) := (tp : Tp) × tp.denote P

abbrev State (P : Prime) := Finmap (fun (_ : Ref) => AnyValue P)

namespace State

end State

end Lampe
