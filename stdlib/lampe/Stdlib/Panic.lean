import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Panic

open «std-1.0.0-beta.12»

/--
Note that this theorem exists only to make it easy to steps through calls to `panic` in your code as
it cannot (and does not) assert any meaningful properties on the functioning of the call to panic.
-/
theorem panic_correct {p T U N msg}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::panic::panic».call h![T, U, N] h![msg])
    (fun _ => ⟦⟧) := by
  enter_decl
  steps

