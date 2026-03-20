import «std-1.0.0-beta.14».Extracted
import Lampe

namespace Lampe.Stdlib.Collections.Vec

open «std-1.0.0-beta.14»

/-!
Core semantic interface for Noir `collections::vec::Vec`.

Vec wraps a single `Vector<T>`, which denotes as `List (T.denote p)`.
Unlike `BoundedVec`, there is no capacity constraint, so no `wellFormed` predicate is needed.

We keep:
- the concrete representation projection (`vector`)
- the semantic view (`embed`)
-/

abbrev vecTp (T : Tp) : Tp :=
  «std-1.0.0-beta.14::collections::vec::Vec».tp h![T]

abbrev Repr (p : Prime) (T : Tp) : Type :=
  Tp.denote p (vecTp T)

def vector {p T} (v : Repr p T) : List (T.denote p) :=
  Builtin.indexTpl v Builtin.Member.head

def embed {p T} (v : Repr p T) : List (T.denote p) :=
  vector v

abbrev V {p : Prime} {T : Tp} (selfRef : Ref) (xs : List (Tp.denote p T)) : SLP (State p) :=
  ∃∃ v : Repr p T, [selfRef ↦ ⟨vecTp T, v⟩] ⋆ ⟦embed v = xs⟧

end Lampe.Stdlib.Collections.Vec
