import «std-1.0.0-beta.12».Extracted
import Lampe

/-!
This file contains (namespaced) definitions of shorthand for calling various trait methods, as well
as asserting the existence of certain trait implementations on types.

Where possible, these shorthands should live in the corresponding files (e.g. `Eq::eq`'s shorthand
is in `Cmp.lean`), but in some cases the potential for import cycles can require that they are
pulled out into a separate file. This is that file.
-/

namespace Lampe.Stdlib

open «std-1.0.0-beta.12»
open Lampe.Stdlib

namespace Append

/-- A shorthand for a call to the `std::append::Append::empty` method. -/
@[reducible]
def empty {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::append::Append».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::append::Append».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::append::Append».«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::append::Append».empty.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::append::Append».empty.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::append::Append».empty generics Self associatedTypes fnGenerics

/-- A shorthand for a call to the `std::append::Append::append` method. -/
@[reducible]
def append {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::append::Append».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::append::Append».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::append::Append».«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::append::Append».append.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::append::Append».append.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::append::Append».append generics Self associatedTypes fnGenerics

/--
Asserts that the provided `tp` has an implementation of `std::append::Append` in the environment.
-/
@[reducible]
def hasImpl (env : Env) (tp : Tp) := «std-1.0.0-beta.12::append::Append».hasImpl env h![] tp

end Append
