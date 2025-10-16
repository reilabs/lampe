import «std-1.0.0-beta.12».Extracted
import Lampe

import Stdlib.Slice

namespace Lampe.Stdlib.Append

open «std-1.0.0-beta.12»
open Lampe.Stdlib

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

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

