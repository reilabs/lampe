-- Generated by lampe

import «ExtractionTests-0.0.0».Extracted.GeneratedTypes
import Lampe

open Lampe

namespace «ExtractionTests-0.0.0»
namespace Extracted

nr_trait_impl[impl_428] <> associated_type::Foo<> for associated_type::Pair<> where  {
    fn «foo»<> (self : associated_type::Pair<>) -> Field {
        (self as associated_type::Pair<>).a;
}
}


def AssociatedType.env := Lampe.Env.mk [] [impl_428]