-- Generated by lampe

import Lampe

open Lampe

namespace «Experiments-0.0.0»
namespace Extracted

nr_struct_def Option2<T> {
    _is_some : bool,
    _value : T
}

nr_type_alias AliasedOpt<T> = Option2<T>