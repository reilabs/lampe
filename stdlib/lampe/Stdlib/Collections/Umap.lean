import «std-1.0.0-beta.12».Extracted.Collections.Umap
import «std-1.0.0-beta.12».Extracted.«std-1.0.0-beta.12»
import Lampe

namespace Lampe
namespace Stdlib

export «std-1.0.0-beta.12».Extracted (
  «std::collections::umap::UHashMap»
  «std::collections::umap::Slot»
  «std::collections::umap::Slot::is_valid»
  «std::collections::umap::Slot::is_available»
  «std::collections::umap::Slot::key_value»
  «std::collections::umap::Slot::key_value_unchecked»
  «std::collections::umap::Slot::set»
  «std::collections::umap::Slot::mark_deleted»
  «std::collections::umap::UHashMap::with_hasher»
  «std::collections::umap::UHashMap::with_hasher_and_capacity»
  «std::collections::umap::UHashMap::clear»
  «std::collections::umap::UHashMap::contains_key»
  «std::collections::umap::UHashMap::is_empty»
  «std::collections::umap::UHashMap::entries»
  «std::collections::umap::UHashMap::keys»
  «std::collections::umap::UHashMap::values»
  «std::collections::umap::UHashMap::iter_mut»
  «std::collections::umap::UHashMap::iter_keys_mut»
  «std::collections::umap::UHashMap::iter_values_mut»
  «std::collections::umap::UHashMap::retain»
  «std::collections::umap::UHashMap::len»
  «std::collections::umap::UHashMap::capacity»
  «std::collections::umap::UHashMap::get»
  «std::collections::umap::UHashMap::insert»
  «std::collections::umap::UHashMap::try_resize»
  «std::collections::umap::UHashMap::remove»
  «std::collections::umap::UHashMap::hash»
  «std::collections::umap::UHashMap::quadratic_probe»
  Collections.Umap.env
)

open «std-1.0.0-beta.12».Extracted
