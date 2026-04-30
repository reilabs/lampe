-- End-to-end proof test for impl Trait return types (issues #265, #267)

import «ExtractionTests-0.0.0».Extracted
import Lampe

open Lampe

set_option linter.unusedTactic false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev ImplTraitEnv := «ExtractionTests-0.0.0».ImplTraitReturn.env

-- some_foo() returns Bar{}, which is ()
theorem some_foo_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::some_foo».call h![] h![])
      fun v => v = () := by
  enter_decl; steps; simp_all

-- wrap_foo() calls some_foo() and returns its result
theorem wrap_foo_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::wrap_foo».call h![] h![])
      fun v => v = () := by
  enter_decl; steps [some_foo_spec]; simp_all

-- use_foo() calls wrap_foo().foo(), which returns 42.
-- This exercises:
--   1. impl Trait resolved to concrete Bar at function return sites
--   2. Trait call resolution (Bar as Foo)::foo
--   3. The trait definition has `as_impl` with return type `Any` (Tp.any)
theorem use_foo_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::use_foo».call h![] h![])
      fun v => v = (42 : Fp lp) := by
  enter_decl
  steps [wrap_foo_spec]
  resolve_trait
  steps
  norm_cast
