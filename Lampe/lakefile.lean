import Lake
open Lake DSL

package Lampe where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  testDriver := "Tests"

require "leanprover-community" / "batteries" @ git "v4.22.0"
require "leanprover-community" / "mathlib" @ git "v4.22.0"

@[default_target]
lean_lib Lampe where

lean_lib Tests where
    globs := #[.submodules `Tests]
