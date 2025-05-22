import Lake
open Lake DSL

package Lampe where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  testDriver := "Tests"

require "leanprover-community" / "mathlib" @ git "v4.19.0"

@[default_target]
lean_lib Lampe where

lean_lib Tests where
    globs := #[.submodules `Tests]
