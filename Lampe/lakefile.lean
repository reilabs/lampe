import Lake
open Lake DSL

package Lampe where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  testDriver := "Tests"

require "leanprover-community" / "mathlib" @ git "v4.15.0-patch1"

@[default_target]
lean_lib Lampe where

lean_lib Tests where
    globs := #[.submodules `Tests]
