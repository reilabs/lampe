import Lake
open Lake DSL

package Lampe where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  moreLeanArgs := #["--tstack=65536"]
  testDriver := "Tests"

require "leanprover-community" / "batteries" @ git "v4.29.1"
require "leanprover-community" / "mathlib" @ git "v4.29.1"

@[default_target]
lean_lib Lampe where

lean_lib Tests where
    globs := #[.submodules `Tests]
