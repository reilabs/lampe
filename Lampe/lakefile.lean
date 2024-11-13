import Lake
open Lake DSL

package «Lampe» where
  version := v!"0.1.0"
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ git "v4.12.0"

@[default_target]
lean_lib «Lampe» where
  -- add any library configuration options here
