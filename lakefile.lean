import Lake
open Lake DSL

package Finiteness where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require regex from git
  "https://github.com/ezhuchko/extended-regexes.git" @ "main"

@[default_target]
lean_lib Finiteness where
