import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.7.0-rc2"

package «leansec» where
  -- add package configuration options here

@[default_target]
lean_lib «Leansec» where
  -- add library configuration options here
