import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint" @ "v4.34.0"

package «LaPToP» where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib «LaPToP» where
