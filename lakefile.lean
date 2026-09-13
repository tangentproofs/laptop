import Lake
open Lake DSL

require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint" @ "v4.33.0"

-- Mathlib last so its transitive pins win for `lake exe cache get` hashes.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

package «LaPToP» where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib «LaPToP» where
