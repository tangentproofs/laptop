import Lake
open Lake DSL

require VersoBlueprint from git
  "https://github.com/tangentforks/verso-blueprint" @ "bump/lean-4.35"

-- Mathlib last so its transitive pins win for `lake exe cache get` hashes.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68"

package «LaPToP» where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib «LaPToP» where

-- The interpreter command line (`lake exe interp`). `LaPToPMain` stays the Verso
-- blueprint generator; this is a separate root and a separate executable.
lean_exe «interp» where
  root := `InterpMain

-- Blueprint/docs target (Verso docs path). Also covered by default via LaPToP.lean.
lean_lib «LaPToPBlueprint» where
  globs := #[
    `LaPToP.Blueprint,
    .submodules `LaPToP.Chapters,
  ]
