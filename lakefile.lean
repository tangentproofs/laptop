import Lake
open Lake DSL

require VersoBlueprint from git
  "https://github.com/tangentforks/verso-blueprint" @ "bump/lean-4.35"

-- The b4 virtual machine, which Hehner's language is compiled to
-- (`Aptop.ProgramTheory.CompileB4`). Pinned to a commit of the branch carrying
-- its formalization until that is merged.
require b4 from git
  "https://github.com/tangentstorm/b4" @ "e5827437f9d287b0e150de3ad62020885b76e1d6" / "imp/lean"

-- Mathlib last so its transitive pins win for `lake exe cache get` hashes.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68"

package «Aptop» where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib «Aptop» where

-- The interpreter command line (`lake exe interp`). `AptopMain` stays the Verso
-- blueprint generator; this is a separate root and a separate executable.
lean_exe «interp» where
  root := `InterpMain

-- Blueprint/docs target (Verso docs path). Also covered by default via Aptop.lean.
lean_lib «AptopBlueprint» where
  globs := #[
    `Aptop.Blueprint,
    .submodules `Aptop.Chapters,
  ]

-- Ampheck: the calculational proof assistant's kernel. It is deliberately free of
-- Mathlib and of Aptop, so `lake build Ampheck` is fast and the kernel's own
-- soundness checks are self-contained. Precompiled, so the `ampheck_proof` command
-- that checks calculations while Aptop builds runs as native code rather than in
-- the interpreter.
lean_lib «Ampheck» where
  precompileModules := true

-- The replays of `Ampheck.Replay` that run against the shipped law lists: each
-- has the kernel evaluate whole proof steps over the full boolean list, which is
-- minutes of work and gigabytes of memory in all. Kept out of `Ampheck` so that
-- `lake build ampheck` does not pay for them; a plain `lake build` checks them.
@[default_target]
lean_lib «AmpheckReplay» where
  globs := #[.submodules `Ampheck.Replay]

-- The headless Ampheck command line (`lake exe ampheck`).
lean_exe «ampheck» where
  root := `AmpheckMain
