import Ampheck.Replay.Sessions

/-!
# Replays: the document's example, and zooming in

The document's own example, `a ⇒ (b ⇒ a)` by portation and specialization, and a
proof that zooms in to use the context a zoom in supplies. Each is checked by
evaluation in Lean's kernel, as `Ampheck.Replay` explains; the commands are there,
and the sessions in `Ampheck.Replay.Sessions`. These are kept out of
`Ampheck.Replay` because a replay against the shipped laws is expensive to
evaluate in the kernel, and `lake build ampheck` should not have to; `lake build
AmpheckReplay` builds them.
-/

namespace Ampheck
namespace Replay

open Expr (var mvar num bin neg)

set_option maxRecDepth 100000

/-! ### `a ⇒ (b ⇒ a)`, by portation and specialization -/

/-- The document's example proves `a ⇒ (b ⇒ a)`. -/
theorem portation_proves : proved portation = some goal := by decide +kernel

/-- Its proof pane is the document's three lines: the goal, `a ∧ b ⇒ a`, `⊤`,
joined by `=`. -/
theorem portation_lines :
    lines portation =
      some [(none, goal),
            (some .eq, bin .imp (bin .and (var "a") (var "b")) (var "a")),
            (some .eq, .top)] := by decide +kernel

/-- It leaves no gap, and ends at the outermost level. -/
theorem portation_complete :
    ((session.steps portation).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

/-! ### Zooming in, and the context a zoom in supplies -/

/-- It proves `(a ⇒ b) ⇒ (a ⇒ a ∧ b)`, with no gap and fully zoomed out. -/
theorem discharge_proves : proved discharge = some dischargeGoal := by decide +kernel

theorem discharge_complete :
    ((session.steps discharge).toOption.map fun d => (d.gaps, d.stack.length))
      = some ([], 1) := by decide +kernel

end Replay
end Ampheck
