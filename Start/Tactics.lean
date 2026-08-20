/-
Shared tactic helpers used across the development.
-/

import Mathlib.Tactic.Bound

/-- Non-terminal version of `bound` for partial solving (Mathlib v4.28 made bound terminal). -/
macro "bound_nt" : tactic =>
  `(tactic| aesop (rule_sets := [Bound, -default]) (config := { enableSimp := false }))
