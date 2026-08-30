/-
Shared tactic helpers used across the development.
-/

import Mathlib.Tactic.Bound

/-- Non-terminal version of `bound` for partial solving (Mathlib's `bound` is terminal). -/
macro "bound_nt" : tactic =>
  `(tactic| aesop (rule_sets := [Bound, -default]) (config := { enableSimp := false }))
