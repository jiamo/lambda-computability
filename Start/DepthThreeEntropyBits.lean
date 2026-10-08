import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/EntropyBits.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
Import change: upstream `Mathlib.Basic.Real.Basic` does not exist on this pin; replaced by `import Mathlib`.
See `NOTICE` at the repository root.
-/

namespace DepthThreeLowerBound

open scoped BigOperators

def trueCount {N : ℕ} (z : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => z i = true).card

theorem trueCount_le {N : ℕ} (z : Fin N → Bool) : trueCount z ≤ N := by
  simpa only [trueCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => z i = true))

theorem trueCount_cast {N : ℕ} (z : Fin N → Bool) :
    (trueCount z : ℝ) = ∑ i, if z i = true then (1 : ℝ) else 0 := by
  exact Finset.natCast_card_filter (fun i => z i = true) Finset.univ

end DepthThreeLowerBound

