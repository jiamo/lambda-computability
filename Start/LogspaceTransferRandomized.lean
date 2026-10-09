import Start.SpaceToLogspaceTransfer
import Start.LogspaceEquality

/-!
# Host `LOGSPACE` languages lie in the randomized upstream classes

This library's own corollary (task `M27-LOGSPACE-TRANSFER`): combining the explicit compiler
`Complexity.Space.ToLogspace.logspace_subset_L` with the absorbed equality
`ExactDerandomization.exact_logarithmic_space_derandomization` (openai/math, see `NOTICE`), every
host `LOGSPACE` language lies in `ExactDerandomization.RL` and `ExactDerandomization.BPL`.

The converse inclusions (`ExactDerandomization.L ⊆ LOGSPACE`) still require a host tape program
simulating several two-sided work tapes and read-only input heads with binary position counters;
they are not claimed here.
-/

set_option autoImplicit false

namespace Complexity.Space

namespace ToLogspace

/-- Every host `LOGSPACE` language is in upstream `RL`. -/
theorem logspace_subset_RL {A : Language} (h : LOGSPACE A) :
    {x | A x} ∈ ExactDerandomization.RL := by
  have := ExactDerandomization.exact_logarithmic_space_derandomization.1
  rw [← this]
  exact logspace_subset_L h

/-- Every host `LOGSPACE` language is in upstream `BPL`. -/
theorem logspace_subset_BPL {A : Language} (h : LOGSPACE A) :
    {x | A x} ∈ ExactDerandomization.BPL := by
  obtain ⟨h1, h2⟩ := ExactDerandomization.exact_logarithmic_space_derandomization
  rw [← h2, ← h1]
  exact logspace_subset_L h

end ToLogspace

end Complexity.Space
