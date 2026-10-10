import Start.LogspaceTransferRandomized
import Start.LogspaceToSpaceCompile

/-!
# Host `LOGSPACE` equals `ExactDerandomization.L`, `RL` and `BPL`

This library's own module (task `M27-LOGSPACE-TRANSFER`).  The two concrete simulations

* `Complexity.Space.ToLogspace.logspace_subset_L` (host machine into an upstream decider, with an
  explicit clock), and
* `Complexity.Space.FromLogspace.logspace_of_L` (upstream decider into a host machine,
  `Start/LogspaceToSpaceCompile.lean`),

give `{x | A x} ∈ ExactDerandomization.L ↔ LOGSPACE A` for every binary language `A`.  With the
absorbed equality `ExactDerandomization.exact_logarithmic_space_derandomization : L = RL ∧ RL = BPL`
(openai/math, see `NOTICE`) the same holds for `RL` and `BPL`.  `LOGSPACE` is the library's own
class of `Start/SpaceMachine.lean`, unchanged.
-/

set_option autoImplicit false

namespace Complexity.Space

/-- **Host `LOGSPACE` is upstream `L`.** -/
theorem mem_L_iff_logspace (A : Language) :
    {x | A x} ∈ ExactDerandomization.L ↔ LOGSPACE A :=
  ⟨FromLogspace.logspace_of_L, ToLogspace.logspace_subset_L⟩

/-- **Host `LOGSPACE` is upstream `RL`.** -/
theorem mem_RL_iff_logspace (A : Language) :
    {x | A x} ∈ ExactDerandomization.RL ↔ LOGSPACE A := by
  rw [← ExactDerandomization.exact_logarithmic_space_derandomization.1]
  exact mem_L_iff_logspace A

/-- **Host `LOGSPACE` is upstream `BPL`.** -/
theorem mem_BPL_iff_logspace (A : Language) :
    {x | A x} ∈ ExactDerandomization.BPL ↔ LOGSPACE A := by
  rw [← ExactDerandomization.exact_logarithmic_space_derandomization.2,
    ← ExactDerandomization.exact_logarithmic_space_derandomization.1]
  exact mem_L_iff_logspace A

end Complexity.Space
