import Start.RandUpstreamToSpaceClass
import Start.LogspaceTransferEquiv

/-!
# Host randomized logarithmic space equals host `LOGSPACE`

This library's own module (task `M27-HOST-RANDOMIZED-SPACE`).  The host classes `HostRL` and
`HostBPL` of `Start/SpaceRandomized.lean` are equal to upstream `RL` and `BPL` by explicit
simulations (`Complexity.Space.hostRL_iff`, `Complexity.Space.hostBPL_iff`, which do not depend on
the derandomization theorem), and upstream `RL` and `BPL` are host `LOGSPACE` by
`Complexity.Space.mem_RL_iff_logspace` and `Complexity.Space.mem_BPL_iff_logspace`
(`Start/LogspaceTransferEquiv.lean`, which uses the absorbed theorem `L = RL = BPL`).
-/

set_option autoImplicit false

namespace Complexity.Space

/-- **Host `BPL` is host `LOGSPACE`.** -/
theorem hostBPL_iff_logspace (A : Language) : HostBPL A ↔ LOGSPACE A :=
  (hostBPL_iff A).trans (mem_BPL_iff_logspace A)

/-- **Host `RL` is host `LOGSPACE`.** -/
theorem hostRL_iff_logspace (A : Language) : HostRL A ↔ LOGSPACE A :=
  (hostRL_iff A).trans (mem_RL_iff_logspace A)

end Complexity.Space
