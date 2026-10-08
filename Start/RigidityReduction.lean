import Start.RigidityCutArithmetic
import Start.RigidityEffectiveRecovery

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/Reduction.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity

theorem main_of_three_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) (havoid : CategoryAvoidance) : MainTheorem :=
  main_of_obligations hrep cut_arithmetic hcover four_value_recovery havoid

end TuringRigidity

