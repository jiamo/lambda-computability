import Start.RigidityCategoryMain
import Start.RigidityDegreeCoverage

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/CoverageMain.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity

theorem main_of_representation (hrep : BorelRepresentation) : MainTheorem :=
  main_of_two_obligations hrep irrational_degree_coverage

end TuringRigidity

