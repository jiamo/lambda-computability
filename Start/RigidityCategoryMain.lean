import Start.RigidityReduction
import Start.RigidityCategoryAvoidance

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/CategoryMain.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity

theorem inverse_le_realDegree_of_representation (hrep : BorelRepresentation)
    (π : Degree ≃o Degree) (t : ℝ) (ht : Irrational t) (ht0 : 0 < t) (ht1 : t < 1) :
    π.symm (realDegree t) ≤ realDegree t :=
  inverse_le_realDegree_of_obligations hrep cut_arithmetic four_value_recovery
    CategorySearch.category_avoidance π t ht ht0 ht1

theorem main_of_two_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) : MainTheorem :=
  main_of_three_obligations hrep hcover CategorySearch.category_avoidance

end TuringRigidity

