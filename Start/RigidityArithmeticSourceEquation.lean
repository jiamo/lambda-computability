import Start.RigidityArithmeticProgramGraph
import Start.RigidityArithmeticShuffleGraph
import Start.RigidityArithmeticPrincipalIntersection

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticSourceEquation.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ArithmeticSourceEquation
open UniformArithmetic ArithmeticProgramGraph ArithmeticShuffleGraph GenericIdentity

theorem equation_arith (p : OracleCode) {P Y L R : OracleFamily}
    (hP : ArithmeticOracle P) (hY : ArithmeticOracle Y)
    (hL : ArithmeticOracle L) (hR : ArithmeticOracle R) :
    Arith (fun O v => SourceEquation p (P O v) (Y O v, L O v, R O v)) := by
  have hYL := code_arith hY hL
  have hYR := code_arith hY hR
  have hi := ArithmeticPrincipalIntersection.principal_arith (value_arith p hP hY)
    (join_arith (value_arith p hP hYL) (value_arith p hP hL))
    (join_arith (value_arith p hP hYR) (value_arith p hP hR))
  exact (total_arith p hP hY).and ((total_arith p hP hL).and
    ((total_arith p hP hR).and ((total_arith p hP hYL).and
      ((total_arith p hP hYR).and hi))))

theorem sourceEquation_arith (p : OracleCode) :
    Arith (fun O _ => SourceEquation p (O 0) (O 1, O 2, O 3)) :=
  equation_arith p (parameter_arith 0) (parameter_arith 1)
    (parameter_arith 2) (parameter_arith 3)

end TuringRigidity.ArithmeticSourceEquation

