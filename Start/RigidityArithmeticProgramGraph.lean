import Start.RigidityUniformPartialGraph
import Start.RigidityArithmeticRelations
import Start.RigidityGenericTotality

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticProgramGraph.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ArithmeticProgramGraph
open Encodable UniformArithmetic IndexMatrix GenericIdentity

theorem eval_arith (p : OracleCode) {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n a : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v ∈ OracleCode.eval (oracleFunction (B O (c v))) p (n v)) := by
  obtain ⟨d, hd⟩ := UniformPartialGraph.eval_iff_table p
  have h := (run_arith hB (hc.comp left_primrec) (Primrec.const (encode d))
    (hn.comp left_primrec) right_primrec (ha.comp left_primrec)).ex
  exact h.congr (fun O v => by
    simpa only [left, right, Nat.unpair_pair, machine_encode, Option.mem_def] using
      (hd (B O (c v)) (n v) (a v)).symm)

theorem output_arith (p : OracleCode) {B : OracleFamily} (hB : ArithmeticOracle B) :
    ArithmeticOracle (fun O v => programOutput p (B O v)) :=
  (eval_arith p hB left_primrec right_primrec (Primrec.const 1)).congr
    (fun _ _ => by simp [programOutput])

theorem value_arith (p : OracleCode) {P A : OracleFamily}
    (hP : ArithmeticOracle P) (hA : ArithmeticOracle A) :
    ArithmeticOracle (fun O v => value p (P O v) (A O v)) :=
  output_arith p (join_arith hA hP)

theorem total_arith (p : OracleCode) {P A : OracleFamily}
    (hP : ArithmeticOracle P) (hA : ArithmeticOracle A) :
    Arith (fun O v => Total p (P O v) (A O v)) := by
  have hB := join_arith hA hP
  have h0 := eval_arith p hB left_primrec right_primrec (Primrec.const 0)
  have h1 := eval_arith p hB left_primrec right_primrec (Primrec.const 1)
  exact (h0.or h1).all.congr (fun O v => by
    simpa only [left, right, Nat.unpair_pair, BinaryHalts] using
      (total_iff_binaryHalts p (P O v) (A O v)).symm)

end TuringRigidity.ArithmeticProgramGraph

