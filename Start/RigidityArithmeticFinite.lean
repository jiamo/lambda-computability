import Start.RigidityArithmeticHierarchy

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticFinite.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

theorem form_true (Y : Oracle) (n : ℕ) (s : Bool) : Form Y n s (fun _ => True) := by
  induction n with
  | zero =>
    classical
    simpa only [Form, RecursivePred, ↓reduceIte] using
      (total_primrec (O := {oracleFunction Y}) (Primrec.const 1))
  | succ n ih => exact ih.raise

theorem Form.finite_all {Y n s k} {P : Fin k → ℕ → Prop}
    (h : ∀ i, Form Y n s (P i)) : Form Y n s (fun x => ∀ i, P i x) := by
  induction k with
  | zero => exact (form_true Y n s).congr (fun x => by simp)
  | succ k ih =>
    exact ((h 0).and (ih (fun i => h i.succ))).congr (fun x => by
      simp only [Fin.forall_fin_succ])

end TuringRigidity.ArithmeticHierarchy

