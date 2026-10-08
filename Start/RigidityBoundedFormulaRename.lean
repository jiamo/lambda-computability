import Start.RigidityFiniteTuple

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Syntax/BoundedFormulaRename.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
universe u

@[simp] theorem Formula.eval_rename_comp (p : Formula) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (p.rename r).Eval e ↔ p.Eval (e ∘ r) := Formula.eval_rename p r e
end TuringRigidity.BoundedSetTheory

