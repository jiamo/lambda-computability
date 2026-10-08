import Start.RigidityUniformOracle
import Start.RigidityJoins

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/CountableBound.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.CountableBound
open UniformOracle

def sum (A : ℕ → Oracle) : Oracle := fun n => A (Nat.unpair n).1 (Nat.unpair n).2

theorem reduces_sum (A : ℕ → Oracle) (k : ℕ) : Reduces (A k) (sum A) := by
  apply RecursiveIn.iff_nat.mpr
  have hO : Nat.RecursiveIn {oracleFunction (sum A)} (oracleFunction (sum A)) :=
    .oracle _ (Set.mem_singleton _)
  have h := total_comp hO (total_pair (total_primrec (Primrec.const k)) (total_primrec Primrec.id))
  exact h.of_eq (fun n => by simp [oracleFunction, sum])

theorem countable_bounded (S : Set Degree) (hS : S.Countable) :
    ∃ b : Degree, ∀ x ∈ S, x ≤ b := by
  by_cases hne : S.Nonempty
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    choose A hA using (fun n => degree_surjective (f n))
    refine ⟨degree (sum A), ?_⟩
    intro x hx
    rw [hf] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [← hA n]
    exact reduces_sum A n
  · exact ⟨⊥, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

end TuringRigidity.CountableBound

