import Start.RigidityModel
import Mathlib.Computability.TuringDegree
import Mathlib.Order.Hom.Basic

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/Degrees.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity

theorem reduces_refl (A : Oracle) : Reduces A A := TuringReducible.refl _
theorem reduces_trans {A B C : Oracle} (h : Reduces A B) (k : Reduces B C) :
    Reduces A C := TuringReducible.trans h k

def degree (A : Oracle) : Degree := toAntisymmetrization Reduces A

@[simp] theorem degree_le_iff (A B : Oracle) : degree A ≤ degree B ↔ Reduces A B := Iff.rfl

theorem degree_eq_iff (A B : Oracle) :
    degree A = degree B ↔ Reduces A B ∧ Reduces B A := by
  exact Quotient.eq

theorem degree_surjective : Function.Surjective degree := by
  intro a
  exact ⟨ofAntisymmetrization Reduces a, toAntisymmetrization_ofAntisymmetrization _ a⟩

theorem order_rigidity_of_inverse_le {α : Type*} [PartialOrder α]
    (h : ∀ π : α ≃o α, ∀ a, π.symm a ≤ a) :
    ∀ π : α ≃o α, ∀ a, π a = a := by
  intro π a
  apply le_antisymm
  · simpa using h π.symm a
  · simpa using π.monotone (h π a)

end TuringRigidity

