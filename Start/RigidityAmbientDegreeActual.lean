import Start.RigidityAmbientDegreeBinding

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/AmbientDegreeActual.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding
universe u

theorem ownRealPower_codes (M R : ZFSet.{u})
    (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M := by
  intro A
  exact (hR _).trans (and_iff_left (realCode_subset A))

theorem ownDegreeUniverse_actual (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ x, x ∈ degreeUniverse R ↔
      ∃ A ∈ SetModelReals.reals M, x = degreeSet (degree A) := by
  intro x
  rw [mem_degreeUniverse]
  have hr := ownRealPower_codes M R hR
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,(hr A).mp hA,degreeCode_eq_degreeSet M hM hT R hr ((hr A).mp hA)⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,(hr A).mpr hA,(degreeCode_eq_degreeSet M hM hT R hr hA).symm⟩

theorem ownDegreeOrder_actual (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ A ∈ SetModelReals.reals M, ∀ B ∈ SetModelReals.reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ degreeOrder R ↔
        Reduces A B := by
  intro A hA B hB
  have hr := ownRealPower_codes M R hR
  rw [←degreeCode_eq_degreeSet M hM hT R hr hA,
    ←degreeCode_eq_degreeSet M hM hT R hr hB]
  exact degreeOrder_actual R ((hr A).mpr hA) ((hr B).mpr hB)

end TuringRigidity.FullSetForcing

