import Start.RigidityNativePersistenceSyntax

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/SourceTAbsolutenessEndpoint.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions
universe u
noncomputable section

theorem source_4_2_2_transitive_countable (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    ∃ D ∈ M, ∃ L ∈ M,
      (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
      (∀ A ∈ reals M, ∀ B ∈ reals M,
        ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
      (∀ ρ : I ≃o I, automorphismSet ρ ∈ M →
        (persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
          (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ)) ∧
      (nonidentityFormula.Realize M (cons D (cons L (cons (idealSet I) (fun _ => ZFSet.omega)))) ↔
        ∃ ρ : I ≃o I, Persistent I ρ ∧ ∃ x : I, ρ x ≠ x) := by
  let C := sourceContext M hM hT
  obtain ⟨D,hDM,hD⟩ := degree_universe C
  obtain ⟨L,hLM,hL⟩ := degree_order C
  exact ⟨D,hDM,L,hLM,hD,hL,
    fun ρ hρ => native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz,
    (realize_nonidentityFormula M hM D L (idealSet I) hDM hLM hI C.omega_mem).trans
      (native_nonidentity_absolute M hM hT hDM hLM hD hL I hI hct hz)⟩

end
end TuringRigidity.ArithmeticTree

