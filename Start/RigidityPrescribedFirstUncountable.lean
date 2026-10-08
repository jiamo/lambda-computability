import Start.RigidityValidFirstUncountable
import Start.RigidityPrescribedCoveringModel

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/PrescribedFirstUncountable.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.PrescribedFirstUncountable
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible SetDegreeDecoding
open PersistentRestrictions ArithmeticTree

theorem prescribed_covering_model_with_omega_one (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{0}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        Valid M ∧ (∃ K, InternalCountableOrdinals.FirstUncountable M K) ∧ (∀ n, A n ∈ modelReals M) ∧
        (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
          π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
        ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
          automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
          SetGenericallyPersistent M _ ρ := by
  obtain ⟨M,hM,hT,hcount,hV,hA,hi,hρ⟩ := prescribed_covering_model.{0} π A
  have hK := ValidFirstUncountable.firstUncountable_exists M hM hV ⟨realCode (A 0),hA 0⟩
  exact ⟨M,hM,hT,hcount,hV,hK,hA,hi,hρ⟩

end TuringRigidity.PrescribedFirstUncountable

