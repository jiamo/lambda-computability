import Start.RigidityPrescribedModelRestriction

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/PrescribedCoveringModel.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel RelationCollapse SetDegreeDecoding
open PersistentRestrictions ArithmeticTree
universe u

theorem prescribed_covering_model (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{u}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        Valid M ∧ (∀ n, A n ∈ modelReals M) ∧
        (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
          π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
        ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
          automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
          SetGenericallyPersistent M _ ρ := by
  obtain ⟨B,hB⟩ := degree_surjective
    (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)))
  let S : ℕ → Oracle | 0 => B | n+1 => A n
  let M := collapsed (hullSet (realSeed.{u} S))
  have hM : Transitive M := collapsed_transitive _
  have hT : SourceT M := collapsed_hull_sourceT _
  have hs (n : ℕ) : S n ∈ modelReals M :=
    (mem_collapsed _ _).mpr ⟨realCode (S n),seed_reals S n,(collapse_real_fixed S n).symm⟩
  have hi : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier :=
    ⟨B,hs 0,hB⟩
  exact ⟨M,hM,hT,inferInstance,collapsed_hull_valid _,fun n => hs (n+1),hi,
    prescribed_model_restriction π M hM hT hi⟩

end TuringRigidity.RelativeConstructible

