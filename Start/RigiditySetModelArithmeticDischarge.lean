import Start.RigiditySetModelInternalRelations
import Start.RigiditySetModelArithmeticInterface

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/SetModelArithmeticDischarge.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open SetDegreeDecoding PersistentRestrictions PersistentPresentation
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem realClosure (C : Context M) : PersistenceRealClosure.Closed (reals M) := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  exact realClosure_of_lower_and_jump M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc

theorem persistent_sets (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    idealSet I ∈ M ∧ automorphismSet ρ ∈ M := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  exact persistent_model_sets M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc hE hEc hA hAM ρ hρ hz

theorem persistent_extension_sets (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  exact persistent_model_extension_sets M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc hE hEc hA hAM ρ hρ hz hX

end
end TuringRigidity.SetModelSyntax

