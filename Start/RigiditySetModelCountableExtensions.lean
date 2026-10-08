import Start.RigiditySetModelPresentedCountability

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/SetModelCountableExtensions.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem persistent_countable_extensions (C : Context M) (hCh : InternalChoice M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M ∧ InternallyCountable M (idealSet J) := by
  obtain ⟨A,hAM,hA⟩ := countable_presentation C hCh I hI hct
  let B := join A X
  let J := JumpIdeal.generated (degree B)
  let H := JumpIdealPresentation.presentation B
  have hH : Presented J H := JumpIdealPresentation.presents B
  have hHM : H ∈ reals M := (realClosure C).presentation ((realClosure C).join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := by
    intro y hy
    obtain ⟨n,rfl⟩ := (hA y).mp hy
    exact J.lower ((CodingExtraction.column_projection_reduces A n).trans
      (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ,he,hσ⟩ := PersistentExtension.source_4_1_10 I J ρ hρ hz hIJ (JumpIdeal.closed _)
  have hs := persistent_sets C hH hHM σ hσ (hIJ hz)
  exact ⟨J,σ,hIJ,hXJ,he,hσ,hs.1,hs.2,countable_of_presentation C hH hHM⟩

end
end TuringRigidity.SetModelCountability

