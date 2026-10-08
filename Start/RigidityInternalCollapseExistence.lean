import Start.RigidityInternalCollapseCounting
import Start.RigidityCountableGroundGeneric

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/InternalCollapseExistence.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem exists_internal_counting_extension (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {A : ZFSet.{u}} (hA : A ∈ M)
    (hne : ∃ x, x ∈ A) :
    ∃ c ∈ M, orderSet c ∈ M ∧
      (∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) ∧
      ∃ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G ∧
        M ⊆ genericExtensionSet M c G.carrier ∧
        Transitive (genericExtensionSet M c G.carrier) ∧
        SourceT (genericExtensionSet M c G.carrier) ∧
        InternallyCountable (genericExtensionSet M c G.carrier) A := by
  classical
  obtain ⟨c,hcM,hc⟩ := conditions_exist M hM hT hA
  have h0M : (∅ : ZFSet.{u}) ∈ M := hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero
  have h0 : (∅ : ZFSet.{u}) ∈ c := (hc ∅).mpr ⟨h0M,prefix_empty A⟩
  let _ := top c h0
  obtain ⟨G,htop,hG⟩ := AtomicForcing.countable_ground_generic M ⟨∅,h0M⟩ (⊤ : Conditions c)
  refine ⟨c,hcM,orderSet_mem M hM hT hcM,hc,G,hG,?_,?_,?_,?_⟩
  · exact ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      hT.replacement.finitePrefix hT.infinity hcM G.carrier htop
  · exact genericExtensionSet_transitive M c hM G.carrier
  · exact extension_sourceT M hM hT hcM (orderSet_mem M hM hT hcM) (orderSet_pair c) G hG htop
  · exact internal_counting M hM hT hA hcM hc hne G hG

end TuringRigidity.BoundedSetTheory.InternalCollapse

