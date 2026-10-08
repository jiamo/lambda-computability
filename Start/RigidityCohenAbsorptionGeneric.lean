import Start.RigidityRegularTreeExtension
import Start.RigidityCohenAbsorptionTree

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenAbsorptionGeneric.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.CohenAbsorptionGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalProjectedGeneric RegularBinaryTree
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem product_generic_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G →
        ∃ W : GenericFilter (Conditions InternalCohen.conditions),
          AtomicForcing.GroundGeneric M W ∧
            genericExtensionSet M InternalCohen.conditions W.carrier =
              genericExtensionSet M c G.carrier := by
  obtain ⟨c,hc,hcs,_,_,B,hBM,hB,T,_,E,_,A,hAM,hAf,hAs,hpos,_,hm,hd,hden⟩ :=
    CohenAbsorptionTree.internal_dense_tree M q hM hT hq hct
  refine ⟨c,hc,hcs,?_⟩
  intro G hG
  have hBP := positive_mem M B hM hT hBM
  have hf : ∀ s, tree c B T E s ∈ positive B ∧
      IsCode c (tree c B T E s) ∧ tree c B T E s ≠ ∅ := by
    intro s
    have hp := ZFSet.mem_sep.mp (hpos s)
    exact ⟨hpos s,((hB _).mp hp.1).2,hp.2⟩
  have hr := tree_nil c B T E
  exact ⟨InternalCohen.pushFilter
      (RegularTreeFilter.branch c (tree c B T E) hr (fun s => (hf s).2.1) hm hd G),
    RegularTreeExtension.branch_extension_eq M c (positive B) A (tree c B T E)
      hM hT hc hBP hAM hAf hAs hf hr hm hd hden G hG⟩

end TuringRigidity.CohenAbsorptionGeneric

