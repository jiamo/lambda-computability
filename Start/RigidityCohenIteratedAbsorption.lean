import Start.RigidityCohenAbsorptionGeneric
import Start.RigidityTaggedProductExtension

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenIteratedAbsorption.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.CohenIteratedAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem same_generics_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) H) :
    ∃ W : GenericFilter (Conditions InternalCohen.conditions),
      AtomicForcing.GroundGeneric M W ∧
        genericExtensionSet M InternalCohen.conditions W.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier)
            (CohenGroundPoset.conditions ZFSet.omega) H.carrier := by
  obtain ⟨c,hc,hcs,habs⟩ := CohenAbsorptionGeneric.product_generic_absorption M q hM hT hq hct
  have hb := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  let J := TaggedProductGeneric.joint q (CohenGroundPoset.conditions ZFSet.omega) c hcs G H
  have hJ := TaggedProductGeneric.joint_ground_generic M q _ c hM hT hq hb hcs G hG H hH
  obtain ⟨W,hW,hWe⟩ := habs J hJ
  exact ⟨W,hW,hWe.trans (TaggedProductExtension.extension_eq M q _ c hM hT hq hb hc hcs G hG H hH)⟩

end TuringRigidity.CohenIteratedAbsorption

