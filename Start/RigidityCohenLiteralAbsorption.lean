import Start.RigidityCohenPrefixDensity
import Start.RigidityDenseInclusionExtension
import Start.RigidityCohenIteratedAbsorption

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenLiteralAbsorption.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.CohenLiteralAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion CohenPrefixDensity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prefix_transport (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (W : GenericFilter (Conditions InternalCohen.conditions)) (hW : AtomicForcing.GroundGeneric M W) :
    let K := push InternalCohen.conditions (CohenGroundPoset.conditions ZFSet.omega) conditions_subset W
    AtomicForcing.GroundGeneric M K ∧
      genericExtensionSet M (CohenGroundPoset.conditions ZFSet.omega) K.carrier =
        genericExtensionSet M InternalCohen.conditions W.carrier := by
  have ha := InternalCohen.conditions_mem M hM hT
  have hb := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  exact ⟨push_ground_generic M _ _ hM hT ha hb conditions_subset dense_inclusion W hW,
    DenseInclusionExtension.extension_eq M _ _ hM hT ha hb conditions_subset dense_inclusion W hW⟩

theorem same_generics_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) H) :
    ∃ K : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)),
      AtomicForcing.GroundGeneric M K ∧
        genericExtensionSet M (CohenGroundPoset.conditions ZFSet.omega) K.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier)
            (CohenGroundPoset.conditions ZFSet.omega) H.carrier := by
  obtain ⟨W,hW,hWe⟩ := CohenIteratedAbsorption.same_generics_absorption M q hM hT hq hct G hG H hH
  obtain ⟨hK,hKe⟩ := prefix_transport M hM hT W hW
  exact ⟨_,hK,hKe.trans hWe⟩

end TuringRigidity.CohenLiteralAbsorption

