import Start.RigiditySourceTPresentationComparison

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/SourceTGenericPresentation.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals
universe u
noncomputable section

theorem generic_presentation_comparison (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : CountableForcing.GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (htop : ⊤ ∈ G.carrier) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) :
    (InternalPresentation M A R ↔ InternalPresentation (genericExtensionSet M c G.carrier) A R) ∧
    (InternalNonidentity M A ↔ InternalNonidentity (genericExtensionSet M c G.carrier) A) := by
  have hsub := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier htop
  have hAE : A ∈ reals (genericExtensionSet M c G.carrier) := by
    change realSet.{u} A ∈ genericExtensionSet M c G.carrier
    exact hsub hA
  have hRE : R ∈ reals (genericExtensionSet M c G.carrier) := by
    change realSet.{u} R ∈ genericExtensionSet M c G.carrier
    exact hsub hR
  exact presentation_comparison M _ hM (genericExtensionSet_transitive M c hM G.carrier)
    hT (extension_sourceT M hM hT hc hoM ho G hG htop) A R hA hAE hR hRE

end
end TuringRigidity.ArithmeticTree

