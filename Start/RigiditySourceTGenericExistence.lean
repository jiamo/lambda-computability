import Start.RigiditySourceTGenericPresentation

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/SourceTGenericExistence.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals CountableForcing
universe u
noncomputable section

theorem countable_ground_generic (M : ZFSet.{u})
    (hct : (M : Set ZFSet.{u}).Countable) (hne : (M : Set ZFSet.{u}).Nonempty)
    {c : ZFSet.{u}} [Preorder (Conditions c)] (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ AtomicForcing.GroundGeneric M G := by
  classical
  obtain ⟨e,he⟩ := hct.exists_eq_range hne
  let D : ℕ → Set (Conditions c) := fun n =>
    if Dense {q | label c q ∈ e n} then {q | label c q ∈ e n} else Set.univ
  have hd : ∀ n, Dense (D n) := by
    intro n
    dsimp only [D]
    split
    · assumption
    · exact fun q => ⟨q,le_rfl,Set.mem_univ q⟩
  obtain ⟨G,hp,hG⟩ := exists_generic D hd p
  refine ⟨G,hp,?_⟩
  intro a ha had
  have har : a ∈ Set.range e := he ▸ ha
  obtain ⟨n,rfl⟩ := har
  obtain ⟨q,hq,hqd⟩ := hG n
  exact ⟨q,hq,by simpa only [D,if_pos had,Set.mem_ofPred_eq] using hqd⟩

theorem sourceT_generic_exists (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{u}).Countable)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ AtomicForcing.GroundGeneric M G ∧
      M ⊆ genericExtensionSet M c G.carrier ∧
      Transitive (genericExtensionSet M c G.carrier) ∧
      SourceT (genericExtensionSet M c G.carrier) := by
  obtain ⟨G,hp,hG⟩ := countable_ground_generic M hct ⟨c,hc⟩ p
  have ht : ⊤ ∈ G.carrier := G.upper le_top hp
  exact ⟨G,hp,hG,
    ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht,
    genericExtensionSet_transitive M c hM G.carrier,
    extension_sourceT M hM hT hc hoM ho G hG ht⟩

end
end TuringRigidity.ArithmeticTree

