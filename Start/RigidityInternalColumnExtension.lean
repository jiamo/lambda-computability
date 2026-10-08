import Start.RigidityInternalCohenSupportedValue
import Start.RigidityInternalNameEvaluation

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/InternalColumnExtension.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.InternalColumnExtension
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

noncomputable def filterImage (A B g : ZFSet.{0}) : ZFSet.{0} :=
  (conditions B).sep (fun q => ∃ p ∈ g, ZFSet.pair p q ∈ restrictionGraph A B)

theorem filterImage_mem (N A B g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hB : B ∈ N) (hg : g ∈ N) : filterImage A B g ∈ N := by
  have hR := restrictionGraph_mem N A B hN hT hA hB
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) (cons g (fun _ => restrictionGraph A B))
    (by intro i; cases i; exact hg; exact hR) (conditions_mem N B hN hT hB)
  simpa only [filterImage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using hs

theorem projected_filter_image (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) :
    genericFilterSet (conditions B) (projected A B hBA G).carrier =
      filterImage A B (genericFilterSet (conditions A) G.carrier) := by
  apply ZFSet.ext; intro q
  rw [mem_genericFilterSet,filterImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨p,hp,hps⟩ := (mem_projected A B hBA G s).mp hs
    refine ⟨label_mem _ s,label _ p,(mem_genericFilterSet _ _ _).mpr ⟨p,hp,rfl⟩,?_⟩
    rw [←hps]
    exact (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩
  · rintro ⟨hq,p,hp,hpq⟩
    obtain ⟨r,hr,hrp⟩ := (mem_genericFilterSet (conditions A) G.carrier p).mp hp
    rw [←hrp] at hpq
    have he := ((pair_restrictionGraph A B _ q).mp hpq).2.2
    refine ⟨project A B hBA r,projected_contains A B hBA G hr,?_⟩
    exact (label_project A B hBA r).trans he.symm

theorem column_extension_subset (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M (conditions B) (projected A B hBA G).carrier ⊆
      genericExtensionSet M (conditions A) G.carrier := by
  let N := genericExtensionSet M (conditions A) G.carrier
  have hN := genericExtensionSet_transitive M (conditions A) hM G.carrier
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  have hc := conditions_mem M A hM hT hA
  have hTN : SourceT N := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) G hG ht
  have hMN : M ⊆ N := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  rw [projected_filter_image A B hBA G]
  apply filterImage_mem N A B _ hN hTN (hMN hA) (hMN hB)
  exact genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht

end TuringRigidity.InternalColumnExtension

