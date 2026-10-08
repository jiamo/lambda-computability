import Start.RigidityCheckedHierarchySyntax
import Start.RigidityCollectionHierarchyInternal
import Start.RigidityRelativeDefCertificates
import Start.RigidityRelativeModelOrdinals

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeHierarchyInternal.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem relative_internal_hierarchy_cover (M x : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      x ∈ d ∧ HierarchyGraph (relativeModel M (groundReals M)) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  have hR := groundReals_mem M hM hT
  exact internal_hierarchy_cover_collection _ _ x (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT hR)
    (relativeModel_sigma_collection M _ hM hT hR)
    ((mem_relativeModel M _ _ hM hT hR).mpr (parameter_in_relativeModel M _ hM hT)) hx

theorem relative_internal_ordinal_hierarchy (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      o.toZFSet ∈ d ∧ CheckedHierarchyGraph (relativeModel M (groundReals M))
        ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  obtain ⟨d,hd,f,hf,ho,hg⟩ := relative_internal_hierarchy_cover M o.toZFSet hM hT
    ((ground_relativeModel_ordinal_iff M hM hT o).mpr ho)
  exact ⟨d,hd,f,hf,ho,(checkedHierarchyGraph_of_context _ _ _ _ _
    (ground_relative_context M hM hT)).mpr hg⟩

end TuringRigidity.RelativeConstructible

