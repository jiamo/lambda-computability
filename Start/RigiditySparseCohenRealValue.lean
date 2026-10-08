import Start.RigiditySparseCohenRealName
import Start.RigiditySparseCohenFilter

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/SparseCohenRealValue.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem val_realName (G : GenericFilter (Conditions poset)) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    realName.val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions poset) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, realName.val G.carrier = realCode A ∧
      (∀ p : Conditions poset, p ∈ G.carrier ↔ ∀ n b,
        ZFSet.pair (natSet n) (bitSet b) ∈ label poset p → A n = b) ∧
      (∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M poset G.carrier := by
  obtain ⟨A,hA⟩ := SparseCohenFilter.union_real G
    (CohenGenericUnion.union_function M ZFSet.omega hM hT
      (sourceT_omega_mem M hM hT) G hG)
  have hv := val_realName G A hA
  exact ⟨A,hv,SparseCohenFilter.mem_filter_iff_agrees G A hA,hA,
    (mem_extensionSet M poset _ _).mpr ⟨realName,realName_internal M hM hT,hv⟩⟩

end TuringRigidity.SparseCohenRealName

