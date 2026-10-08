import Start.RigidityFiniteOrdinalCode
import Start.RigidityUniformHeightDomains

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalCodeDomains.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem paddedCode_entries_mem (A : ZFSet.{u}) (hA : Transitive A)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ A) (i : Fin n) : (v i).toZFSet ∈ A :=
  hA _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr (entry_lt_paddedCode v β i))

theorem paddedCode_padding_mem (A : ZFSet.{u}) (hA : Transitive A)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ A) : β.toZFSet ∈ A :=
  hA _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr (padding_lt_paddedCode v β))

theorem paddedCode_body_mem (A : ZFSet.{u}) (hA : Transitive A)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ A) : (vectorCode v).toZFSet ∈ A :=
  hA _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr (right_lt_pairCode _ _))

theorem padded_height_domain (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) :
    let a := paddedCode v β
    a.toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      (∀ i, (v i).toZFSet ∈ level (groundReals M) (heightDomainIndex a)) ∧
      β.toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      (vectorCode v).toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      paddedDecode n a = v ∧
      (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level (groundReals M) (heightDomainIndex a) →
        (largestOrdinalSentence.Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) e ↔
          e 0 = a.toZFSet)) := by
  have hm := largestOrdinal_ground_domain M hM hT (paddedCode v β)
    (hβ.trans (padding_lt_paddedCode v β).le)
  exact ⟨hm.1,paddedCode_entries_mem _ (level_transitive _ _) v β hm.1,
    paddedCode_padding_mem _ (level_transitive _ _) v β hm.1,
    paddedCode_body_mem _ (level_transitive _ _) v β hm.1,paddedDecode_paddedCode v β,hm.2⟩

theorem padded_height_index_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ M) :
    (heightDomainIndex (paddedCode v β)).toZFSet ∈ M :=
  heightDomainIndex_internal M hM hT _ ha

end TuringRigidity.OrdinalCoding

