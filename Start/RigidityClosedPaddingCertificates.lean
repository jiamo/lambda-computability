import Start.RigidityRecursiveOmegaBound
import Start.RigidityInternalOmegaFixedPoint
import Start.RigidityVectorCodeLevels

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/ClosedPaddingCertificates.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem padded_certificates_of_lower_closure (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) (hoff : realSeedOffset+β=β) (hv : vectorCode v < β)
    (hvec : VectorCodeCertificates (level (groundReals M) β) v)
    (hpow : ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet) :
    PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v β := by
  let R := groundReals M
  let c := paddedCode v β
  let δ := heightDomainIndex c
  have hβpos : 0 < β := hβ.bot_lt
  have hβc : β < c := padding_lt_paddedCode v β
  have hcodeabs := offset_absorbed_above realSeedOffset β c hoff hβc.le
  have hδ : δ=c+1 := heightDomainIndex_of_absorbed c hcodeabs
  have hβδ : β ≤ δ := hβc.le.trans (hδ ▸ le_self_add)
  have hcut : ordinalHeight (seed R)+c=c := by rw [ground_seed_offset M hM hT]; exact hcodeabs
  have hmem (a : Ordinal.{u}) (ha : a ≤ c) : a.toZFSet ∈ level R δ := by
    rw [hδ,ordinal_mem_level_iff,← add_assoc,hcut]
    exact Order.lt_add_one_iff.mpr ha
  have hb1 : β+1 ≤ c := Order.add_one_le_iff.mpr hβc
  have hu : Ordinal.omega0 ^ (β+1) < c := by
    change Ordinal.omega0 ^ (β+1) < pairCode β (vectorCode v)
    rw [pairCode,if_pos hv.le]
    simpa only [add_zero] using (add_lt_add_iff_left (Ordinal.omega0 ^ (β+1))).mpr
      (Ordinal.opow_pos (vectorCode v) Ordinal.omega0_pos)
  have hvpow := level_mono R hβδ (hpow (vectorCode v) hv).1
  have hcβ := padded_omega_boundary_certificates M hM hT v β hβ hoff hv.le hpow
    (omega_boundary_product_without_offset M hM hT β hβpos)
  have hck := (hpow (vectorCode v) hv).2.mono (level_mono R hβδ)
  have hsum := padded_final_sum_certificates M hM hT v β hβpos hoff hv.le
  refine ⟨hmem β hβc.le,hmem (vectorCode v) (hv.trans hβc).le,?_,hvec.mono (level_mono R hβδ)⟩
  rw [PairCodeCertificates,if_pos hv.le]
  exact ⟨hmem (β+1) hb1,hmem _ hu.le,hvpow,hmem _ hu.le,hcβ,hck,
    fun h => Bool.noConfusion h,hsum⟩

end TuringRigidity.OrdinalCoding

