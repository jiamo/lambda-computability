import Start.DepthThreeHardSliceProbability
import Start.DepthThreeHardSliceSelection

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/HardSliceExistence.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem actual_hash_coefficient_window_failure_le {d r h b : ℕ}
    (p : Fin r → Bool) [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hr : 0 < r) (hb : 1 ≤ b) (hh : 0 < h) (q : ℝ)
    (σ : Restriction (Fin d)) (hσ : restrictionWindow q σ)
    (hbound :
      (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r +
        sparseMomentBound (Fintype.card (Live σ)) b
          (hardSliceSparseConstant b hb * Fintype.card (Live σ)) h
          ((2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 4)) ≤
      2 * (2 : ℝ) ^ (-(q * d) / 16)) :
    finiteProb (fun ω : (Fin (d + r - 1) → Bool) ×
        (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
      ¬ corr b (fun z => sign (hashAcceptance p (2 * h) ω.1 ω.2 (fill σ z))) ≤
        (2 : ℝ) ^ (-(q * d) / 16)) ≤
      2 * (2 : ℝ) ^ (-(q * d) / 16) := by
  have hlow : (q * d) / 2 ≤ (Fintype.card (Live σ) : ℝ) := by
    simpa only [restrictionWindow, Fintype.card_fin] using hσ.1
  have hthreshold : (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 8) ≤
      (2 : ℝ) ^ (-(q * d) / 16) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  apply le_trans _ ((actual_hash_coefficient_failure_le p hr σ b hb h hh).trans hbound)
  apply finiteProb_mono
  intro ω hω hsmall
  exact hω (hsmall.trans hthreshold)

theorem exists_good_hash_coefficients {d r h b : ℕ}
    (p : Fin r → Bool) [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hr : 0 < r) (hb : 1 ≤ b) (hh : 0 < h) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hbound : ∀ m : ℕ, (q * d) / 2 ≤ (m : ℝ) → (m : ℝ) ≤ 2 * (q * d) →
      (2 : ℝ) ^ m / (2 : ℝ) ^ r +
        sparseMomentBound m b (hardSliceSparseConstant b hb * m) h
          ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤ 2 * (2 : ℝ) ^ (-(q * d) / 16)) :
    ∃ (u : Fin (d + r - 1) → Bool) (β : Fin (2 * h) → BinaryAlgebra.BitQuotient p),
      restrictionAvg q (fun σ => if ¬ goodRestriction q
        ((2 : ℝ) ^ (-(q * d) / 16)) b (hashAcceptance p (2 * h) u β) σ
        then 1 else 0) ≤ 4 * (2 : ℝ) ^ (-(q * d) / 16) := by
  have hfixed (σ : Restriction (Fin d)) (hσ : restrictionWindow q σ) :
      finiteProb (fun ω : (Fin (d + r - 1) → Bool) ×
          (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
        ¬ corr b (fun z => sign (hashAcceptance p (2 * h) ω.1 ω.2 (fill σ z))) ≤
          (2 : ℝ) ^ (-(q * d) / 16)) ≤
        2 * (2 : ℝ) ^ (-(q * d) / 16) := by
    apply actual_hash_coefficient_window_failure_le p hr hb hh q σ hσ
    apply hbound
    · simpa only [restrictionWindow, Fintype.card_fin] using hσ.1
    · simpa only [restrictionWindow, Fintype.card_fin] using hσ.2
  obtain ⟨ω, hω⟩ := exists_good_parameter hq hq1 b
    (fun ω : (Fin (d + r - 1) → Bool) × (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
      hashAcceptance p (2 * h) ω.1 ω.2)
    (by simpa only [Fintype.card_fin] using hfixed)
  exact ⟨ω.1, ω.2, by simpa only [Fintype.card_fin] using hω⟩

def coefficientInputBits {r t : ℕ} (p : Fin r → Bool)
    (β : Fin t → BinaryAlgebra.BitQuotient p) : Fin t → Fin r → Bool :=
  fun j i => BinaryAlgebra.fieldBit
    (BinaryAlgebra.coordinates (fun i => BinaryAlgebra.bitValue (p i)) (β j) i)

@[simp] theorem encode_coefficientInputBits {r t : ℕ} (p : Fin r → Bool)
    (β : Fin t → BinaryAlgebra.BitQuotient p) (j : Fin t) :
    BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
      (fun i => BinaryAlgebra.bitValue (coefficientInputBits p β j i)) = β j := by
  simp only [coefficientInputBits, BinaryAlgebra.bitValue_fieldBit]
  exact BinaryAlgebra.encode_coordinates _ _

theorem hashAcceptance_coefficientInputBits {d r t : ℕ} (p : Fin r → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (u : Fin (d + r - 1) → Bool) (β : Fin t → BinaryAlgebra.BitQuotient p) :
    hashAcceptance p t u
      (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
        (fun i => BinaryAlgebra.bitValue (coefficientInputBits p β j i))) =
      hashAcceptance p t u β := by
  simp only [encode_coefficientInputBits]

end DepthThreeLowerBound

end

