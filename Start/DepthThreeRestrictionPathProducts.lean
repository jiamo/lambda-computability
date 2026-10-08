import Start.DepthThreeRestrictionExpansion
import Mathlib.Algebra.BigOperators.Fin

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/RestrictionPathProducts.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

universe u v

variable {V : Type u} {I : Type v} [DecidableEq V] [DecidableEq I] [Fintype I]

theorem pathDenominator_eq_prod_prefix (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) :
    pathDenominator scope T b violation P =
      ∏ h : Fin P.length,
        (easyCount scope T b violation (revealed scope T (P.take (h.val + 1))) : ℝ) := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih =>
      rw [pathDenominator_snoc, ih]
      rw [Fin.prod_univ_eq_prod_range
        (fun h : ℕ => (easyCount scope T b violation
          (revealed scope T (P.take (h + 1))) : ℝ)) P.length,
        Fin.prod_univ_eq_prod_range
          (fun h : ℕ => (easyCount scope T b violation
            (revealed scope T ((P ++ [i]).take (h + 1))) : ℝ)) (P ++ [i]).length]
      simp only [List.length_append, List.length_singleton, Finset.prod_range_succ]
      have hlast : (P ++ [i]).take (P.length + 1) = P ++ [i] :=
        List.take_of_length_le (by simp)
      rw [hlast]
      congr 1
      apply Finset.prod_congr rfl
      intro h hh
      rw [List.take_append_of_le_length
        (Nat.succ_le_of_lt (Finset.mem_range.mp hh))]

theorem pathNumerator_eq_indicator_support (violation : I → Bool) (P : List I) :
    pathNumerator violation P = if ∀ i ∈ P, violation i = true then 1 else 0 := by
  classical
  by_cases hs : ∀ i ∈ P, violation i = true
  · rw [if_pos hs]
    unfold pathNumerator
    apply List.prod_eq_one
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    simp [violationValue, hs i hi]
  · rw [if_neg hs]
    by_contra hne
    exact hs ((pathNumerator_ne_zero_iff violation P).mp hne)

theorem pathTerm_eq_support_prod_inv (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) :
    pathTerm scope T b violation P =
      if ∀ i ∈ P, violation i = true then
        ∏ h : Fin P.length,
          (easyCount scope T b violation
            (revealed scope T (P.take (h.val + 1))) : ℝ)⁻¹
      else 0 := by
  classical
  by_cases hs : ∀ i ∈ P, violation i = true
  · simp only [pathTerm, pathNumerator_eq_indicator_support, if_pos hs,
      pathDenominator_eq_prod_prefix, one_div, Finset.prod_inv_distrib]
  · simp only [pathTerm, pathNumerator_eq_indicator_support, if_neg hs, zero_div]

end DepthThreeLowerBound

end

