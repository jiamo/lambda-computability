import Mathlib.FieldTheory.Finite.GaloisField

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/IrreduciblePolynomial.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace DepthThreeLowerBound

theorem exists_monic_irreducible_natDegree_two (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial (ZMod 2),
      P.Monic ∧ Irreducible P ∧ P.natDegree = r := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top
    (ZMod 2) (GaloisField 2 r)
  have hαint : IsIntegral (ZMod 2) α := IsIntegral.of_finite (ZMod 2) α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hαint,
    minpoly.irreducible hαint, ?_⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq
    (ZMod 2) α).mp hα).trans
      (GaloisField.finrank 2 (Nat.ne_of_gt hr))

theorem exists_monic_irreducible_degree_two (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial (ZMod 2),
      P.Monic ∧ Irreducible P ∧ P.degree = (r : WithBot ℕ) := by
  obtain ⟨P, hP, hI, hdegree⟩ := exists_monic_irreducible_natDegree_two r hr
  refine ⟨P, hP, hI, ?_⟩
  rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdegree]

end DepthThreeLowerBound

