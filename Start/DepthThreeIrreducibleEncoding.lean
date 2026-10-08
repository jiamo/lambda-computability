import Start.DepthThreeAlgebraPolynomial
import Start.DepthThreeIrreduciblePolynomial

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
directory `lean/OAI/Computability/DepthThree/IrreducibleEncoding.lean`, family 112,
paper "Beyond the square-root exponent for depth-three Boolean circuits".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.DepthThree*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace DepthThreeLowerBound
namespace BinaryAlgebra

def polynomialBits (P : Polynomial F2) (r : ℕ) : Fin r → Bool :=
  fun i => fieldBit (P.coeff i.val)

theorem inputPolynomialBits_polynomialBits (P : Polynomial F2) (hP : P.Monic)
    {r : ℕ} (hdegree : P.natDegree = r) :
    inputPolynomialBits (polynomialBits P r) = P := by
  ext j
  rcases lt_trichotomy j r with hj | rfl | hj
  · simpa only [polynomialBits, bitValue_fieldBit] using
      inputPolynomialBits_coeff_lt (polynomialBits P r) ⟨j, hj⟩
  · rw [inputPolynomialBits_coeff_leading]
    simpa only [hdegree] using hP.coeff_natDegree.symm
  · have hleft : (inputPolynomialBits (polynomialBits P r)).coeff j = 0 :=
      inputPolynomial_coeff_of_gt _ hj
    rw [hleft]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa only [hdegree] using hj

end BinaryAlgebra

theorem exists_irreducible_inputPolynomialBits (r : ℕ) (hr : 0 < r) :
    ∃ p : Fin r → Bool, Irreducible (BinaryAlgebra.inputPolynomialBits p) := by
  obtain ⟨P, hP, hI, hdegree⟩ := exists_monic_irreducible_natDegree_two r hr
  refine ⟨BinaryAlgebra.polynomialBits P r, ?_⟩
  rw [BinaryAlgebra.inputPolynomialBits_polynomialBits P hP hdegree]
  exact hI

end DepthThreeLowerBound

