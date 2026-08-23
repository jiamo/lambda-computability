/-
The converse of Kraft's inequality.

`Start/Kraft.lean` proves Kraft's inequality: the weights `2 ^ (-|w|)` of a prefix free family of
bit strings sum to at most `1`.  This file proves the converse for a non-decreasing sequence of
lengths: whenever `n : ℕ → ℕ` is monotone and every finite Kraft sum `∑_{i < N} 2 ^ (-n i)` is at
most `1`, there really is a prefix free coding whose `i`-th code word has length `n i`.

The construction is the classical one, carried out entirely in `ℕ` so that no real binary
expansions are needed.  Put

  `kraftIndex n i = ∑_{j < i} 2 ^ (n i - n j)`,

the partial Kraft sum rescaled by `2 ^ n i`; monotonicity of the lengths makes it a natural
number.  The Kraft hypothesis says exactly that `kraftIndex n i < 2 ^ n i`, so it has an `n i`-bit
binary representation, and that is the `i`-th code word.  Prefix freeness comes from the estimate
`kraftIndex n j ≥ (kraftIndex n i + 1) * 2 ^ (n j - n i)` for `i < j`: truncating the `j`-th code
word to `n i` bits already overshoots the `i`-th one.

Combined with `Kraft.sum_wt_le_one` this gives the exact characterization
`Kraft.exists_prefixFree_iff`: for monotone lengths, a prefix free coding with those lengths
exists if and only if all finite Kraft sums are at most `1`.
-/

import Start.Kraft

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Kraft

open scoped BigOperators

------------------------------------------------------------------------
-- Fixed-width binary representations
------------------------------------------------------------------------

/-- The `len`-bit big-endian binary representation of `a`. -/
def bitsOfNat (len a : ℕ) : List Bool :=
  (List.range len).map fun i => a.testBit (len - 1 - i)

@[simp]
theorem length_bitsOfNat (len a : ℕ) : (bitsOfNat len a).length = len := by
  simp [bitsOfNat]

theorem testBit_eq_false_of_lt_pow {a m j : ℕ} (ha : a < 2 ^ m) (hj : m ≤ j) :
    a.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hj))

/-- Truncating a fixed-width representation to a prefix divides by a power of two. -/
theorem eq_div_of_bitsOfNat_prefix {m n a b : ℕ} (hb : b < 2 ^ n) (ha : a < 2 ^ m)
    (h : bitsOfNat m a <+: bitsOfNat n b) : a = b / 2 ^ (n - m) := by
  have hmn : m ≤ n := by
    have := h.length_le
    simpa using this
  have htake : (bitsOfNat n b).take m = bitsOfNat m a := by
    have := List.prefix_iff_eq_take.1 h
    rw [length_bitsOfNat] at this
    exact this.symm
  have hbits : ∀ i < m, a.testBit (m - 1 - i) = b.testBit (n - 1 - i) := by
    intro i hi
    have hlen : i < ((bitsOfNat n b).take m).length := by
      rw [List.length_take, length_bitsOfNat]
      omega
    have h1 : ((bitsOfNat n b).take m)[i] = b.testBit (n - 1 - i) := by
      rw [List.getElem_take]
      simp [bitsOfNat, List.getElem_map, List.getElem_range]
    have h2 : ((bitsOfNat n b).take m)[i]'hlen = (bitsOfNat m a)[i]'(by simp [hi]) := by
      simp only [htake]
    rw [h1] at h2
    rw [h2]
    simp [bitsOfNat, List.getElem_map, List.getElem_range]
  refine Nat.eq_of_testBit_eq fun k => ?_
  rcases lt_or_ge k m with hk | hk
  · have := hbits (m - 1 - k) (by omega)
    have hk1 : m - 1 - (m - 1 - k) = k := by omega
    have hk2 : n - 1 - (m - 1 - k) = k + (n - m) := by omega
    rw [hk1, hk2] at this
    rw [this, Nat.testBit_div_two_pow]
  · have hbdiv : b / 2 ^ (n - m) < 2 ^ m := by
      have : b < 2 ^ m * 2 ^ (n - m) := by
        rw [← pow_add]
        have : m + (n - m) = n := by omega
        rw [this]
        exact hb
      exact Nat.div_lt_of_lt_mul (by linarith [this])
    rw [testBit_eq_false_of_lt_pow ha hk, testBit_eq_false_of_lt_pow hbdiv hk]

------------------------------------------------------------------------
-- The construction
------------------------------------------------------------------------

variable (n : ℕ → ℕ)

/-- The partial Kraft sum below `i`, rescaled by `2 ^ n i`: a natural number as soon as the
lengths are non-decreasing. -/
def kraftIndex (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, 2 ^ (n i - n j)

/-- The code word attached to `i`: the `n i`-bit binary representation of `kraftIndex n i`. -/
def kraftCode (i : ℕ) : List Bool := bitsOfNat (n i) (kraftIndex n i)

@[simp]
theorem length_kraftCode (i : ℕ) : (kraftCode n i).length = n i := by
  simp [kraftCode]

variable {n}

/-- The Kraft hypothesis, in the form used below: every finite Kraft sum is at most `1`. -/
theorem kraftIndex_lt (hmono : Monotone n)
    (hk : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((2 : ℝ)⁻¹ ^ n i) ≤ 1) (i : ℕ) :
    kraftIndex n i < 2 ^ n i := by
  have hcast : (kraftIndex n i : ℝ)
      = 2 ^ n i * ∑ j ∈ Finset.range i, ((2 : ℝ)⁻¹ ^ n j) := by
    rw [kraftIndex, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : n j ≤ n i := hmono (le_of_lt (Finset.mem_range.1 hj))
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hji, inv_pow]
  have hsum := hk (i + 1)
  rw [Finset.sum_range_succ] at hsum
  have hpos : (0 : ℝ) < 2 ^ n i := by positivity
  have hmul : 2 ^ n i * (∑ j ∈ Finset.range i, ((2 : ℝ)⁻¹ ^ n j)) + 1 ≤ 2 ^ n i := by
    have := mul_le_mul_of_nonneg_left hsum (le_of_lt hpos)
    rw [mul_add, mul_one] at this
    have hone : (2 : ℝ) ^ n i * ((2 : ℝ)⁻¹ ^ n i) = 1 := by
      rw [inv_pow, mul_inv_cancel₀ (by positivity)]
    rw [hone] at this
    exact this
  rw [← hcast] at hmul
  have : (kraftIndex n i : ℝ) + 1 ≤ ((2 ^ n i : ℕ) : ℝ) := by push_cast; exact hmul
  have hnat : kraftIndex n i + 1 ≤ 2 ^ n i := by exact_mod_cast this
  omega

/-- The gap estimate: passing from `i` to a later index adds at least one whole block. -/
theorem le_kraftIndex (hmono : Monotone n) {i j : ℕ} (hij : i < j) :
    (kraftIndex n i + 1) * 2 ^ (n j - n i) ≤ kraftIndex n j := by
  have hni : n i ≤ n j := hmono hij.le
  have hsplit : ∑ l ∈ Finset.range (i + 1), 2 ^ (n j - n l) ≤ kraftIndex n j :=
    Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega)
  rw [Finset.sum_range_succ] at hsplit
  have hfirst : ∑ l ∈ Finset.range i, 2 ^ (n j - n l)
      = kraftIndex n i * 2 ^ (n j - n i) := by
    rw [kraftIndex, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hli : n l ≤ n i := hmono (le_of_lt (Finset.mem_range.1 hl))
    rw [← pow_add]
    congr 1
    omega
  rw [hfirst] at hsplit
  calc (kraftIndex n i + 1) * 2 ^ (n j - n i)
      = kraftIndex n i * 2 ^ (n j - n i) + 2 ^ (n j - n i) := by ring
    _ ≤ kraftIndex n j := hsplit

/-- **The converse of Kraft's inequality.**  For a non-decreasing sequence of lengths satisfying
the Kraft inequality there is a prefix free coding realizing exactly those lengths. -/
theorem prefixFreeCoding_kraftCode (hmono : Monotone n)
    (hk : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((2 : ℝ)⁻¹ ^ n i) ≤ 1) :
    PrefixFreeCoding (kraftCode n) := by
  have hlt := kraftIndex_lt hmono hk
  intro i j hpre
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hij
  · have hdiv : kraftIndex n i = kraftIndex n j / 2 ^ (n j - n i) :=
      eq_div_of_bitsOfNat_prefix (hlt j) (hlt i) hpre
    have hge := le_kraftIndex hmono hij
    have hle : kraftIndex n i + 1 ≤ kraftIndex n j / 2 ^ (n j - n i) :=
      Nat.le_div_iff_mul_le (Nat.two_pow_pos _) |>.2 hge
    omega
  · have hlen : n i ≤ n j := by
      have := hpre.length_le
      simpa using this
    have hji : n j ≤ n i := hmono hij.le
    have hnij : n j = n i := le_antisymm hji hlen
    have hdiv : kraftIndex n i = kraftIndex n j / 2 ^ (n j - n i) :=
      eq_div_of_bitsOfNat_prefix (hlt j) (hlt i) hpre
    rw [hnij] at hdiv
    simp at hdiv
    have hge := le_kraftIndex hmono hij
    rw [hnij] at hge
    simp at hge
    omega

/-- The characterization of the possible length sequences of a prefix free coding, for
non-decreasing lengths: Kraft's inequality is necessary and sufficient. -/
theorem exists_prefixFree_iff (hmono : Monotone n) :
    (∃ c : ℕ → List Bool, (∀ i, (c i).length = n i) ∧ PrefixFreeCoding c) ↔
      ∀ N : ℕ, ∑ i ∈ Finset.range N, ((2 : ℝ)⁻¹ ^ n i) ≤ 1 := by
  constructor
  · rintro ⟨c, hlen, hc⟩ N
    have := sum_wt_le_one hc (Finset.range N)
    simpa [wt, hlen] using this
  · intro hk
    exact ⟨kraftCode n, length_kraftCode n, prefixFreeCoding_kraftCode hmono hk⟩

end Kraft
