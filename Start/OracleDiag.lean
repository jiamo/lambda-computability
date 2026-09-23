/-
**The counting step of a diagonalization against polynomial-time oracle machines.**

A stage-wise construction of a separating oracle (Baker–Gill–Solovay) rests on one combinatorial
fact: on an input of length `n`, a polynomial-time oracle machine asks the oracle about fewer
than `2 ^ n` words as soon as `n` is large, so some word of length `n` is left unasked and the
construction is free to decide its membership afterwards.  This file proves that fact for the
oracle Cobham terms of `Start/OracleCob.lean`.

* `Complexity.exists_mul_pow_lt_two_pow` — `c · n ^ k < 2 ^ n` from some point on;
* `Complexity.PolyMono.lt_two_pow` — a monotone polynomial bound is eventually below `2 ^ n`;
* `Complexity.card_words_of_length` — there are `2 ^ n` words of length `n`;
* `Complexity.exists_word_length_not_mem` — a list shorter than `2 ^ n` misses a word of
  length `n`;
* `Complexity.CobQ.exists_word_not_queried` — **the diagonalization step**: for each oracle term
  there is an `n₀` such that on arguments of length at most `n ≥ n₀`, with any oracle, some word
  of length `n` is not queried;
* `Complexity.CobQ.exists_word_not_queried_unary` — the same on the unary input `1^n`, which is
  the shape the Baker–Gill–Solovay language uses.
-/

import Mathlib
import Start.OracleCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Filter

/-- **A polynomial is eventually below the exponential.** -/
theorem exists_mul_pow_lt_two_pow (c k : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, c * n ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) (by norm_num)
  have hpos : (0 : ℝ) < 1 / (c + 1) := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ k / 2 ^ n) < 1 / (c + 1) :=
    h.eventually_lt_const hpos
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  have hlt := hn₀ n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hc : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have h3 : (n : ℝ) ^ k < 1 / ((c : ℝ) + 1) * 2 ^ n := (div_lt_iff₀ h2).mp hlt
  have h4 : ((c : ℝ) + 1) * (n : ℝ) ^ k < ((c : ℝ) + 1) * (1 / ((c : ℝ) + 1) * 2 ^ n) :=
    mul_lt_mul_of_pos_left h3 hc
  have h5 : ((c : ℝ) + 1) * (1 / ((c : ℝ) + 1) * 2 ^ n) = 2 ^ n := by field_simp
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hcast : (c : ℝ) * (n : ℝ) ^ k < 2 ^ n := by nlinarith
  have : ((c * n ^ k : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; exact hcast
  exact_mod_cast this

/-- A monotone polynomial bound is eventually below `2 ^ n`. -/
theorem PolyMono.lt_two_pow {p : ℕ → ℕ} (hp : PolyMono p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, p n < 2 ^ n := by
  obtain ⟨a, k, ha⟩ := hp.1
  obtain ⟨m₀, hm₀⟩ := exists_mul_pow_lt_two_pow (a * 2 ^ k) k
  refine ⟨max m₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnm : m₀ ≤ n := le_trans (le_max_left _ _) hn
  have hstep : (n + 1) ^ k ≤ 2 ^ k * n ^ k := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left (by omega) k
  calc p n ≤ a * (n + 1) ^ k := ha n
    _ ≤ a * (2 ^ k * n ^ k) := Nat.mul_le_mul_left a hstep
    _ = a * 2 ^ k * n ^ k := by ring
    _ < 2 ^ n := hm₀ n hnm

/-! ### Counting the words of a given length -/

/-- There are `2 ^ n` words of length `n`. -/
theorem card_words_of_length (n : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).image fun v => List.ofFn v).card = 2 ^ n := by
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- A list of fewer than `2 ^ n` words misses a word of length `n`. -/
theorem exists_word_length_not_mem {Q : List Word} {n : ℕ} (h : Q.length < 2 ^ n) :
    ∃ w : Word, w.length = n ∧ w ∉ Q := by
  by_contra hcon
  have hall : ∀ w : Word, w.length = n → w ∈ Q := by
    intro w hw
    by_contra hmem
    exact hcon ⟨w, hw, hmem⟩
  have hsub : ((Finset.univ : Finset (Fin n → Bool)).image fun v => List.ofFn v) ⊆ Q.toFinset := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hu
    exact List.mem_toFinset.2 (hall _ (by simp))
  have hcard := Finset.card_le_card hsub
  rw [card_words_of_length] at hcard
  have := Q.toFinset_card_le
  omega

namespace CobQ

/-- **The diagonalization step.**  For every polynomial-time oracle machine there is a length
from which on, whatever the oracle and whatever the arguments of that length, some word of that
length is never asked about.  This is what leaves a stage-wise construction free to put a word of
length `n` into the oracle, or to keep it out, without disturbing the run. -/
theorem exists_word_not_queried (t : CobQ) :
    ∃ n₀ : ℕ, ∀ (A : Oracle) (args : List Word) (n : ℕ), n₀ ≤ n → maxLen args ≤ n →
      ∃ w : Word, w.length = n ∧ w ∉ queries A t args := by
  obtain ⟨p, hp, hcount⟩ := polyQueryCount t
  obtain ⟨n₀, hn₀⟩ := hp.lt_two_pow
  refine ⟨n₀, fun A args n hn hargs => ?_⟩
  refine exists_word_length_not_mem (Q := queries A t args) ?_
  calc (queries A t args).length ≤ p (maxLen args) := hcount A args
    _ ≤ p n := hp.2 hargs
    _ < 2 ^ n := hn₀ n hn

/-- The same on the unary input `1^n`, the shape used by the Baker–Gill–Solovay language. -/
theorem exists_word_not_queried_unary (t : CobQ) :
    ∃ n₀ : ℕ, ∀ (A : Oracle) (n : ℕ), n₀ ≤ n →
      ∃ w : Word, w.length = n ∧ w ∉ queries A t [List.replicate n Bool.true] := by
  obtain ⟨n₀, h⟩ := exists_word_not_queried t
  refine ⟨n₀, fun A n hn => h A [List.replicate n Bool.true] n hn ?_⟩
  simp [maxLen]

end CobQ

end Complexity
