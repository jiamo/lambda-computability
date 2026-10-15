import Start.KolmogorovCountLower

/-!
# A short index code: numbers below `N` as closed terms of size `3 log₂ N + O(1)`

Task `M19-INDEX-CODE-RATE`.

`Start/KolmogorovCountLower.lean` writes a number below `2^j` as a nest of `j` realizers, one per
bit, at a cost of `55` per bit.  Here the two digit realizers are bound once, by a pair of
abstractions, and each bit is a de Bruijn index of size `1` or `2` applied to the rest:

`binProg l = (λ λ. d_{b₁} (d_{b₂} (… (d_{bⱼ} ⌜0⌝)…))) dblTerm dblOneTerm`,

where `d_false = var 1` (bound to `dblTerm`, `n ↦ 2n`) and `d_true = var 0` (bound to
`dblOneTerm`, `n ↦ 2n+1`).  Each bit costs at most `3`.

* `Lambda.binProg_isProgramFor` — `binProg l` is a program for `binVal l`.
* `Lambda.size_binProg_le` — `size (binProg l) ≤ 97 + 3 · |l|`.
* **`Lambda.kolm_le_of_lt_two_pow_index`** — every `n < 2^j` has `kolm n ≤ 97 + 3 j`.
* **`Lambda.kolm_le_three_log`** — every `i < N` has `kolm i ≤ 3 · log₂ N + 100`: the constant is
  `C = 3` per bit, against `55` for the nested realizers.
* **`Lambda.kolm_index_rate_lower`** — no constant below `1/2` per bit is possible: for
  `2p < q` there is no `c` with `q · kolm i ≤ p · log₂ N + c` for all `i < N` (from the counting
  bound `Lambda.card_kolm_le`, through `Lambda.exists_le_four_pow_kolm_gt`).
-/

set_option autoImplicit false

noncomputable section

namespace Lambda

/-- The value of a little-endian bit list. -/
def binVal : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * binVal l + (if b then 1 else 0)

/-- The body: a word in `var 1` (bit `false`) and `var 0` (bit `true`) applied to `⌜0⌝`. -/
def binBody : List Bool → Lambda
  | [] => Lambda.church 0
  | b :: l => Lambda.app (Lambda.var (if b then 0 else 1)) (binBody l)

/-- The same word with the two digit realizers substituted. -/
def binWord : List Bool → Lambda
  | [] => Lambda.church 0
  | b :: l => Lambda.app (if b then dblOneTerm else dblTerm) (binWord l)

/-- The index program for a bit list. -/
def binProg (l : List Bool) : Lambda :=
  Lambda.app (Lambda.app (Lambda.lam (Lambda.lam (binBody l))) dblTerm) dblOneTerm

theorem dblTerm_closed : Lambda.IsClosed dblTerm := realizes_dblTerm.1

theorem dblOneTerm_closed : Lambda.IsClosed dblOneTerm := realizes_dblOneTerm.1

theorem subst_binBody_high (l : List Bool) (s : Lambda) (x : ℕ) :
    Lambda.subst s (x + 2) (binBody l) = binBody l := by
  induction l with
  | nil => exact Lambda.IsClosed_imp_subst_eq (Lambda.church_closed 0) _ _
  | cons b l ih =>
      cases b <;> simp [binBody, Lambda.subst, ih]

theorem binProg_closed (l : List Bool) : Lambda.IsClosed (binProg l) := by
  refine Lambda.IsClosed_app (Lambda.IsClosed_app ?_ dblTerm_closed) dblOneTerm_closed
  intro s x
  simp only [Lambda.subst, subst_binBody_high]

theorem subst_binBody (l : List Bool) :
    Lambda.subst dblOneTerm 0 (Lambda.subst dblTerm 1 (binBody l)) = binWord l := by
  induction l with
  | nil =>
      simp only [binBody, binWord, Lambda.IsClosed_imp_subst_eq (Lambda.church_closed 0)]
  | cons b l ih =>
      cases b
      · simp [binBody, binWord, Lambda.subst, ih,
          Lambda.IsClosed_imp_subst_eq dblTerm_closed]
      · simp [binBody, binWord, Lambda.subst, ih]

theorem binProg_reduces_word (l : List Bool) : Lambda.reduces (binProg l) (binWord l) := by
  have h1 : Lambda.reduces (Lambda.app (Lambda.lam (Lambda.lam (binBody l))) dblTerm)
      (Lambda.lam (Lambda.subst dblTerm 1 (binBody l))) := by
    have := @Lambda.beta_reduces (Lambda.lam (binBody l)) dblTerm
    simpa only [Lambda.subst, Lambda.lift_closed dblTerm_closed] using this
  have h2 := @Lambda.beta_reduces (Lambda.subst dblTerm 1 (binBody l)) dblOneTerm
  rw [subst_binBody] at h2
  exact Lambda.reduces_trans (Lambda.reduces_app_left h1) h2

theorem binWord_reduces (l : List Bool) :
    Lambda.reduces (binWord l) (Lambda.church (binVal l)) := by
  induction l with
  | nil => exact Lambda.reduces.refl _
  | cons b l ih =>
      cases b
      · have := realizes_dblTerm.2 (binVal l)
        exact Lambda.reduces_trans (Lambda.reduces_app_right ih) (by simpa [binVal] using this)
      · have := realizes_dblOneTerm.2 (binVal l)
        exact Lambda.reduces_trans (Lambda.reduces_app_right ih) (by simpa [binVal] using this)

theorem binProg_isProgramFor (l : List Bool) : IsProgramFor (binProg l) (binVal l) :=
  ⟨binProg_closed l, Lambda.reduces_trans (binProg_reduces_word l) (binWord_reduces l)⟩

theorem size_binBody_le (l : List Bool) : size (binBody l) ≤ 3 + 3 * l.length := by
  induction l with
  | nil => simp [binBody, size_church]
  | cons b l ih => cases b <;> simp [binBody] <;> omega

theorem size_binProg_le (l : List Bool) : size (binProg l) ≤ 97 + 3 * l.length := by
  have := size_binBody_le l
  simp only [binProg, size_app, size_lam, size_dblTerm, size_dblOneTerm]
  omega

/-- Every number below `2^j` is the value of a bit list of length `j`. -/
theorem exists_binVal (j : ℕ) : ∀ n < 2 ^ j, ∃ l : List Bool, l.length = j ∧ binVal l = n := by
  induction j with
  | zero =>
      intro n hn
      exact ⟨[], rfl, by simp [binVal]; omega⟩
  | succ j ih =>
      intro n hn
      obtain ⟨l, hl, hv⟩ := ih (n / 2) (by rw [pow_succ] at hn; omega)
      refine ⟨decide (n % 2 = 1) :: l, by simp [hl], ?_⟩
      simp only [binVal, hv]
      by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-- **Every number below `2^j` has complexity at most `97 + 3 j`.** -/
theorem kolm_le_of_lt_two_pow_index (j : ℕ) : ∀ n < 2 ^ j, kolm n ≤ 97 + 3 * j := by
  intro n hn
  obtain ⟨l, hl, rfl⟩ := exists_binVal j n hn
  exact (kolm_le_of_isProgramFor (binProg_isProgramFor l)).trans (hl ▸ size_binProg_le l)

/-- **The index code rate `C = 3`:** every `i < N` has `kolm i ≤ 3 · log₂ N + 100`. -/
theorem kolm_le_three_log (N : ℕ) : ∀ i < N, kolm i ≤ 3 * Nat.log 2 N + 100 := by
  intro i hi
  have hN : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have := kolm_le_of_lt_two_pow_index (Nat.log 2 N + 1) i (hi.trans hN)
  omega

/-- **No index code rate below `1/2` per bit:** if `2p < q`, no additive constant `c` makes
`q · kolm i ≤ p · log₂ N + c` hold for all `i < N`. -/
theorem kolm_index_rate_lower (p q c : ℕ) (hpq : 2 * p < q) :
    ¬ ∀ N i, i < N → q * kolm i ≤ p * Nat.log 2 N + c := by
  intro h
  obtain ⟨s, hs, hk⟩ := exists_le_four_pow_kolm_gt (c + 1)
  have hlog : Nat.log 2 (4 ^ (c + 1) + 1) < 2 * (c + 1) + 1 := by
    apply Nat.log_lt_of_lt_pow (by positivity)
    have e : (2 : ℕ) ^ (2 * (c + 1) + 1) = 2 * 4 ^ (c + 1) := by
      rw [pow_succ, pow_mul]
      norm_num
      ring
    have : 1 ≤ 4 ^ (c + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have h1 := h (4 ^ (c + 1) + 1) s (by omega)
  have h2 : p * Nat.log 2 (4 ^ (c + 1) + 1) ≤ p * (2 * (c + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : q * (c + 2) ≤ q * kolm s := Nat.mul_le_mul_left _ (by omega)
  have h4 : (2 * p + 1) * (c + 2) ≤ q * (c + 2) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

end Lambda
