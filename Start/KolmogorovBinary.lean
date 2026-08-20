/-
Compact (binary) numerals, and the logarithmic form of the invariance theorem.

`Start/Kolmogorov.lean` bounds the complexity of a description `p` by `3 * p + c`, because the
obvious way to feed `p` to a lambda term is the *unary* Church numeral `church p`, whose size is
`3 * p + 3`.  Here we build a compact numeral: a closed term `binNum p` of size `O(log p)` that
still reduces to `church p`, obtained by reading the binary expansion of `p` with the doubling
term `mult (church 2)` and `succ`.

Consequences:

* `Lambda.exists_const_kolm_le_size` — every number `n` has a lambda program of size
  `O(bit length of n)`, so `kolm n = O(log n)`;
* `Lambda.exists_const_kolm_le_size_of_partrec` and `Lambda.exists_const_kolm_le_size_of_tm2` —
  the invariance theorem in logarithmic form: for any partial recursive (equivalently, Turing
  machine computable) description system `V`, complexity is bounded by a constant multiple of the
  *bit length* of the description.

The measure here counts syntax nodes, and each bit of a compact numeral costs a constant number
of them, so on bit lengths the bounds are up to a multiplicative constant.  An additive statement
about bit lengths would need a program measure counted in bits; a prefix-free such measure is what
Chaitin's `Ω` additionally requires, and neither is built here.  (Additivity *in the node measure*
does hold: see `Lambda.kolm_le_kolmWith`.)
-/

import Start.Kolmogorov

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- The doubling term: `mult (church 2)`. -/
def dbl : Lambda := Lambda.app Lambda.mult (Lambda.church 2)

theorem dbl_closed : Lambda.IsClosed dbl :=
  Lambda.IsClosed_app Lambda.mult_closed (Lambda.church_closed 2)

theorem dbl_reduces (n : ℕ) : Lambda.reduces (Lambda.app dbl (Lambda.church n))
    (Lambda.church (2 * n)) := Lambda.mult_works 2 n

/-- A compact numeral: a closed term of size logarithmic in `n` reducing to `church n`. -/
def binNum : ℕ → Lambda
  | 0 => Lambda.church 0
  | (n + 1) =>
      if (n + 1) % 2 = 0 then Lambda.app dbl (binNum ((n + 1) / 2))
      else Lambda.app Lambda.succ (Lambda.app dbl (binNum ((n + 1) / 2)))
  decreasing_by all_goals omega

theorem binNum_closed (n : ℕ) : Lambda.IsClosed (binNum n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => rw [binNum]; exact Lambda.church_closed 0
      | (m + 1) =>
          rw [binNum]
          have ihm : Lambda.IsClosed (binNum ((m + 1) / 2)) := ih ((m + 1) / 2) (by omega)
          split
          · exact Lambda.IsClosed_app dbl_closed ihm
          · exact Lambda.IsClosed_app Lambda.succ_closed (Lambda.IsClosed_app dbl_closed ihm)

theorem binNum_reduces (n : ℕ) : Lambda.reduces (binNum n) (Lambda.church n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => rw [binNum]; exact Lambda.reduces.refl _
      | (m + 1) =>
          rw [binNum]
          have ihm : Lambda.reduces (binNum ((m + 1) / 2)) (Lambda.church ((m + 1) / 2)) :=
            ih ((m + 1) / 2) (by omega)
          have hdbl : Lambda.reduces (Lambda.app dbl (binNum ((m + 1) / 2)))
              (Lambda.church (2 * ((m + 1) / 2))) :=
            Lambda.reduces_trans (Lambda.reduces_app_right ihm) (dbl_reduces _)
          split
          · next heven =>
              have h2 : 2 * ((m + 1) / 2) = m + 1 := by omega
              rwa [h2] at hdbl
          · next hodd =>
              have h2 : 2 * ((m + 1) / 2) + 1 = m + 1 := by omega
              have hsucc : Lambda.reduces
                  (Lambda.app Lambda.succ (Lambda.church (2 * ((m + 1) / 2))))
                  (Lambda.church (2 * ((m + 1) / 2) + 1)) := Lambda.succ_works _
              rw [h2] at hsucc
              exact Lambda.reduces_trans (Lambda.reduces_app_right hdbl) hsucc

/-- The per-bit cost of the compact numeral. -/
def binCost : ℕ := size dbl + size Lambda.succ + 2

theorem size_binNum_step (n : ℕ) :
    size (binNum (n + 1)) ≤ size (binNum ((n + 1) / 2)) + binCost := by
  rw [binNum, binCost]
  split <;> simp only [size_app] <;> omega

/-- The compact numeral for `n` has size at most `binCost * k + 3` whenever `n < 2 ^ k`. -/
theorem size_binNum_le (k : ℕ) : ∀ n : ℕ, n < 2 ^ k → size (binNum n) ≤ binCost * k + 3 := by
  induction k with
  | zero =>
      intro n hn
      have : n = 0 := by simpa using hn
      subst this
      simp [binNum, size_church]
  | succ k ih =>
      intro n hn
      match n with
      | 0 => simp [binNum, size_church]
      | (m + 1) =>
          have hhalf : (m + 1) / 2 < 2 ^ k := by
            have : (m + 1) < 2 ^ k * 2 := by
              simpa [pow_succ] using hn
            omega
          have h1 := size_binNum_step m
          have h2 := ih ((m + 1) / 2) hhalf
          have : binCost * k + binCost = binCost * (k + 1) := by ring
          omega

/-- **Every number has a program of logarithmic size.** -/
theorem exists_const_kolm_le_size : ∃ c : ℕ, ∀ n : ℕ, kolm n ≤ c * (Nat.size n + 1) := by
  refine ⟨binCost + 3, fun n => ?_⟩
  have hprog : IsProgramFor (binNum n) n := ⟨binNum_closed n, binNum_reduces n⟩
  have hle := kolm_le_of_isProgramFor hprog
  have hsize := size_binNum_le (Nat.size n) n (Nat.lt_size_self n)
  have hbound : binCost * Nat.size n + 3 ≤ (binCost + 3) * (Nat.size n + 1) := by nlinarith
  omega

/-- **Invariance theorem, logarithmic form.**  For any partial recursive description system `V`,
the complexity of a described number is bounded by a constant multiple of the *bit length* of the
description. -/
theorem exists_const_kolm_le_size_of_partrec {V : ℕ →. ℕ} (hV : Partrec V) :
    ∃ c : ℕ, ∀ p s : ℕ, V p = Part.some s → kolm s ≤ c * (Nat.size p + 1) := by
  obtain ⟨F, hFc, hF⟩ := lambdaComputable_of_partrec_closed hV
  refine ⟨size F + binCost + 4, fun p s hps => ?_⟩
  have hred : Lambda.reduces (Lambda.app F (binNum p)) (Lambda.church s) :=
    Lambda.reduces_trans (Lambda.reduces_app_right (binNum_reduces p)) ((hF p s).1 hps)
  have hprog : IsProgramFor (Lambda.app F (binNum p)) s :=
    ⟨Lambda.IsClosed_app hFc (binNum_closed p), hred⟩
  have hle := kolm_le_of_isProgramFor hprog
  have hsize := size_binNum_le (Nat.size p) p (Nat.lt_size_self p)
  simp only [size_app] at hle
  have hbound : size F + (binCost * Nat.size p + 3) + 1 ≤
      (size F + binCost + 4) * (Nat.size p + 1) := by nlinarith
  omega

/-- The same statement for Turing machines, through the model equivalence. -/
theorem exists_const_kolm_le_size_of_tm2 {V : ℕ →. ℕ} (hV : TM2Partrec.TM2ComputableNat V) :
    ∃ c : ℕ, ∀ p s : ℕ, V p = Part.some s → kolm s ≤ c * (Nat.size p + 1) :=
  exists_const_kolm_le_size_of_partrec (TM2Partrec.tm2Computable_iff_partrec.mp hV)

end Lambda
