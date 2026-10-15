# M19-TERM-COUNT-LOWER — exponential lower bounds for the raw size measure

**Status:** DONE_STRONG.

Module: `Start/KolmogorovCountLower.lean` (this library's own definitions and proofs; no `sorry`,
axioms `propext`, `Classical.choice`, `Quot.sound` only).

## Terms

* `Lambda.termCount` — the recursion `c 0 = 0`, `c (n+1) = 1 + c n + Σ_{a ≤ n} c a · c (n-a)`
  (one variable `var n`, abstractions of terms of size `n`, applications), computed by a table
  so that the kernel evaluates it; `Lambda.termCount_succ` is the recursion as a theorem.
* `Lambda.termCount_le_card : termCount n ≤ Nat.card {t // size t = n}` — an injection
  `Unit ⊕ S n ⊕ Σ a ≤ n, S a × S (n-a) → S (n+1)`.
* `Lambda.card_size_eq_pow_le : (#size = s)^j ≤ #(size ≤ (s+1) j + 1)` — the chain
  `a₁ (a₂ (… (aⱼ 0)…))` is injective (supermultiplicativity of the counts).
* `Lambda.termCount_hundred : 3^101 · 30 ≤ termCount 100` (kernel evaluation).
* **`Lambda.three_pow_le_card_size_le : 3334 ≤ m → 3^m ≤ Nat.card {t // size t ≤ m}`.**

With `Lambda.card_size_le` (`≤ 4^m`) the number of terms of size `≤ m` lies between `3^m` and
`4^m` for all `m ≥ 3334`.  (Numerically — not a proved statement — the exact growth rate of the
recursion is about `3.38`: the root of `(1-x)^3 = 4x^2` is `x ≈ 0.296`.  Taking larger `s` in
`card_size_eq_pow_le` raises the provable base towards it.)

## Numbers under `kolm`

* `Lambda.dblTerm = mkApp2 mult (mkConst 2) I` (size 36) realizes `n ↦ 2n`;
  `Lambda.dblOneTerm = mkApp1 succ dblTerm` (size 54) realizes `n ↦ 2n+1`.
* `Lambda.kolm_le_of_lt_two_pow : n < 2^j → kolm n ≤ 3 + 55 j` (binary expansion, through
  `Lambda.kolm_apply_le`).
* `Lambda.two_pow_le_card_kolm_le : 2^j ≤ Nat.card {s // kolm s ≤ 3 + 55 j}`.
* **`Lambda.two_pow_le_card_kolm_le_pow : 114 ≤ m → 2^m ≤ (Nat.card {s // kolm s ≤ m})^110`**,
  i.e. at least `c^m` numbers of complexity `≤ m` with the explicit base `c = 2^(1/110) > 1`.

## Quantitative target for M19-SYMMETRY-HARD-HALF

The counting side of the hard half ("`s` is determined by `y`, `m` and its index among at most
`N` candidates") is now pinned between bases: for terms, `3^m ≤ #(size ≤ m) ≤ 4^m`, so the
counting term `log N` in `kolm`-units is `log₄ N` up to a factor at most `log 4 / log 3 < 1.27`;
the base `4` of `card_size_le` cannot be replaced by anything below `3`.  What decides the
constant on the counting term in the final inequality is the *coding rate of indices*: writing an
index `i < N` as a closed term.  With the binary realizers above this costs `55 log₂ N + O(1)`
size, i.e. `110 log₄ N`, so an argument using them yields
`K(y) + K(s | y) ≤ K(s, y) + 110 · log₄(#candidates) + O(log)`-type bounds with a multiplicative
constant on the counting term, not the classical constant `1`.  The justified target for
`M19-SYMMETRY-HARD-HALF` is therefore the logarithmic-error form with an explicit constant
determined by the index code, and the constant `1` additionally requires an index code whose
size is `log₄ N + o(log N)` — which this module does not provide and which is not claimed.
