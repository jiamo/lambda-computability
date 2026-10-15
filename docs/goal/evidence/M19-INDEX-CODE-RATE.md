# M19-INDEX-CODE-RATE — a short index code

**Status:** DONE_STRONG.

Module: `Start/KolmogorovIndexCode.lean` (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound` only, see `docs/goal/evidence/M29-PART1-axioms.txt`).

## The code

`Start/KolmogorovCountLower.lean` wrote a number below `2^j` as the nest
`D_{b₁} (D_{b₂} (… (D_{bⱼ} ⌜0⌝)…))` of the digit realizers `dblTerm` (`n ↦ 2n`, size 36) and
`dblOneTerm` (`n ↦ 2n+1`, size 54): `55` size units per bit.  Most of that is the realizers being
written out again for every bit.  The new code binds them once:

```
binProg l = (λ λ. d_{b₁} (d_{b₂} (… (d_{bⱼ} ⌜0⌝)…))) dblTerm dblOneTerm
d_false = var 1   (size 2, bound to dblTerm)
d_true  = var 0   (size 1, bound to dblOneTerm)
```

Each bit is one application node plus one de Bruijn index, so it costs `2` or `3`.

* `Lambda.binProg_isProgramFor : IsProgramFor (binProg l) (binVal l)` — two β-steps substitute
  the realizers (`binProg_reduces_word`), then the realizers compute the binary value
  (`binWord_reduces`).
* `Lambda.size_binProg_le : size (binProg l) ≤ 97 + 3 · |l|`.
* `Lambda.kolm_le_of_lt_two_pow_index : n < 2^j → kolm n ≤ 97 + 3 j`.
* **`Lambda.kolm_le_three_log : i < N → kolm i ≤ 3 · Nat.log 2 N + 100`.**  So `C = 3`, against
  `55` for the nested realizers (and against the `27.5` named in the row).

## The other side

* **`Lambda.kolm_index_rate_lower (p q c) (hpq : 2 p < q) : ¬ ∀ N i, i < N → q · kolm i ≤
  p · Nat.log 2 N + c`.**  No index code beats `1/2` per bit: by `Lambda.card_kolm_le` (at most
  `4^m` numbers of complexity `≤ m`, through `Lambda.exists_le_four_pow_kolm_gt`), some `s ≤ 4^m`
  has `kolm s > m = (1/2) log₂ 4^m`.

So the best constant `C*` with `kolm i ≤ C* log₂ N + O(1)` for all `i < N` satisfies
`1/2 ≤ C* ≤ 3`.  (A base-4 version of the same code, with four bound realizers and digits costing
`2..5` per two bits, would give `2.5`; it is not formalized.)

## The constant on the counting term of M19-SYMMETRY-HARD-HALF

Stated against `Lambda.card_kolm_le` (base `4`, i.e. `log₄` in `kolm` units, `= (1/2) log₂`):
writing the index of `s` among at most `N` candidates costs at most `3 log₂ N + 100 =
6 log₄ N + 100` size units with this code, against the information-theoretic `log₄ N` that
`card_kolm_le` charges.  The counting term of the hard half therefore carries the factor `6`
(relative to `log₄ N`; `3` relative to `log₂ N`) with this code, down from `110` (resp. `55`) with
the nested realizers.  The classical constant `1` would need an index code of size
`log₄ N + o(log N)`; the lower bound above shows only that nothing below `log₄ N` is possible,
and neither the constant `1` nor any constant below `6` is claimed.
