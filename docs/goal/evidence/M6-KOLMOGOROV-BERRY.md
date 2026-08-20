# M6-KOLMOGOROV-BERRY

**Status:** DONE_STRONG

In `Start/Kolmogorov.lean`, plus one addition to `Start/SecondRecursion.lean`.

* `Lambda.exists_code_fixed_point_closed` (`Start/SecondRecursion.lean`) — the fixed point of
  Kleene's second recursion theorem can be taken **closed**, which is what is needed for it to be
  a program in the sense of `Lambda.IsProgramFor`.
* `Lambda.add_le_pair`, `Lambda.size_le_encode` — `size t ≤ 2 * encode t + 1`: the size accounting
  that replaces any computability statement about term size on codes.
* `Lambda.not_computablePred_kolm_le` — **the relation `kolm s ≤ n` is undecidable.**  Berry's
  paradox: if it were decidable, the search "least `s` with `kolm s > 2 * c + 1`" is partial
  recursive and total (by `Lambda.exists_incompressible`), so it has a closed lambda realizer `G`;
  the closed fixed point `X ↠ G ⌜X⌝` is then a program for a number whose complexity exceeds
  `2 * encode X + 1 ≥ size X`, contradiction.
* `Lambda.not_computable_kolm` — **`kolm` is not a computable function**, a corollary.

Note on the statement: for each *fixed* `n` the set `{s | kolm s ≤ n}` is finite, hence decidable,
so only the uniform two-argument relation can be (and is) undecidable.

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on
`Lambda.not_computablePred_kolm_le`, `Lambda.not_computable_kolm` and
`Lambda.exists_code_fixed_point_closed` reports only `propext, Classical.choice, Quot.sound`.
