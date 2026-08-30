# M10-KOLM-UPPER-SEMICOMPUTABLE

**Status:** DONE_STRONG

Module `Start/KolmogorovApprox.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings, and
`#print axioms` on `Lambda.rePred_kolm_le`, `Lambda.not_rePred_lt_kolm`,
`Lambda.kolm_eq_iInf_kolmAt` and `Lambda.primrec_kolmAt` reports only `propext`,
`Classical.choice` and `Quot.sound`.

## The question

`Start/Kolmogorov.lean` proves that `Lambda.kolm` is not computable, and
`Start/KolmogorovHalting.lean` computes it from a halting oracle.  What survives without the
oracle is the classical *one-sided* effectivity: a shortest program can be found by running all
candidates in parallel, but one never learns that the search is finished.  Formally, `K` is upper
semicomputable — its lower graph is r.e., and it is the limit of a computable non-increasing
approximation — and neither half can be improved: the upper graph is not even r.e.

## The argument

* `Lambda.progBy s k c` — the **time-bounded program test**: `c` codes a closed term whose
  leftmost-outermost run reaches `church s` within `k` steps.  It is primitive recursive
  (`Lambda.progBy_primrec`, from `Lambda.is_valid_code_primrec`, `Lambda.isClosed_code_primrec`,
  `Lambda.nstep_code_iterate_primrec` and `Lambda.church_code_primrec`), correct
  (`Lambda.progBy_encode_iff`, `Lambda.exists_isProgramFor_of_progBy`,
  `Lambda.exists_progBy_of_isProgramFor`), and stable in the number of steps
  (`Lambda.progBy_mono`, by `Lambda.nstep_iterate_stable`: a normal form is a fixed point).
* `Lambda.rePred_kolm_le` — `K s ≤ n` is r.e.: it holds iff some pair (code, stage) passes the
  test with the code's size at most `n`, which is the sufficient condition
  `Lambda.Post.rePred_of_exists_test` (generalized in `Start/PostSimple.lean` from `ℕ` to an
  arbitrary `Primcodable` domain, so that it applies to the pair `(s, n)`).
* `Lambda.not_rePred_lt_kolm` — the complementary relation `n < K s` is **not** r.e.: an
  enumeration of it would be a sound r.e. system of complexity lower bounds proving all true
  ones, contradicting `Lambda.chaitin_incompleteness` together with
  `Lambda.exists_incompressible`.
* `Lambda.minAt s k b` — the least size of a program for `s` found within `k` steps among the
  codes below `b`, defined by recursion on `b` with default `3 * s + 3` (the size of the Church
  numeral), and `Lambda.kolmAt s k = minAt s k (encBound (3 * s + 3) + 1)`, the bound of
  `Start/CodeArith.lean` restricting the search to the codes that can possibly be shorter.
* `Lambda.kolm_le_kolmAt`, `Lambda.kolmAt_antitone`, `Lambda.exists_kolmAt_eq_kolm` — every value
  found is the size of a genuine program, so the approximation is above `K`; by
  `Lambda.progBy_mono` it is non-increasing in the stage; and a shortest program is found at the
  stage at which it halts, so the approximation reaches `K`.
* `Lambda.primrec_minAt` and `Lambda.primrec_kolmAt` — the bounded minimisation is a primitive
  recursion on the bound (`Primrec.nat_rec`) with a primitive recursive step, composed with the
  primitive recursive bound `Lambda.encBound_primrec`.

## Results

* **`Lambda.rePred_kolm_le`** — `REPred fun q : ℕ × ℕ => kolm q.1 ≤ q.2`.
* **`Lambda.not_rePred_lt_kolm`** — `¬ REPred fun q : ℕ × ℕ => q.2 < kolm q.1`.
* **`Lambda.primrec_kolmAt`** — the stagewise approximation is primitive recursive.
* **`Lambda.kolm_eq_iInf_kolmAt`** — `kolm s = ⨅ k, kolmAt s k`, and
  **`Lambda.kolmAt_eventually_eq_kolm`** — the approximation is exact from some stage on, so `K`
  is limit computable.

Together with `Lambda.not_computablePred_kolm_le` (`Start/Kolmogorov.lean`) this is the exact
effective content of `K`: recursively enumerable from above, not decidable, not r.e. from below.

## Boundary

The complexity measure is the project's `Lambda.kolm`, the least *size* of a closed lambda term
whose leftmost-outermost reduction reaches the Church numeral; "computable" is Mathlib's
`Primrec`/`REPred` on `ℕ`.  The approximation `kolmAt` searches the code range supplied by
`Lambda.encBound`, which is sufficient because a program shorter than the Church numeral has a
code below that bound; no attempt is made to make the search efficient.

## Gates

```bash
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.KolmogorovApprox
```
