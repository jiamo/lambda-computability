# M10-POST-THEOREM-TWO

**Status:** DONE_STRONG

Module `Start/PostTheoremTwo.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

Join the arithmetical hierarchy of `Start/ArithHierarchy.lean` with Shoenfield's limit lemma of
`Start/LimitLemma.lean` at level two: identify `Δ⁰₂` with the limit computable predicates, hence
with the predicates decidable from the halting oracle `∅'`.

## What is proved

* `Lambda.Arith.LimitComputablePred` — a predicate is limit computable when its characteristic
  function is the pointwise limit of a computable sequence of guesses.
* `Lambda.Arith.sigmaAt_two_of_limitComputablePred`,
  `Lambda.Arith.piAt_two_of_limitComputablePred`,
  `Lambda.Arith.deltaAt_two_of_limitComputablePred` — a limit is both a `Σ⁰₂` and a `Π⁰₂`
  statement: "some stage is followed only by `true` guesses", and "after every stage there is a
  `true` guess".
* The stagewise construction for the converse: `Lambda.Arith.allB`, `Lambda.Arith.leastB` (bounded
  conjunction and bounded least witness, with their characterizations), `Lambda.Arith.aliveUpTo`,
  `Lambda.Arith.bestWitness`, `Lambda.Arith.twoGuess`, and their computability
  (`Lambda.Arith.computable₂_twoGuess`).
* `Lambda.Arith.exists_stage_dead`, `Lambda.Arith.bestWitness_eventually`,
  `Lambda.Arith.bestWitness_large` — the convergence analysis: the side that has a true witness
  settles on its least one, while on the side that has none every candidate is eventually
  refuted, so the comparison of the two settles correctly.
* `Lambda.Arith.limitComputablePred_of_deltaAt_two` — hence every `Δ⁰₂` predicate is limit
  computable.
* `Lambda.Arith.deltaAt_two_iff_limitComputablePred` — **Post's theorem at level two**.
* `Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle` — combining with the limit lemma:
  `Δ⁰₂` is exactly the class of predicates decidable from `∅'`.

## Boundary

None.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
