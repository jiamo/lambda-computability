# M10-LIMIT-LEMMA

**Status:** DONE_STRONG

Modules `Start/JumpApprox.lean` and `Start/LimitLemma.lean`, imported by `Start.lean` and
registered in `Start/Capstones.lean`.  Both build without `sorry` and without linter warnings.

## What the task asked

Identify the sets computable from the halting oracle `∅'` with the sets that are pointwise limits
of computable sequences of guesses — Shoenfield's limit lemma.

## What is proved

`Start/JumpApprox.lean`:

* `Lambda.Oracle.jumpApprox` — the stage-`s` approximation of `∅'`: accept an index when the
  machine it names halts on itself within `s` steps against the empty oracle, with
  `Lambda.Oracle.primrec₂_jumpApprox` (it is primitive recursive), monotonicity in the stage, and
  `Lambda.Oracle.exists_jumpApprox_agree` — on any finite initial segment the approximation is
  eventually correct.
* `Lambda.Oracle.scanOf` — the first value produced by a stagewise run, with its characterization.

`Start/LimitLemma.lean`:

* `Lambda.Oracle.LimitComputable` — the definition;
* `Lambda.Oracle.limitGuess`, `Lambda.Oracle.limitGuess_eventually` — running a reduction against
  the approximated oracle gives guesses that settle on the true value;
* `Lambda.Oracle.limitComputable_of_turingReducible`,
  `Lambda.Oracle.turingReducible_of_limitComputable` — the two directions;
* `Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle` — **Shoenfield's limit
  lemma**;
* `Lambda.Oracle.limitComputable_of_repred` — every r.e. set is limit computable, and
  `Lambda.Oracle.not_limitComputable_jumpChar_haltingOracle` — `∅''` is not.

## Boundary

None.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
