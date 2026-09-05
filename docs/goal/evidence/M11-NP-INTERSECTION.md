# M11-NP-INTERSECTION

**Status:** DONE_STRONG

`Start/ComplexityClasses.lean` closed `NP` under union — the witness carries a tag bit saying
which verifier to run — and `Start/ThreeSat.lean` closed it under intersection with `P`.  The
missing closure property, intersection of two `NP` languages, needs a witness carrying *two*
witnesses, hence a pairing of words that a Cobham term can undo.  That is what
`Start/NPInter.lean` supplies.  The module is imported by `Start.lean`, registered in
`Start/Capstones.lean`, builds without `sorry` or linter warning, and `Complexity.InNP.inter`
depends only on `propext`, `Classical.choice`, `Quot.sound`.

## The pairing and its projections (first exit criterion)

* `Complexity.pairW u v` — `u` with every bit doubled, the marker `10`, then `v` verbatim;
* `Complexity.pairDelta` — the four-state automaton reading such a word: state `0` expects the
  first bit of a doubled pair, states `1` and `2` remember it, and state `3`, entered at the first
  mismatched pair, is the tail;
* `Complexity.fstOf`, `Complexity.sndOf` — the transductions of that automaton emitting,
  respectively, one bit per completed pair and every bit after the marker;
* `Complexity.fstOf_pairW`, `Complexity.sndOf_pairW` — **the projections undo the pairing**.

## The projections are Cobham terms (second exit criterion)

`Complexity.eval_lrunTerm` of `Start/CobhamTransducer.lean` turns a left-to-right finite-state
transduction into a Cobham term; the local lemmas `Complexity.lst_append` and
`Complexity.lrun_append` are what the computations above need.

* `Complexity.fstTerm`, `Complexity.sndTerm`, with `Complexity.eval_fstTerm` and
  `Complexity.eval_sndTerm`.

## The length bound (third exit criterion)

A verifier is total, so it must accept or reject *arbitrary* witnesses, and the witness bound of
the definition of `NP` has to hold for them.  Reading an arbitrary word, the automaton sees
matched pairs, then at most one mismatched pair, then the tail:

* `Complexity.pairSlack`, `Complexity.length_le_of_proj_aux` — the bound with the slack of the
  current state, by induction on the word;
* `Complexity.length_le_of_proj` — `|x| ≤ 2 * |fstOf x| + 3 + |sndOf x|`.

## `NP` is closed under intersection (fourth exit criterion)

* `Complexity.InNP.inter` — the verifier runs each of the two verifiers on the corresponding
  projection of the witness and takes the conjunction; the witness bound is
  `2 * p₁ n + 3 + p₂ n`, polynomial and monotone, and completeness uses `pairW` of the two
  witnesses.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.NPInter`
