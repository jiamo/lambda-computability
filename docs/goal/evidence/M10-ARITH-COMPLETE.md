# M10-ARITH-COMPLETE

**Status:** DONE_STRONG

Module `Start/ArithComplete.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/ArithHierarchyProper.lean` produces, for every level `n + 1`, a *universal* predicate and
diagonalises against it.  Upgrade "universal" to "complete": show that every level is closed
downwards under many-one reducibility, that the universal predicates are hard for their level,
and read off the standard consequences — including that the halting problem is the level-one
example.

## What is proved

* `Lambda.Arith.SigmaAt.of_manyOne`, `Lambda.Arith.PiAt.of_manyOne`,
  `Lambda.Arith.DeltaAt.of_manyOne` — every level is closed downwards under `≤₀`.  This is what
  makes completeness a meaningful notion.
* `Lambda.Arith.SigmaComplete`, `Lambda.Arith.PiComplete` — membership in the level together with
  hardness for it.
* `Lambda.Arith.computable_injective_pairLeft` — the section `x ↦ ⟨e, x⟩` of the pairing is
  computable and injective, so it is a one-one reduction.
* `Lambda.Arith.UnivSigma.oneOne_hard`, `Lambda.Arith.UnivSigma.sigmaComplete`,
  `Lambda.Arith.UnivPi.oneOne_hard`, `Lambda.Arith.UnivPi.piComplete` — a universal predicate for
  a level is hard for it already for one-one reducibility, hence complete.
* `Lambda.Arith.exists_sigmaComplete`, `Lambda.Arith.exists_piComplete`,
  `Lambda.Arith.exists_sigmaOneOneComplete`, `Lambda.Arith.exists_piOneOneComplete` — every level
  `n + 1` carries complete, indeed one-one complete, predicates on both sides.
* `Lambda.Arith.SigmaComplete.compl`, `Lambda.Arith.PiComplete.compl` — complementation exchanges
  the two notions of completeness.
* `Lambda.Arith.SigmaComplete.of_manyOne`, `Lambda.Arith.PiComplete.of_manyOne` — completeness
  travels upwards along a reduction into a predicate of the level.
* `Lambda.Arith.SigmaComplete.manyOneEquiv` — any two `Σ⁰ₙ`-complete predicates are many-one
  equivalent.
* The negative half at level `n + 1`: `Lambda.Arith.SigmaComplete.not_piAt`,
  `Lambda.Arith.PiComplete.not_sigmaAt`, `Lambda.Arith.SigmaComplete.not_deltaAt`,
  `Lambda.Arith.PiComplete.not_deltaAt`, `Lambda.Arith.SigmaComplete.not_sigmaAt_lower`,
  `Lambda.Arith.SigmaComplete.not_piAt_lower`, `Lambda.Arith.PiComplete.not_piAt_lower`, and
  `Lambda.Arith.SigmaComplete.not_computablePred`,
  `Lambda.Arith.PiComplete.not_computablePred`.
* `Lambda.Arith.sigmaComplete_one_codeHasNormalForm`,
  `Lambda.Arith.sigmaComplete_one_codeConverges`,
  `Lambda.Arith.piComplete_one_not_codeHasNormalForm`,
  `Lambda.Arith.not_computablePred_codeHasNormalForm'` — level one is the halting problem of the
  lambda calculus, which places the `Σ₁`-completeness theorem of `Start/HaltingComplete.lean`
  inside the hierarchy.
* `Lambda.Arith.not_exists_arithmetical_complete` — the union of the levels has no complete
  predicate, matching the absence of a universal one.

## Boundary

None.

## Gates

* `lake build Start.ArithComplete` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
