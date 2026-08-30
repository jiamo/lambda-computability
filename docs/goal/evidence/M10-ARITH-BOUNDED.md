# M10-ARITH-BOUNDED

**Status:** DONE_STRONG

Module `Start/ArithBounded.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

Unbounded quantifiers raise the level of a predicate in the hierarchy of
`Start/ArithHierarchy.lean`.  Show that *bounded* ones do not: every level `Σ⁰ₙ` and `Π⁰ₙ` is
closed under `∀ y < b x` and `∃ y < b x` for a computable bound `b`.

## What is proved

* `Lambda.Arith.allLt`, `Lambda.Arith.exLt` — the bounded conjunction and disjunction of a `Bool`
  test, defined by recursion on the bound, with `Lambda.Arith.allLt_eq_true_iff`,
  `Lambda.Arith.exLt_eq_true_iff` characterizing them and `Lambda.Arith.computable_allLt`,
  `Lambda.Arith.computable_exLt` making them computable uniformly in the test (via
  `Computable.nat_rec`).
* `Lambda.Arith.computablePred_ball_lt`, `Lambda.Arith.computablePred_bex_lt` — the level-zero
  case: the computable predicates are closed under both bounded quantifiers.
* `Lambda.Arith.sigmaAt_of_computablePred`, `Lambda.Arith.piAt_of_computablePred` — a computable
  predicate sits at every level, on both sides.
* `Lambda.Arith.exists_code_of_ball_exists` — **collection**: if every argument below a bound has
  a witness, then a single number codes a list of witnesses for all of them at once
  (`w ↦ List.getD (ofNat (List ℕ) w) y 0`).
* `Lambda.Arith.sigmaAt_bounded_closure` — the main induction on the level, proving both bounded
  quantifier cases for `Σ⁰ₙ` simultaneously.  For the bounded universal quantifier, collection
  replaces the family of witnesses required by the inner existential quantifier with one coded
  list, so the existential quantifier can be pulled out in front of the bounded universal one;
  for the bounded existential quantifier, the bound is folded into the outermost existential
  quantifier as a conjunct with a computable predicate.  The `Π` halves follow by de Morgan
  through `Lambda.Arith.piAt_iff_sigmaAt_not`.
* `Lambda.Arith.SigmaAt.ball_lt`, `Lambda.Arith.SigmaAt.bex_lt`, `Lambda.Arith.PiAt.ball_lt`,
  `Lambda.Arith.PiAt.bex_lt` — the four closure theorems in usable form.

## Boundary

None.

## Gates

* `lake build Start.ArithBounded` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
