# M10-CREATIVE-CODESETS

**Status:** DONE_STRONG

Module `Start/CreativeCodeSets.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/RiceCreative.lean` proves that a convertibility-invariant class of lambda terms which is
inhabited and contains no unsolvable term has a code set many-one above the diagonal halting set,
and that such a code set is *creative* as soon as it is recursively enumerable.  It leaves the
enumerability hypothesis unverified for any concrete class.  This task supplies it and reads off
the resulting classification.

## What is proved

* `Lambda.reduces_of_conv_normal` — a term convertible with a normal term already reduces to it
  (the common reduct of the convertibility can only be the normal term itself).
* `Lambda.conv_church_iff_exists_nstep` — hence `Conv t (church m)` holds exactly when some stage
  of the leftmost run of `t` equals `church m`; this is the semi-decision procedure.
* `Lambda.convChurchTest`, `Lambda.convChurchTest_primrec`,
  `Lambda.codeSet_conv_church_iff_valid_and_test` — the stage test on codes and its primitive
  recursiveness, and the resulting characterisation "valid code and some stage succeeds".
* `Lambda.rePred_codeSet_conv_church` — the codes of the terms convertible with `church m` form a
  recursively enumerable set.
* `Lambda.creative_codeSet_conv_church` — with `Lambda.creative_codeSet` this set is **creative**;
  `Lambda.manyOneEquiv_codeSet_conv_church_haltK` and `Lambda.not_simple_codeSet_conv_church` are
  the standard consequences.
* `Lambda.creative_codeHasNormalForm`, `Lambda.creative_codeConverges` — the lambda-calculus
  halting set and the set of codes converging to a Church numeral are creative, from their
  enumerability (`Start/HaltingComplete.lean`) and their many-one completeness.
* `Lambda.manyOneEquiv_codeHasNormalForm_haltK`, `Lambda.manyOneEquiv_codeConverges_haltK`,
  `Lambda.manyOneEquiv_codeHasNormalForm_codeConverges` — all of these problems sit at the same
  many-one degree as Kleene's `K`.

## Boundary

Creativity is stated in the sense of `Start/PostCreative.lean` (r.e. with a productive
complement); the many-one equivalences are many-one, not recursive isomorphism — Myhill's
isomorphism theorem is not claimed.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
