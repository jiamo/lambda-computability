# M7-HALTING-SIGMA1-COMPLETE

**Status:** DONE_STRONG

Module `Start/HaltingComplete.lean`, imported by `Start.lean`.  It upgrades the undecidability
results of `Start/NormalizationUndecidable.lean` to a placement in the arithmetical hierarchy,
using mathlib's `REPred` (`Mathlib/Computability/RE.lean`) and the many-one reducibility
`≤₀` of `Mathlib/Computability/Reduce.lean`.

## Theorems

* `Lambda.rePred_of_valid_test` — a reusable criterion: a predicate of the form "the code is a
  valid term and some primitive recursive test succeeds at some stage" is `REPred`.
* `Lambda.rePred_codeHasNormalForm : REPred CodeHasNormalForm` and
  `Lambda.rePred_codeConverges : REPred CodeConverges` — the halting set of the lambda calculus
  (in both the "has a normal form" and the "leftmost reduction converges" formulations) is
  recursively enumerable.
* `Lambda.rePred_le_codeHasNormalForm` and `Lambda.rePred_le_codeConverges` — **every** r.e.
  predicate many-one reduces to it.  The reduction is built from the domain of a partial
  recursive function (`Lambda.exists_partrec_dom_eq`), which is represented by a lambda term
  (`Lambda.exists_reduction_term`), and the reduction map `Lambda.reduceCode` is primitive
  recursive.
* `Lambda.codeHasNormalForm_sigma1_complete` and `Lambda.codeConverges_sigma1_complete` — the
  conjunction of the two previous items: the lambda halting set is **Σ₁-complete**.
* `Lambda.not_rePred_not_codeHasNormalForm` and `Lambda.not_rePred_not_codeConverges` — by
  Post's theorem (`ComputablePred.computable_iff_re_compl_re'`) the complement is **not** r.e.,
  so halting is r.e. but not co-r.e.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` on the main theorems reports only
`propext, Classical.choice, Quot.sound`.
