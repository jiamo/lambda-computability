# M7-KOLM-HALTING-BRIDGE

**Status:** DONE_STRONG

Module `Start/KolmogorovHalting.lean` (imported by `Start.lean`).

Two uncomputability results had been proved independently — undecidability of
normalization (`Lambda.not_computablePred_codeHasNormalForm`, a reduction from the halting
problem) and uncomputability of `K` (`Lambda.not_computable_kolm`, Berry's paradox through
the second recursion theorem). This module connects them.

* `Lambda.computable_kolm_of_decidable_halting :
  ComputablePred CodeHasNormalForm → Computable Lambda.kolm` — **a halting oracle computes
  `K`**. With a halting decider the leftmost run of `Start/LeftmostRun.lean` becomes a total
  computable test `Lambda.progTest` ("is the code `c` a closed program for `s`?"), and only
  finitely many codes need inspecting, because `Lambda.encBound` bounds the code of a term
  of size `≤ n` and `church s` is always a program for `s` of size `3s + 3`. So `K s` is the
  minimum of a computable function over a computably bounded range (`Lambda.minProg`,
  `Lambda.kolm_eq_minProg`).
* `Lambda.not_computablePred_codeHasNormalForm_of_berry` — contraposing gives a *second*,
  completely different proof of the undecidability of normalization, from Berry's paradox
  alone.
* `Lambda.kolm_uncomputable_iff` — the resulting equivalence of the two negative
  statements.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
