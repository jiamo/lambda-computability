# M7-OMEGA-UNCOMPUTABLE

**Status:** DONE_STRONG

Module `Start/OmegaUncomputable.lean` (imported by `Start.lean`).

`Start/ChaitinOmega.lean` stops at the convergence of `Ω` (`0 < Ω < 1`). This module proves
Chaitin's theorem.

* `Lambda.RealComputable x` — the standard notion: a computable `f` with
  `|x - f n / 2 ^ n| ≤ 2 ^ (-n)`.
* The halting set is c.e., so `Ω` is a computable *supremum*: `Lambda.omegaNum k` /
  `Lambda.omegaApprox k` is a primitive recursive dyadic rational
  (`Lambda.omegaNum_primrec`, `Lambda.omegaApprox_eq_div`, `Lambda.sum_stageTerms`) with
  `Lambda.omegaApprox_le : Ω_k ≤ Ω` and `Lambda.exists_omegaApprox_gt` (the approximations
  increase to `Ω`). Auxiliary arithmetizations: `Lambda.is_valid_code`,
  `Lambda.bitsLen_code`, `Lambda.closure_code`, `Lambda.stageHalt`.
* `Lambda.not_realComputable_chaitinOmega : ¬ RealComputable chaitinOmega`. A computable
  upper estimate would decide halting: to test a closed `u` with `L = |bits u|`, approximate
  `Ω` within `2 ^ (-L-2)` and enumerate stages until `Ω_k > Ω - 2 ^ (-L)`; at that stage
  every halting program of length `L` has been found, since otherwise its weight `2 ^ (-L)`
  would still be missing (`Lambda.omegaApprox_add_le`). That contradicts
  `Lambda.not_computablePred_codeHasNormalForm`.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
