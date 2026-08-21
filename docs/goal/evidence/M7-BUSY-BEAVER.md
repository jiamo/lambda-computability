# M7-BUSY-BEAVER

**Status:** DONE_STRONG

Module `Start/BusyBeaver.lean` (imported by `Start.lean`).

* `Lambda.bbTime n` — the maximum of `Lambda.haltTime t` over the normalizing terms with
  `encode t ≤ n`; `Lambda.bbSize n` — the same over terms of syntactic size `≤ n`. Both are
  well defined because `Lambda.finite_setOf_encode_le` and
  `Lambda.finite_setOf_size_le` bound the search; `Lambda.haltTime_le_bbTime`,
  `Lambda.haltTime_le_bbSize`, `Lambda.bbTime_mono`.
* `Lambda.hasNormalForm_iff_haltsBy_code` — a bound on the halting time turns normalization
  into a bounded computation, so `Lambda.not_computable_of_halting_bound`: no computable
  function bounds halting times (else normalization would be decidable, contradicting
  `Lambda.not_computablePred_codeHasNormalForm`).
* Consequently `Lambda.not_computable_bbTime`, `Lambda.not_computable_bbSize`,
  `Lambda.no_computable_bound_bbTime`, and
  `Lambda.bbTime_exceeds_computable` — every computable `f` is exceeded by `bbTime` at
  arbitrarily large arguments.
* Certificates: `Lambda.HaltCert t k` (a checkable witness that `t` halts in exactly `k`
  leftmost steps) with `Lambda.HaltCert.haltTime_eq`, and the lower bounds
  `Lambda.bbTime_ge_of_cert`, `Lambda.bbSize_ge_of_cert`. Non-vacuity:
  `Lambda.haltCert_I_I : HaltCert (I I) 1` and `Lambda.one_le_bbSize_five`.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
