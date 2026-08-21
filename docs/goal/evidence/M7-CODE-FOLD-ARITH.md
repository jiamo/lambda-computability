# M7-CODE-FOLD-ARITH

**Status:** DONE_STRONG

Module `Start/CodeArith.lean` (imported by `Start.lean`).

Several later developments (busy beavers, the halting/`K` bridge, the enumeration behind
`Ω`) need numerical attributes of a term to be computable *from its code*. They are all
structural folds, so the fold is arithmetized once.

* `Lambda.termFold fv fapp flam` — the generic fold over terms.
* `Lambda.codeFold` — the same fold computed on codes; `Lambda.codeFold_correct` says
  `codeFold fv fapp flam (encode t) = termFold fv fapp flam t`, and
  `Lambda.codeFold_primrec` says it is primitive recursive as soon as `fv`, `fapp`, `flam`
  are (via `Lambda.codeFoldStep_primrec` and course-of-values recursion).
* `Lambda.size_code`, `Lambda.size_code_primrec` — the syntactic size used by plain
  Kolmogorov complexity is primitive recursive on codes (`Lambda.size_eq_termFold`).
* `Lambda.freeMax`, `Lambda.freeMax_code`, `Lambda.freeMax_code_primrec` — one more than
  the largest free de Bruijn index; `Lambda.isClosedAt_iff_freeMax_le` and
  `Lambda.isClosed_iff_freeMax_eq_zero` turn closedness into the primitive recursive test
  `Lambda.isClosed_code` (`Lambda.isClosed_code_primrec`).
* `Lambda.encBound` — a monotone (`Lambda.encBound_mono`), primitive recursive
  (`Lambda.encBound_primrec`) bound with
  `Lambda.encode_le_encBound : size t ≤ n → encode t ≤ encBound n`, which converts "search
  all terms of size ≤ n" into a bounded search over codes.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
