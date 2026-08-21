# M7-LEFTMOST-CLOCK

**Status:** DONE_STRONG

Module `Start/LeftmostRun.lean` (imported by `Start.lean`).

`Start/Leftmost.lean` proves the normal order strategy normalizing; the complexity
developments need a *clock* on top of it.

* `Lambda.nstep` — the leftmost step made total (normal forms are fixed points:
  `Lambda.nstep_of_is_normal`), arithmetized by `Lambda.nstep_code`
  (`Lambda.nstep_code_primrec`, `Lambda.nstep_code_iterate`,
  `Lambda.nstep_code_iterate_primrec`).
* `Lambda.reduces_nstep_iterate` — every iterate is reachable by reduction.
* `Lambda.hasNormalForm_iff_exists_normal_iterate` — `t` has a normal form iff
  `nstep^[k] t` is normal for some `k`; `Lambda.haltTime t` is the least such `k`
  (`Lambda.is_normal_nstep_haltTime`, `Lambda.haltTime_le`) and `Lambda.nf t` the normal
  form (`Lambda.reduces_nf`, `Lambda.nf_eq_of_reduces_normal`).
* `Lambda.isNormal_code`, `Lambda.haltsBy_code` — primitive recursive tests ("this code is
  a normal form", "this code reaches a normal form within `k` leftmost steps"), with
  `Lambda.hasNormalForm_iff_exists_haltsBy_code`.
* `Lambda.hasNormalForm_lam`, `Lambda.closure`, `Lambda.hasNormalForm_closure_iff`,
  `Lambda.isClosed_closure` — an arbitrary term may be replaced by a closed term with the
  same halting behaviour.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
