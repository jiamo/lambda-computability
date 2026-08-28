# M10-CAPSTONE-REGISTRY

**Status:** DONE_STRONG

Until now a crowning theorem and a dead file looked the same to every automatic check: both have
declarations that nothing else refers to.  This task makes the difference mechanical.

## The register — `Start/Capstones.lean`

One `#check` per terminal statement, grouped by area: the interfaces of the untyped calculus, the
size explosion, algorithmic information theory (`K`, `Kt`, universal search), Cook–Levin and the
P-uniform circuit families, the graph model and `D∞`, and `λΠ` with its set-theoretic models.
`#check` verifies name *and* type and is re-run on every build, so the register cannot rot.

## The gates — `scripts/check_closure.py`

1. **Import closure.**  Every `Start/*.lean` is reachable from `Start.lean` (a consumer of the
   whole library, such as `Start/Demo.lean`, is exempt).  Six modules were outside it and are now
   imported: `CircuitShift`, `KolmogorovPair`, `ReducesIn`, `LevinKt`, `LevinSearch`, plus
   `Capstones` itself.  A sixth, `Start/DecodeTest.lean`, could not join them: it re-declared
   `Lambda.decode_eq` and `Lambda.encode_of_decode`, which `Start.KolmogorovHalting` already
   declares, so the two could not sit in one environment.  The duplicate file has been deleted;
   the documented versions are the ones in `Start.KolmogorovHalting`.
2. **Registration.**  Every module is either referred to by another module or `#check`-ed in
   `Start/Capstones.lean`.  Twenty-one terminal modules were unregistered; all are registered now.
3. **Terminal statement first.**  A task states the Lean type it will land, and is finished when
   that type appears in `Start/Capstones.lean` — not when a prose document says so.

`python3 scripts/check_closure.py` exits 0.

## Repaired orphans

* `Start/KolmogorovPair.lean` — the additive constants of `Lambda.kolmCond_apply_le` and
  `Lambda.exists_const_kolmCond_of_pair` were off, and one `rw` had to become a `simp only`.
* `Start/CircuitShift.lean` — stale rewrites and missing `simp` lemmas after the `Cob` API drifted.

Both now compile and are registered.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.Capstones`
