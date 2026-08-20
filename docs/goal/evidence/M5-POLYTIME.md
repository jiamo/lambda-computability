# M5-POLYTIME

**Status:** DONE_STRONG

New module `Start/TM2PolyTime.lean` (imported by `Start.lean`).

* `TM2Partrec.HaltsWithin` — the machine has produced its output within `m` steps, at the level of
  symbol codes; `TM2Partrec.haltsWithin_of_outputsInTime` shows `Mathlib`'s `Turing.TM2OutputsInTime`
  implies it, and `TM2Partrec.dom_evalCode_of_haltsWithin` that a bounded run converges.
* `TM2Partrec.TM2TimeRealization`, `TM2ComputableNatInTime`, `TM2ComputableNatInPolyTime` — the
  time-bounded refinement of the machine realization record from `Start/TM2Capstone.lean`.
* `TM2Partrec.dom_of_tm2ComputableNatInTime`, `computable_of_tm2ComputableNatInTime`,
  `computable_of_tm2ComputableNatInPolyTime`, `lambdaComputable_of_tm2ComputableNatInPolyTime` —
  a time bound forces totality, computability, and lambda-definability.
* `TM2Partrec.haltTM`, `idTimeRealization`, `tm2ComputableNatInTime_id`,
  `tm2ComputableNatInPolyTime_id` — a one-instruction machine computing the identity in one step,
  so the notions are not vacuous.
* `TM2Partrec.partrec_of_tm2ComputableInPolyTime`, `haltsWithin_of_tm2ComputableInPolyTime` — the
  bridge to `Mathlib`'s own `Turing.TM2ComputableInPolyTime`.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` on the headline results reports only
`propext, Classical.choice, Quot.sound`.
