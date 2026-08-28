# M7-LEGACY-MODULE-BACKFILL

**Status:** DONE_STRONG

A handful of modules had been written as by-products of earlier milestones without a board
task of their own. They are recorded here so that every file under `Start/` is accounted
for.

* `Start/FixedPoint.lean` — Turing's fixed-point combinator `Lambda.Theta = A A` with
  `A = λx y. y (x x y)`. Unlike Curry's `Y` it satisfies the fixed-point equation as a
  *reduction*: `Lambda.Theta_reduces : Θ F ↠ F (Θ F)`, whence
  `Lambda.exists_fixed_point`. Used by the second recursion theorem (M4).
* `Start/Undecidable.lean` — the halting problem for the lambda calculus in the form
  "reduces to a Church numeral": `Lambda.not_computablePred_codeConverges`, by reduction
  from `ComputablePred.halting_problem` through the realizer of `Start/PartialCapstone.lean`
  (M3/M4).
* `Start/NormalizationUndecidable.lean` — the standard strengthening: whether a term has a
  normal form at all is undecidable
  (`Lambda.not_computablePred_codeHasNormalForm`). The extra ingredient is
  `Lambda.partialTerm_not_hasWhnfEval`: the strict realizer has no weak head normal form
  when the simulated computation diverges. This is the undecidability result all of M7's
  complexity theory reduces to.
* `Start/Leftmost.lean` — the leftmost-outermost (normal order) strategy is normalizing;
  it discharges the hypothesis `Lambda.EvalNormalization` left open by
  `Start/EvalSound.lean` (M2), using the weak head machinery of `Start/WeakHead.lean` and
  `Start/Standardization.lean`.
* `Start/DecodeTest.lean` — a small standalone check of the decoding equations
  (`Lambda.decode_eq`, `Lambda.encode_of_decode`); not imported by `Start.lean`, but built
  by the M7-VERIFICATION-DEBT gate.  *(Deleted since: it duplicated the declarations of
  `Start/KolmogorovHalting.lean`, so it could never enter the import closure.  The documented
  versions are the ones in `Start.KolmogorovHalting`.)*
* `Start/Demo.lean` — the guided tour of the development; likewise built explicitly.

Every other module under `Start/` is named in the exit criteria or the evidence note of some
board task.
