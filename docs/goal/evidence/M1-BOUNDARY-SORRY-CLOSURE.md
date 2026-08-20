# M1-BOUNDARY-SORRY-CLOSURE

Close the remaining sorry in Start.Boundary

* `Start/Boundary.lean` contains no `sorry` (checked with `rg -n "sorry" Start/`).
* `EncodingBoundary.fromConcrete.succ_correct` is now `Lambda.succ_correct`, proved in
  `Start/Church.lean` (extracted from the old monolith together with `Lambda.iterate`,
  `Lambda.church_reduces_iterate` and `Lambda.succ_works`).
* The record was also strengthened: `EncodingBoundary` now carries `church_closed`,
  `church_normal` and `church_injective` instead of the trivial `church_is_term` field, and
  `ComputabilityInternalizer` is indexed by the function it computes, with
  `ComputabilityInternalizer.toLambdaComputable` as the roundtrip.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 6 tasks validated
lake env lean Start/Boundary.lean        # no errors
lake build                               # Build completed successfully
```
