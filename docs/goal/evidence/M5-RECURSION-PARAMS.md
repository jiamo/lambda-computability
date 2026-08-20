# M5-RECURSION-PARAMS

**Status:** DONE_STRONG

New module `Start/RecursionParams.lean` (imported by `Start.lean`).

* `Lambda.paramW`, `Lambda.paramFix`, `Lambda.paramCode` — the parameterised diagonal term
  `W_y = λz. F (diagTerm z) (church y)`, its self-application `X_y = W_y ⌜W_y⌝`, and its code.
* `Lambda.paramCode_primrec` — the code of the fixed point is primitive recursive in the parameter.
* `Lambda.paramFix_reduces` — `X_y ↠ F ⌜X_y⌝ (church y)` for every closed `F`.
* `Lambda.exists_recursion_with_parameters` — the packaged statement: a primitive recursive `s`
  with `decode (s y) = some X` and `X ↠ F (church (s y)) (church y)`.

Gates: `lake build Start.RecursionParams` succeeds; no `sorry`.
