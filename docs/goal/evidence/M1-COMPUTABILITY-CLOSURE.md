# M1-COMPUTABILITY-CLOSURE

Replace the placeholder definitions with the real evaluator

* `Lambda.eval_placeholder` and `Lambda.compute_fun_placeholder` are gone.
* `Start/Computability.lean` now exports the real development: `Lambda.step_iter`,
  `Lambda.eval_step`, `Lambda.eval` with `Lambda.eval_partrec`, `Lambda.unbody_code`,
  `Lambda.unchurch_code` (with correctness and `Primrec` proofs) and `Lambda.compute_fun`
  with `Lambda.compute_fun_partrec`.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 6 tasks validated
lake env lean Start/Computability.lean   # no errors
lake build                               # Build completed successfully
```
