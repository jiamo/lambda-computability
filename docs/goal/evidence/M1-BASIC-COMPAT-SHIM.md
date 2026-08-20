# M1-BASIC-COMPAT-SHIM

Reduce Start.Basic to a compatibility layer

* `Start/Basic.lean` went from 7890 lines to a short re-export shim that documents the module
  map; `import Start.Basic` keeps working for downstream users and every theorem name is
  unchanged.
* The development now lives in `Start/Syntax.lean`, `Start/Reduction.lean`, `Start/Church.lean`,
  `Start/Encoding.lean`, `Start/CodeOps.lean`, `Start/Computability.lean`,
  `Start/CodePrimrec.lean`, `Start/EvalSound.lean`, `Start/Arithmetic.lean`,
  `Start/Combinators.lean`, `Start/Sqrt.lean`, `Start/Pairing.lean` and `Start/Recursion.lean`.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 6 tasks validated
lake build                               # Build completed successfully
```
