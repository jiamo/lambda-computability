# M1-MODULAR-ENTRYPOINT-SWITCH

Make the modular files the canonical Start entrypoint

* `Start.lean` imports the modular split directly: `Start.Tactics`, `Start.Syntax`,
  `Start.Reduction`, `Start.Church`, `Start.Encoding`, `Start.CodeOps`, `Start.Computability`,
  `Start.CodePrimrec`, `Start.EvalSound`, `Start.Arithmetic`, `Start.Combinators`, `Start.Sqrt`,
  `Start.Pairing`, `Start.Recursion`, `Start.Boundary`, and finally the `Start.Basic` shim.
* The default `lake build` target therefore builds every module, including `Start.Boundary`,
  which the old entrypoint never compiled.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 6 tasks validated
lake env lean Start.lean                 # no errors
lake build                               # Build completed successfully
```
