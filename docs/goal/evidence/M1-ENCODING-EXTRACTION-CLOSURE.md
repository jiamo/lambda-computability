# M1-ENCODING-EXTRACTION-CLOSURE

Extract the encoding helpers needed by modular computability

* The code-level operations that used to live in `Start/Basic.lean` are now in
  `Start/CodeOps.lean` (code validity, `app_code`/`lam_code`/`var_code`/`body_code`/`church_code`,
  `subst_code`, `step_code`, `code_step` and their `Primrec` proofs) and in
  `Start/CodePrimrec.lean` (arithmetized decoder, `ECF` closure format, `lift_code`,
  `subst_code'`, `step_code'`, `code_step'`).
* `Start/Encoding.lean` still builds standalone and only owns `Lambda.encode`, `Lambda.decode`
  and the `Encodable Lambda` instance.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 6 tasks validated
lake env lean Start/Encoding.lean        # no errors
lake build                               # Build completed successfully
```
