# M4-SMN-UNIFORM — the s-m-n theorem in uniform coded form

## What was added

`Start/SMN.lean` (imported by `Start.lean`).

- `Lambda.smnCode c n = app_code c (church_code n)` — fixing a parameter of a coded term.
- `Lambda.smnCode_primrec` — it is primitive recursive in both arguments (`Primrec₂`).
- `Lambda.smnCode_encode`, `Lambda.decode_smnCode` — `smnCode (encode F) n` is exactly the code of
  `F (church n)`.
- `Lambda.exists_smn` — **the s-m-n theorem**: there is a primitive recursive `s` with
  `decode (s (encode F) n) = some (F (church n))` for every term `F` and every `n`.
- `Lambda.smn_realizes` — the computational form: the term coded by `smnCode (encode F) n` reduces
  on `church m` exactly as `F (church n) (church m)` does.

Previously this fact was used ad hoc inside the undecidability reductions (`Lambda.haltCode`,
`Lambda.strictHaltCode`); it is now available as a reusable statement.

## Verification

- `lake build` succeeds, no errors and no linter warnings; no `sorry` in `Start/SMN.lean`.
- `#print axioms Lambda.exists_smn`: only `propext, Classical.choice, Quot.sound`.
