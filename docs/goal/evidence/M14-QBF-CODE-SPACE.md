# M14-QBF-CODE-SPACE — the memory of the QBF evaluator, in the length of the code

**Status:** DONE_STRONG

`Start/Qbf.lean` bounds the memory of the evaluating stack machine by
`varBound p + (height p + 1) · (2 w + 2)` bits, with `w` the width of a pointer into the formula,
which with `w = size p` is quadratic in the *size* of the formula
(`Complexity.Qbf.tqbf_memBits_le_size`).  A membership `TQBF ∈ PSPACE` is, however, a statement
about the *code*: the input of a machine deciding `Complexity.Qbf.tqbfLang` is the binary word of
`Start/QbfWord.lean`, and the bound has to be a polynomial in the length of that word.

`Start/QbfCodeSpace.lean` converts the currency.

## What is proved

* `Complexity.Qbf.QBF.size_le_length_enc` — the code spends at least one bit per node, so
  `size p ≤ |enc p|`.
* `Complexity.Qbf.QBF.varBound_le_length_enc` — every variable index is written in unary, so the
  number of variables the assignment must hold is at most `|enc p|`.
* `Complexity.Qbf.QBF.height_lt_length_enc` — hence the depth of the recursion, and with it the
  number of activation records, is below `|enc p|`.
* `Complexity.Qbf.tqbf_memBits_le_length_enc` — **every state of the evaluator on a closed formula
  fits in `2 n² + 3 n` bits**, where `n = |enc p|`: a pointer of `n` bits addresses the code, the
  assignment costs at most `n` bits and the stack at most `n` records of `2 n + 2` bits.
* `Complexity.Qbf.tqbf_memBits_le_length` — the same for a word of the language, i.e. for `w` the
  code of `p`.

## Boundary

This is a bound on the memory measure of the stack machine, not yet a membership in
`Complexity.Space.PSPACE`: what remains for `M14-TQBF-IN-PSPACE` is an offline machine of
`Start/SpaceMachine.lean` which decodes its input word and performs the evaluation on its work
tape, within the bound proved here.

## Gates

```
lake build                        # Build completed successfully (9181 jobs), 0 errors
python3 scripts/check_sorry.py    # OK: no sorry/admit in 462 modules
python3 scripts/check_closure.py  # OK: 461 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```
