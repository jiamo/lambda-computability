# M14-QBF-WORD-LANG

**Status:** DONE_STRONG

`TQBF` is now available as a *language of words*, and the reduction of `Start/QbfPspace.lean` as a
map of words whose output length — not only whose node count — is bounded by a single polynomial
in the input length.

## What is built

### `Start/QbfWord.lean` — the code of a formula

* `Complexity.Qbf.QBF.unary` — a natural number in unary, terminated by a zero bit.
* `Complexity.Qbf.QBF.enc` — a self-delimiting code: three tag bits per node (two for a variable
  or a negation), the variable indices in unary, then the codes of the subformulas in order.
* `Complexity.Qbf.QBF.decUnary`, `Complexity.Qbf.QBF.dec` — the decoder, driven by a fuel bound
  which the size of the formula supplies.
* `Complexity.Qbf.QBF.dec_enc_append` — the decoder reads a formula back off the front of its
  code, so `Complexity.Qbf.QBF.enc_injective`: the code is injective.
* `Complexity.Qbf.QBF.length_enc_le` — a formula of size `n` whose variables are below `v` has a
  code of length at most `n * (v + 3)`.
* `Complexity.Qbf.tqbfLang`, `Complexity.Qbf.tqbfLang_enc_iff` — the language of the codes of the
  true closed formulas, and the characterization of its members.

### The reduction as a map of words

`Complexity.Qbf.QBF.varBoundOf` and `Complexity.Qbf.QBF.wordBound` express a bound on the variable
indices and on the length of the code of the reduction formula as functions of the input length;
`Complexity.Qbf.QBF.varBound_machineF_le_varBoundOf` and
`Complexity.Qbf.QBF.length_enc_machineF_le` prove them, using the variable bound of
`Start/QbfVarBound.lean` and the size bound of `Start/QbfPspace.lean`, and
`Complexity.Qbf.QBF.polyBound_wordBound` shows the length bound is polynomial whenever the space
bound is.

## Results

* `Complexity.Qbf.QBF.npspace_polyLength_tqbfWord` — **every language in `NPSPACE` is mapped into
  `tqbfLang` by one map of words whose output length is bounded by a single polynomial in the
  input length**;
* `Complexity.Qbf.QBF.pspace_polyLength_tqbfWord` — the same for `PSPACE`.

## Bookkeeping

The module was written but left outside the import closure of `Start.lean`, so it was neither
built nor gated.  It is now imported by `Start.lean` (together with `Start/QbfVarBound.lean`) and
registered with prose and `#check`s in `Start/Capstones.lean`, so `scripts/check_closure.py`
covers it.

## Boundary

The map of words is not shown to be computable in polynomial time — to be the value of a term of
`Complexity.Cob`.  That is the only missing ingredient of the `PSPACE`-hardness of `TQBF`, and it
stays recorded as the open task `M14-TQBF-PSPACE-HARD`.

## Gates

```
lake build                        # Build completed successfully, 0 errors, 0 new warnings
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```
