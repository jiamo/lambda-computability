# M14-QBF-COB-PIECES

**Status:** DONE_STRONG

The first pieces of the code of the reduction formula are now *written by Cobham terms*, not only
described.

## What is built

### `Start/CobhamRange.lean` — one block per index of a range

The block-emitting recursion of `Start/CobhamBlock.lean` sweeps a word from the right, so the
index of a block has to be recovered from the counter.  `Complexity.Cob.dropN` drops as many bits
off its second argument as its first is long (`Complexity.Cob.eval_dropN`), which on unary words
is truncated subtraction (`Complexity.Cob.eval_dropN_replicate`).  With it,
`Complexity.rangeEmitTerm` writes `(List.range n).flatMap W` from `1^n` and a parameter word whose
leading ones carry `n` (`Complexity.eval_rangeEmitTerm`), the block of the index `l` being the
value of a given term at `1^l` and the parameter.

### `Start/CobhamFields.lean` — the parameter word

`Complexity.fieldsWord` writes a list of naturals in unary, each field closed by a zero bit, and
`Complexity.Cob.fieldTerm k` reads the `k`-th field (`Complexity.Cob.eval_fieldTerm`).

### `Start/QbfCobPrefix.lean` — the quantifier prefixes

`Complexity.Qbf.QBF.quantPrefixTerm` writes the code of a nest of `n` quantifiers over the
variables `o, …, o + n - 1` from the width and the offset in unary
(`Complexity.Qbf.QBF.eval_quantPrefixTerm`); with the streaming form of the code this gives
`Complexity.Qbf.QBF.enc_exBits_eval` and `Complexity.Qbf.QBF.enc_allBits_eval`.

### `Start/QbfCobEqBlock.lean` — the block-equality formulas

`Complexity.Qbf.QBF.idxTerm` writes a variable index `i * m + l` in unary from the field `i * m`
and the position `l` (`Complexity.Qbf.QBF.eval_idxTerm`); the products are computed once, outside
the sweep, so the block written at a position stays short and the padding constant of the term
does not depend on the instance.  `Complexity.Qbf.QBF.enc_eqBlock_eval` shows that the code of
`eqBlock m i j` is the value of one Cobham term at `1^m` and the unary fields `m, i * m, j * m`,
followed by the code of the constant that closes the conjunction.

### `Start/QbfCobLevel.lean` — the block of a level

Composing the two, `Complexity.Qbf.QBF.levelTerm` writes the block that one level of the midpoint
recursion contributes: its three quantifier prefixes and the four block equalities of its
antecedent.  The parameter word of a level (`Complexity.Qbf.QBF.levelParam`) carries the width and
the five products of a block index with the width in unary, and the pieces assemble the parameter
words they expect out of those fields (`Complexity.Qbf.QBF.eval_prefixArg`,
`Complexity.Qbf.QBF.eval_eqArg`).  `Complexity.Qbf.QBF.reachPre_eval` proves the block is that
term's value.

## Boundary

What remains for the `PSPACE`-hardness of `TQBF` is the rest of the assembly: the sweep over the
levels of the midpoint recursion, which has to build the parameter word of each level from the
counter, the constraints of the machine itself
(`stepF`, `initF`, `accF`, whose case lists depend on the input word and on thresholds compared in
unary), and the outer composition producing the whole code from the input.  That is the remaining
content of `M14-TQBF-PSPACE-HARD`.

## Gates

```
lake build                        # Build completed successfully, 0 errors, 0 new warnings
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```
