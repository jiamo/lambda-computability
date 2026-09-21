# M14-QBF-WORD-STREAM

**Status:** DONE_STRONG

The binary code of the reduction formula is exhibited in the shape a polynomial-time compiler
needs: a concatenation of blocks, one per position of a counter, each block a closed function of
that position.

## Why this shape

The Cobham toolkit of this library produces a word by sweeping a word once and emitting a block at
every position (`Complexity.eval_blkRunTerm` for blocks that may grow with the input,
`Complexity.eval_lrunTerm` for bounded ones).  To compile the reduction one therefore has to know
that the code of `Complexity.Qbf.QBF.machineF M x s` *is* such a concatenation.  The essential
point is that the midpoint recursion of `Start/QbfReach.lean` has a **single** recursive call, so
its code is linear — one block per level — rather than a tree.

## What is built — `Start/QbfWordStream.lean`

* `Complexity.Qbf.QBF.enc_var`, `.enc_neg`, `.enc_conj`, `.enc_disj`, `.enc_all`, `.enc_ex` — the
  code of each node, as tag bits followed by the codes of the parts.
* `Complexity.Qbf.QBF.enc_exBits`, `.enc_allBits` — a quantifier prefix over a block of variables
  is a concatenation over `List.range n` of the tag bits and the index in unary.
* `Complexity.Qbf.QBF.enc_conjAll`, `.enc_disjAny` — a finite conjunction or disjunction is a
  concatenation over its list, followed by the code of the constant that closes it.
* `Complexity.Qbf.QBF.legsF`, `Complexity.Qbf.QBF.reachPre` — the antecedent and the whole block
  of one level of the midpoint recursion: the three quantifier prefixes over the scratch blocks,
  the tag bits of the implication, and the code of the antecedent.  No recursion is left in it.
* `Complexity.Qbf.QBF.enc_reachF_succ` — one level contributes exactly `reachPre`.
* `Complexity.Qbf.QBF.aAt`, `Complexity.Qbf.QBF.bAt` — the endpoint blocks at level `j`, in closed
  form.
* `Complexity.Qbf.QBF.enc_reachF` — **the code of the reachability formula is
  `(List.range k).flatMap (fun j => reachPre m (aAt a t j) (bAt b t j) (t + 3 j))` followed by the
  code of the base case**.
* `Complexity.Qbf.QBF.enc_machineF_stream` — **the code of the whole reduction formula is the two
  outer quantifier prefixes, the tag bits of the two conjunctions, the codes of the initial and
  accepting constraints, the blocks of the levels, and the code of the base case**.

## Boundary

The blocks are *described* — they are still functions of the level written in Lean, not terms of
`Complexity.Cob` producing them from a unary counter.  Turning this description into a Cobham term
(and so obtaining the `PSPACE`-hardness of `TQBF`) is what the open task `M14-TQBF-PSPACE-HARD`
now needs, and nothing else.

## Gates

```
lake build                        # Build completed successfully, 0 errors, 0 new warnings
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
```
