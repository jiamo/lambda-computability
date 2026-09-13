# M14-QBF-REACH-FORMULA

**Status:** DONE_STRONG

The midpoint recursion of `Start/SavitchReach.lean` is written as a quantified Boolean formula,
proved correct, and proved small.  This is the formula half of the PSPACE-hardness of `TQBF`.

## What is built (`Start/QbfReach.lean`)

Vertices are words of `m` bits, read off an assignment in **blocks**: block `i` is the variables
`i * m, …, i * m + m - 1` (`Complexity.Qbf.blockVal`).  Writing a word into a block is
`Complexity.Qbf.setBits`, and the two facts a construction with scratch space needs are proved:
reading back the block just written returns the word, and writing a block leaves every other
block alone (`blockVal_setBits_self`, `blockVal_setBits_of_ne`).

Quantification over a block (`QBF.allBits`, `QBF.exBits`) is quantification over a word of that
width (`QBF.eval_allBits`, `QBF.eval_exBits`), and equality of two blocks is a formula of size
`10 * m + 4` (`QBF.eqBlock`, `QBF.eval_eqBlock`, `QBF.size_eqBlock`).

The formula itself is `QBF.reachF stepF m k a b t`.  The edge relation enters only as a family of
formulas `stepF a b`, one per pair of blocks.  At depth `k + 1` the formula quantifies
existentially over a midpoint in block `t`, then universally over a pair of endpoints in blocks
`t + 1` and `t + 2` guarded by

```
(block (t+1) = block a ∧ block (t+2) = block t) ∨ (block (t+1) = block t ∧ block (t+2) = block b)
```

so that a **single** recursive call stands for both legs — which is exactly why the formula grows
by a fixed amount per level instead of doubling.

## Results

* `Complexity.Qbf.QBF.eval_reachF` — the formula holds under an assignment exactly when the word
  in block `a` reaches the word in block `b` within `2 ^ k` steps, in the sense of
  `Complexity.Reach.reachLe`.  The hypotheses are that `stepF a b` expresses the edge relation
  between the words in blocks `a` and `b` (for every assignment), that the relation relates words
  of width `m` to words of width `m`, and that the two endpoint blocks lie below the scratch
  area `t`.
* `Complexity.Qbf.QBF.size_reachF_le` — the size is at most
  `c + 10 * m + 5 + k * (43 * m + 21)`, where `c` bounds the size of one step formula.
* The hypotheses are satisfiable: an example in the module instantiates the construction with the
  equality relation, whose step formula is `eqBlock`.

## Boundary

What remains for `TQBF` to be proved PSPACE-hard is the *machine* half: that the configuration
graph of a machine of `Start/SpaceMachine.lean` running in space `s` admits such a family of step
formulas — configurations encoded as words of `O(s + log n)` bits and one formula per pair of
blocks expressing one transition — computed from the input in polynomial time.  That is recorded
as the open task `M14-TQBF-PSPACE-HARD`.

## Gates

```
lake build                        # Build completed successfully, 0 errors, 0 warnings
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
```
