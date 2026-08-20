# M1-LINTER-HARDENING

Ratchet down the warning surface

Strategy: clean the modules one warning class at a time, never by disabling a linter.

Result: the warning count dropped from 1072 to 229 and nine warning classes are now empty.

| class | before | after |
|---|---:|---:|
| `linter.style.longLine` | 763 | 89 |
| `linter.flexible` | 84 | 83 |
| `linter.style.multiGoal` | 59 | 57 |
| `linter.unusedSimpArgs` | 56 | 0 |
| `linter.style.setOption` | 23 | 0 |
| `linter.unusedVariables` | 22 | 0 |
| `linter.unnecessarySimpa` | 20 | 0 |
| `linter.style.refine` | 15 | 0 |
| `linter.unusedTactic` | 12 | 0 |
| `linter.style.openClassical` | 12 | 0 |
| `linter.unnecessarySeqFocus` | 3 | 0 |
| `linter.unreachableTactic` | 1 | 0 |

What was done:

* dropped 204 leftover `#check`/`#print` debugging commands during the module split;
* removed unused `simp` arguments, no-op tactics and unnecessary `simpa`/`<;>` uses;
* removed unused binders and hypotheses (and made `natPair'_case_lt`/`natPair'_case_ge` state
  the value of `Nat.pair` in each case, so their hypotheses are load-bearing);
* replaced `refine'` by `refine ... ?_`;
* removed file-level `set_option maxHeartbeats/synthInstance.*`, keeping a single documented
  scoped `set_option maxHeartbeats ... in`;
* removed `open scoped Classical` (no module needed it);
* reflowed long declaration, comment and proof lines.

The remaining classes (`longLine`, `flexible`, `multiGoal`) need per-proof restructuring and are
left as follow-up work.

Gates:

```
python3 scripts/goal_state.py validate   # OK: 6 tasks validated
lake build                               # Build completed successfully
```
