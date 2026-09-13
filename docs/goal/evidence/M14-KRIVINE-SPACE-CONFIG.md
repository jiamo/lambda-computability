# M14-KRIVINE-SPACE-CONFIG

**Status:** DONE_STRONG

The space measure of the Krivine implementation and the memory measure of the space-bounded
machine model are now measured on the same object: the binary word of a collected state is a work
tape, and its length is what `Start/SpaceMachine.lean` counts.

## What is built (`Start/KrivineSpaceConfig.lean`)

`Krivine.Impl.spaceConfig w s` is the configuration of the offline machine model whose work tape
is `encStateBin w (gcState s)` — the state collected and written with fixed-width binary fields —
with both heads at the origin.

* `Krivine.Impl.spaceConfig_space` — its memory measure (`Complexity.Space.Config.space`) is the
  length of that word (at least one, the cell the head stands on).
* `Krivine.Impl.gcState_eq_of_spaceConfig_eq` — at a width the two states fit in, the
  configuration determines the collected state: nothing is lost by moving to the tape.
* `Krivine.Impl.space_le_spaceConfig_space` — the tape holds at least one bit per live cell.
* `Krivine.Impl.spaceConfig_space_le` — and at most `(4 + |stack| + 3 · space) · (w + 1)` bits.
* `Krivine.Impl.spaceConfig_space_le_widthOf` — at the width a collected state needs, that is
  `(4 + |stack| + 3 · space) · (Nat.size (|tab| + |stack| + space) + 1)`: the cell measure times
  the number of bits of an address.
* `Krivine.Impl.spaceConfig_space_le_of_budget` — the `O(S · log S)` shape: if the code table,
  the stack and the live data fit in a budget `S`, the tape holds at most
  `(4 * S + 4) * (Nat.size (3 * S) + 1)` bits.
* `Krivine.Impl.spaceConfig_space_le_gpeak`, `Krivine.Impl.spaceConfig_space_le_of_run_budget` —
  the same, along a whole run of the implementation that collects at every transition, in terms
  of the peak live data of that run.

## Boundary

This is the **memory** half of the bridge.  It does not build a machine of
`Start/SpaceMachine.lean` that performs Krivine transitions on the word, so it does not by itself
place the languages decided by λ-terms within a space bound in `Complexity.Space.DSPACE`.  That
simulation — and the converse one, a λ-term simulating a space-bounded machine — remain the open
tasks `M14-KRIVINE-SPACE-CLASS` and `M14-SPACE-REASONABLE`.

## Gates

```
lake build                        # Build completed successfully, 0 errors, 0 warnings
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
```
