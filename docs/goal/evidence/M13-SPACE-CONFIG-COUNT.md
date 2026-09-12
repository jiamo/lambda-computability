# M13-SPACE-CONFIG-COUNT — acceptance in bounded space is reachability in a finite graph

`Start/SpaceConfigCount.lean` is the bridge from the machine model (`M13-SPACE-MODEL`) to the
graph (`M13-SAVITCH-REACH`).

## The finite graph

* `Complexity.Space.BoundedCfg M x s` — the configurations of `M` on the input `x` whose state is
  one of the machine's states, whose input head is on the input or its end marker, and whose work
  tape uses at most `s` cells.  These three conditions are exactly the invariants proved in
  `M13-SPACE-MODEL`, so every reachable configuration is one of them
  (`Complexity.Space.mem_boundedCfg_of_steps`).
* The type is finite because a bounded configuration is determined by its state, its input head,
  the length of its work tape, the `s` cells of that tape and its work head: that is the injection
  behind the `Fintype` instance, and the count it gives is
  `Complexity.Space.card_boundedCfg_le`:

      Fintype.card (BoundedCfg M x s) ≤ q · (n + 1) · (s + 1) · 2 ^ s · (s + 1)

  (`Complexity.Space.cfgBound`).
* `Complexity.Space.BoundedCfg.step`, `.stepB` — the machine's one-step relation read on them, as
  a relation and as a Boolean function.

## Runs are walks

* `Complexity.Space.steps_boundedCfg`, `Complexity.Space.steps_of_boundedCfg` — a run of the
  machine is a walk in that graph and conversely.
* `Complexity.Space.accepts_iff_exists_reachable_accepting` — acceptance is reachability of an
  accepting configuration.
* `Complexity.Space.exists_short_accepting_run` — hence an accepting run can always be taken of
  length below `cfgBound M x s`; this is the exponential-time upper bound that a space bound
  implies, in the form the rest of the development uses.

## Gates

`lake build`, `python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.
