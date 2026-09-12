# M12-KRIVINE-SPACE-LIVE — a space measure for the Krivine machine with sharing

`Start/KrivineHeap.lean` runs the Krivine machine on a code table and a heap with sharing, and
`Start/KrivineHeapCost.lean` measures its *time*.  Neither measures space, and the length of the
heap cannot: `Krivine.Impl.hstep` appends a cell at every administrative transition and never
removes one, so after `n` transitions the heap has `n` cells whatever the machine is doing.

`Start/KrivineSpace.lean` supplies the measure and the two theorems that make it legitimate.

## Reachability

* `Krivine.Impl.Cell.refs` — the addresses a cell refers to.
* `Krivine.Impl.reachF`, `Krivine.Impl.reach` — the addresses reachable from an address, computed
  with fuel and then with the length of the heap.  `Krivine.Impl.reachF_eq_reach` proves the
  computation does not depend on the fuel (a well-formed heap refers only downwards, so the walk
  from `p` stays below `p`), `Krivine.Impl.reach_eq` unfolds it one step,
  `Krivine.Impl.reach_refs` and `Krivine.Impl.reach_trans` are closure under references and
  transitivity, and `Krivine.Impl.reach_append` says that allocating a cell does not change what
  an old address reaches.

## The measure

* `Krivine.Impl.roots` — the environment pointer and the stack.
* `Krivine.Impl.IsLive`, `Krivine.Impl.liveList` — a cell is live when a root reaches it; the live
  addresses in increasing order.
* `Krivine.Impl.space` — **the space of a state**: the number of live cells.
  `Krivine.Impl.space_initState` (zero initially), `Krivine.Impl.space_le_heap_length`.

## Only the live cells are read

`Krivine.Impl.decState_congr_live`: two states with the same code and the same pointers, whose
heaps agree on everything reachable from the roots, represent the same abstract Krivine state.
Nothing outside the live data can influence the run, so counting only the live data is not an
under-count.

## The dead cells can be removed (`Start/KrivineSpaceGc.lean`)

* `Krivine.Impl.gcHeap`, `Krivine.Impl.gcState` — collection: keep the live cells in their
  original order and rename every reference to the rank of the address it points at
  (`Krivine.Impl.rankIn`).
* `Krivine.Impl.gcHeap_wf`, `Krivine.Impl.gcHeap_typed`, `Krivine.Impl.gcState_valid` — the
  invariant `Krivine.Impl.Valid` survives collection.
* `Krivine.Impl.decClos_gcHeap`, `Krivine.Impl.decEnvP_gcHeap`, `Krivine.Impl.gcState_dec` —
  **collection preserves the state the implementation represents**.
* `Krivine.Impl.gcState_heap_length` — the collected heap has exactly `space s` cells, so after
  collection the length of the heap *is* the space.

## The cost of a transition, in space

`Krivine.Impl.space_hstep_le`: a transition increases the space by at most one cell.  The
administrative transitions allocate one cell whose references are roots
(`Krivine.Impl.space_alloc_le`); a variable lookup allocates nothing and its new environment is
reachable from the old one (`Krivine.Impl.mem_reach_envNth`), so it cannot increase the space.

## Boundary

This task defines and justifies the measure; it says nothing yet about how many *bits* a state
costs (`M12-KRIVINE-SPACE-LOG`) or about the space of a whole run
(`M12-KRIVINE-SPACE-INVARIANCE`).
