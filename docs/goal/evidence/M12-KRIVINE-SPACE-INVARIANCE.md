# M12-KRIVINE-SPACE-INVARIANCE — the machine runs in the space of its live data

`Start/KrivineSpaceRun.lean` runs the shared Krivine machine with a **collection after every
transition** and puts together the two previous tasks.

## The collected machine

* `Krivine.Impl.gstep` — one transition of `Krivine.Impl.hstep` followed by
  `Krivine.Impl.gcState`; `Krivine.Impl.grun` runs it.
* `Krivine.Impl.gstep_trans`, `Krivine.Impl.gstep_valid`, `Krivine.Impl.gstep_isNone_iff` — it
  makes the same transitions of `Krivine.Trans` between the same decoded states, keeps the
  invariant, and is stuck exactly when the machine is.
* `Krivine.Impl.exists_grun_of_run` — every run of the abstract machine is performed by it.

## No garbage

* `Krivine.Impl.Collected s` — the heap holds exactly the live cells, `|heap| = space s`.
* `Krivine.Impl.gstep_collected`, `Krivine.Impl.grun_collected` — every state of a collected run
  is collected.  This rests on `Krivine.Impl.space_gcState` (`Start/KrivineSpace.lean`):
  collection loses no live cell, because reachability survives the renaming
  (`Krivine.Impl.mem_reach_gcHeap`) and ranks separate live addresses.
* By contrast the heap of `Krivine.Impl.hrun` grows by one cell per transition, so its length is
  a time measure.

## The memory of the run

* `Krivine.Impl.gpeak` — the peak memory of a collected run; `Krivine.Impl.gpeak_le` bounds it by
  the initial memory plus the number of transitions, and
  `Krivine.Impl.heap_length_le_gpeak_of_grun` bounds every state of the run by the peak.
* `Krivine.Impl.encStateBin_length_le'` — a state costs at most
  `(4 + |stack| + 3 · |heap|) · (w + 1)` bits, and for a collected state `|heap|` *is* its space,
  so with `w = Krivine.Impl.widthOf` this is the logarithmic overhead of
  `M12-KRIVINE-SPACE-LOG`.
* `Krivine.Impl.eval_impl_space` — **the space statement for an evaluation**, in the shape of the
  time statement `Krivine.Impl.eval_impl_cost`: a term the weak head strategy normalises in `k`
  steps is evaluated by the collected implementation to a stuck state holding its weak head
  normal form, its final memory holds exactly its live cells, is bounded by the peak of the run,
  which is at most the number of transitions, and is written in
  `(4 + |stack| + 3 · |heap|) · (w + 1)` bits.

## The comparison with the calculus

The peak is bounded here by the number of transitions.  The comparison with a *space* cost model
of the λ-calculus itself is `M12-KRIVINE-SPACE-CALCULUS`: `Krivine.State.cells` measures a state
of the calculus by the nodes of its closure trees, `Krivine.Impl.space_le_cells_decState` bounds
the live cells of a valid implementation state by that measure, and
`Krivine.Impl.gpeak_le_of_cells_le` bounds the peak of a collected run by any bound on the
measure along the run (`Start/KrivineSpaceCalculus.lean`).  A pass over the binary encoding
compiled into a machine model of the library — the analogue, for space, of
`Start/KrivineCobStep.lean` — is `Krivine.Impl.popStackBinT` in `Start/KrivineCobBin.lean`.
