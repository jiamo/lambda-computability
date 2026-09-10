# M11-KRIVINE-UNIT-COST

**Status:** DONE_STRONG

`M11-KRIVINE-INVARIANCE` bounds the *number* of transitions of the Krivine machine.  This task is
the other half: a transition has to be *performed*, on a state written down as a word, at a cost
polynomial in the length of that word.  Two modules were added.

## The implementation (`Start/KrivineHeap.lean`, first exit criterion)

The abstract state of `Start/Krivine.lean` is a tree — closures carry environments which carry
closures — so writing it down naively can cost exponentially more than the run that produced it.
The implementation shares everything instead:

* `Krivine.Impl.Node`, `Krivine.Impl.Tab`, `Krivine.Impl.flatten` — the initial term is flattened
  **once** into a table of nodes, and every piece of code in the run is an address in that table.
  `Krivine.Impl.decTerm_flatten` proves the table decodes back to the term,
  `Krivine.Impl.tabOf_length` that it has one node per syntax node;
* `Krivine.Impl.Cell`, `Krivine.Impl.Heap` — the environments are linked lists in a heap of
  cells; a `beta` transition allocates one cons cell in front of the current environment and a
  `app` transition allocates one closure cell.  Nothing is copied, and the tails are shared;
* `Krivine.Impl.decClos`, `Krivine.Impl.decEnvP`, `Krivine.Impl.decState` — the abstract state a
  heap state represents.  `Krivine.Impl.decClF_prefix` is the key stability lemma: decoding reads
  only the cells that are already there, so allocating at the end disturbs nothing;
* `Krivine.Impl.Valid` — the invariant (acyclic, well-typed heap, valid pointers), preserved by
  `Krivine.Impl.Valid.hstep`.

**The simulation is exact.**  `Krivine.Impl.hstep_trans` — a step of `Krivine.Impl.hstep` is the
transition of `Krivine.Trans` *with the same label* between the decoded states — and
`Krivine.Impl.hstep_isNone_iff` — the implementation is stuck exactly when the machine is.

## The word encoding and the cost (`Start/KrivineHeapCost.lean`)

* `Krivine.Impl.encState` writes a state as a word over `Bool`: unary addresses, self-delimiting
  cells, the heap written once.  `Krivine.Impl.encState_inj` proves the encoding **faithful**: a
  state is determined by its word.  Unary addresses keep the arithmetic elementary; a binary
  encoding would only be shorter.
* `Krivine.Impl.encState_length_le` (fourth exit criterion, first half) — the length of the
  encoding is at most `encBound T m`, a polynomial in the size `T` of the table and the number
  `m` of heap cells.
* `Krivine.Impl.hstep_shape`, `Krivine.Impl.hstep_heap_length`, `Krivine.Impl.hstep_sized` — a
  transition allocates at most one cell and never lets the stack outgrow the heap, so after `n`
  transitions from the initial state the heap has at most `n` cells: the encoding of a reachable
  state is polynomial in `|t|` and in the number of transitions (fourth exit criterion).
* `Krivine.Impl.walkSteps_le` — a variable lookup visits at most as many cells as the heap has,
  because the addresses it visits strictly decrease.  Hence `Krivine.Impl.hstepPasses_le`: one
  transition is at most `m + 1` sequential passes over the encoded state.
* `Krivine.Impl.hstepCost`, `Krivine.Impl.hstepCost_le` (third exit criterion, in the pass cost
  model) — one transition costs at most `(m + 2) · (encBound T m + 1)`.
* `Krivine.Impl.exists_hrun_of_run` — every run of the abstract machine is performed by the
  implementation, step for step, which is what lets the transition count of
  `Krivine.eval_cost` be reused.
* `Krivine.Impl.eval_impl_cost` (fifth exit criterion) — **the headline**: a term the weak head
  strategy normalises in `k` steps is evaluated by the implementation from the encoded initial
  state to a stuck state, in `n ≤ b + |t| · (1 + b · (b + 1))` transitions with `b ≤ k` β
  transitions, reaching the weak head normal form of `t` in exactly `b` β-steps, at a total cost
  at most `n · ((n + 2) · (encBound |t| n + 1))`.

## The second exit criterion, met by `M11-KRIVINE-PASS-MACHINE`

The cost above is counted in *sequential passes over the encoded state*, each pass costing the
length of that encoding.  What was left open here — a term of one of the library's machine models
computing `encState s'` from `encState s` — is supplied by `M11-KRIVINE-PASS-MACHINE`:
`Krivine.Impl.stepT` is a single Cobham term doing exactly that (`Krivine.Impl.eval_stepT`), its
cost in that model is polynomial in the length of its input (`Krivine.Impl.stepT_compiles`), and
`Krivine.Impl.eval_impl_cob_cost` composes the two with the transition count.  The task therefore
has no open boundary left.

## Gates

Both modules are imported by `Start.lean`, are `sorry`-free and linter-clean, and the headline
results (`Krivine.Impl.eval_impl_cost`, `Krivine.Impl.hstep_trans`,
`Krivine.Impl.encState_length_le`) depend only on `propext`, `Classical.choice`, `Quot.sound`.
`lake build`, `python3 scripts/goal_state.py validate`, `python3 scripts/check_closure.py` and
`scripts/pack_gate.sh` all pass.
