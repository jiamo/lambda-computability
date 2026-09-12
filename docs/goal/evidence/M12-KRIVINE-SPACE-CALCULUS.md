# M12-KRIVINE-SPACE-CALCULUS — a space measure on the calculus, and the machine runs inside it

`Start/KrivineSpaceCalculus.lean` supplies the measure that `Start/KrivineSpaceRun.lean` was
missing: a notion of space for the states of the calculus itself, and the comparison with the
live data of the machine.

## The measure

* `Krivine.Clos.cells`, `Krivine.envCells` — the space of a closure and of an environment: one
  node for the closure itself, one node per cons of its environment, recursively.
* `Krivine.State.cells` — the space of a state of the calculus: the space of its environment
  plus the space of the closures on its stack.  The code is not counted: it is a pointer into
  the program, not data that the run builds.

## The machine runs inside it

* `Krivine.Impl.reach_length_le_cells`, `Krivine.Impl.reach_length_le_envCells` — the heap
  addresses reachable from a closure pointer are at most the nodes of the closure that pointer
  decodes to, and likewise for a cons pointer and its environment.  Both are proved together by
  strong induction on the address, which terminates because a well-formed heap only refers
  backwards, and the case analysis on the cell is where the well-typedness of the heap is used:
  the environment pointer of a closure cell points at a cons cell, and the address in a cons
  cell points at a closure cell.
* `Krivine.Impl.space_le_cells_decState` — **the live cells of a valid implementation state are
  at most the nodes of the state of the calculus it represents**: the live addresses are
  distinct and all reachable from the roots, so their number is at most the total length of the
  reachability lists of the roots, which the previous item bounds root by root.  Sharing can
  only save: the machine never holds more cells than the unshared state has nodes.
* `Krivine.Impl.heap_length_le_cells_of_collected` — for a collected state, whose heap holds
  exactly its live cells, the same bound is a bound on the heap itself.
* `Krivine.Impl.gpeak_le_of_cells_le` — **the peak of a collected run is bounded by any bound on
  the calculus space of the states it passes through**, by induction along the run: a transition
  of the collected machine preserves both validity and the absence of garbage.
* `Krivine.Impl.eval_impl_space_calculus` — the space of an evaluation, in the shape of
  `Krivine.Impl.eval_impl_cost` and of `Krivine.Impl.eval_impl_space`: the collected run reaches
  the weak head normal form in a polynomially bounded number of transitions, holds exactly its
  live cells, occupies at most the calculus space of the state it represents, has its peak
  bounded by any bound on that measure along the run, and writes a state down in
  `(4 + |stack| + 3 · |heap|) · (w + 1)` bits — the logarithmic factor of
  `Start/KrivineSpaceLog.lean`.

## One pass over the binary encoding

`Start/KrivineCobBin.lean` compiles a pass over the *binary* encoding into a machine model of the
library, the analogue for space of `Start/KrivineCobStep.lean`, whose Cobham term performs a
transition on the unary encoding.  Because the fields of `Krivine.Impl.encStateBin` have fixed
width, the offsets of the encoding depend only on the width `w` and on the length of the stack,
so the terms come as a family indexed by those two numbers — the usual shape of a uniform machine
model on fixed-width data — and reading a field is reading a block of bits at a known offset.

* `Complexity.Cob.bitAtT`, `Complexity.Cob.eval_bitAtT` — the bit at a given offset, as a
  one-letter word.
* `Complexity.Cob.takeNT`, `Complexity.Cob.eval_takeNT` — the block of the first `n` bits: the
  concatenation of the first `n` bit terms, which is `List.take n` as soon as the word is long
  enough.
* `Krivine.Impl.popStackBinT` — **the pass**: the code and the environment pointer are copied
  (`take (2w+1)`), the field holding the length of the stack is rewritten to the new length, the
  first entry of the stack is skipped (`drop (4w+1)`, then `take (k·w)`) and the rest of the word
  — the heap length and the heap — is copied (`drop (3w+1+(k+1)·w)`).
* `Krivine.Impl.eval_popStackBinT` — **the pass is correct**: on the encoding, in width `w`, of a
  state whose stack has `k+1` entries, it evaluates to the encoding of the state with its stack
  popped.  The proof splits the word at the three offsets the term reads at and identifies each
  block by its length.
* `Krivine.Impl.popStackBinT_compiles` — the pass compiles into a family of Boolean circuits of
  size polynomial in the length of its input (`Tseitin.cobCompiles`), so it costs polynomial time
  in this model.
