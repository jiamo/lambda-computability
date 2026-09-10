# M11-KRIVINE-PASS-MACHINE

**Status:** DONE_STRONG

`M11-KRIVINE-UNIT-COST` implements the Krivine machine on a code table and a heap, writes its
states as words (`Krivine.Impl.encState`) and counts the cost of a run in *sequential passes* over
that encoding.  Its open boundary was that no term of a machine model of the library was exhibited
that performs such a pass: `Krivine.Impl.hstep` was a function on structured states, not a word
function of the library's models.  This task closes that gap, for the model `Complexity.Cob` —
Cobham's class of polynomial-time functions on words, the model in which the uniformity of the
Cook–Levin reduction is stated in this library.

## Reading and writing the encoding with Cobham terms (`Start/KrivineCobWord.lean`)

The code table is written as a word by `Krivine.Impl.encNode` and `Krivine.Impl.encTab`, in the
same self-delimiting style as the cells of the heap.  Every field of an encoded state is then read,
skipped or rebuilt by a Cobham term, each with its `eval` lemma:

* `Krivine.Impl.leadUT`, `Krivine.Impl.takeUT`, `Krivine.Impl.dropUT` — a unary field;
* `Krivine.Impl.takePtrT`, `Krivine.Impl.dropPtrT`, `Krivine.Impl.dropCellT`,
  `Krivine.Impl.dropNodeT` — a pointer, a cell of the heap, a node of the table;
* `Krivine.Impl.iterT` — iterating a term as many times as a unary argument counts, with the
  instances `Krivine.Impl.dropCellsT`, `Krivine.Impl.dropNodesT`, `Krivine.Impl.dropUsT`;
* `Krivine.Impl.countCellsT` — the number of cells of a heap, a finite-state transduction.

The two consequences that the transition needs are `Krivine.Impl.eval_dropCellsT` —
**dereferencing an address is a Cobham function** — and `Krivine.Impl.eval_countCellsT`.

## One transition as a Cobham term (`Start/KrivineCobStep.lean`, exit criteria 1 and 2)

`Krivine.Impl.stepT` is a single Cobham term of two arguments, the encoded state and the encoded
code table.  Its three branches follow the three cases of `Krivine.Impl.hstep`: an application
pushes the closure of its argument, an abstraction pops the stack and allocates a cons cell, a
variable walks down the environment.  The walk is `Krivine.Impl.walkT`, an iteration of
`Krivine.Impl.walkStepT` whose length is the variable index; `Krivine.Impl.eval_walkT` proves it
computes the pointer walk `Krivine.Impl.envDrop`, itself identified with variable lookup by
`Krivine.Impl.envNth_eq_envDrop`.

`Krivine.Impl.eval_stepT` is the agreement statement: on the encoding of a state satisfying the
invariant `Krivine.Impl.Valid`, the term evaluates to the encoding of the successor state, and to
the empty word exactly when the machine is stuck.  So the word function is *the* transition, read
through `Krivine.Impl.encState`.

## The cost, and the composition (exit criteria 3 and 4)

* `Krivine.Impl.stepT_compiles : Tseitin.CobCompiles stepT` — the term compiles into a family of
  Boolean circuits whose size is bounded by a monotone polynomial in the width of its arguments.
  That is the cost measure of this model, so **a transition costs polynomial time in the length of
  the encoded state**.  It is the library's general compilation theorem
  (`Complexity.Tseitin.cobCompiles`, proved in `Start/CobhamCircuit.lean` and
  `Start/CobhamBRec.lean`) applied to `stepT`.
* `Krivine.Impl.valid_hrun` and `Krivine.Impl.eval_stepT_hrun` — the invariant is preserved along a
  run, so every state a run reaches is transformed by the term into its successor.
* `Krivine.Impl.eval_impl_cob_cost` — **the headline**: a term the weak head strategy normalises in
  `k` steps is evaluated by the implementation from the encoded initial state to a stuck state in
  `n ≤ b + |t| · (1 + b · (b + 1))` transitions with `b ≤ k` β transitions, reaching the weak head
  normal form of `t` in exactly `b` β-steps, at a cost bounded as in
  `Krivine.Impl.eval_impl_cost`, *and every one of those transitions is performed by the single
  Cobham term* `Krivine.Impl.stepT`.

## Boundary (exit criterion 5)

The open boundary of `M11-KRIVINE-UNIT-COST` is emptied: its second exit criterion is now met by
`Krivine.Impl.eval_stepT` in the model `Complexity.Cob`, and that task is `DONE_STRONG`.  What the
statement does *not* claim is a Turing machine: the transition is a Cobham term, whose cost is the
size of the circuits it compiles into, not the step count of `Turing.FinTM2`
(`Start/TM2PolyTime.lean`) or of `Complexity.TuringMachine` (`Start/UniformTM.lean`).  Those two
models are related to the Cobham terms elsewhere in the library, and nothing here depends on the
choice.

## Gates

Both modules are imported by `Start.lean`, registered in `Start/Capstones.lean`, `sorry`-free and
linter-clean.  `#print axioms` on `Krivine.Impl.eval_walkT`, `Krivine.Impl.eval_stepT`,
`Krivine.Impl.stepT_compiles` and `Krivine.Impl.eval_impl_cob_cost` reports only `propext`,
`Classical.choice`, `Quot.sound`.  `lake build` (9116 jobs, no error, no linter warning),
`python3 scripts/goal_state.py validate`, `python3 scripts/check_closure.py` (396 modules) and
`python3 scripts/check_manifest.py` all pass.
