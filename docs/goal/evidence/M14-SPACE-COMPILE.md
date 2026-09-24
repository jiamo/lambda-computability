# M14-SPACE-COMPILE — a bounded-memory abstract machine realized by an offline machine

**Status:** DONE_STRONG (for the exit criteria of this task; see "What this does not do")

Three open tasks — `M14-TQBF-IN-PSPACE`, `M14-KRIVINE-SPACE-CLASS` and, in the converse
direction, `M14-SPACE-REASONABLE` — were blocked on the same missing piece: a special-purpose
abstract machine with its own memory bound (the QBF evaluator, `2n² + 3n` bits; the Krivine
machine with a shared heap, `O(s log s)`) had to be implemented as a machine of
`Start/SpaceMachine.lean`.  This task builds that bridge once, in the pattern of
`Start/Rewriting.lean` (one interface, one bridge lemma per client) and
`Start/DescriptionSystem.lean`.

## The split into two halves

Simulating an abstract machine on an offline machine has two halves of different nature.

* **Run level** — given that each abstract step is carried out by a stretch of the offline
  machine, the offline machine accepts exactly what the abstract machine accepts, and *every*
  configuration it reaches (including every intermediate configuration of every simulated step)
  fits in the bound.  This is the same argument every time; it is proved once here.
* **Step level** — one abstract step has to be performed by the finite control of an offline
  machine on the binary encoding of the abstract state.  This cannot be proved once and for all:
  the finite control of an offline machine cannot compute an arbitrary transition function.
  So a general compiler that takes *only* "a state type, a transition function, an encoding and a
  memory bound" and returns a machine cannot exist.  What can be done once is to make the step
  level *writable*: a structured language of tape programs with a verified compiler.  That is the
  second half of this task.

## What is proved

`Start/SpaceCompile.lean` — the run level:

* `Complexity.Space.AbsMachine` (with `.Reaches`, `.Accepts`) — a deterministic abstract machine
  on binary inputs, states of an arbitrary type.
* `Complexity.Space.Machine.Path`, `Complexity.Space.Machine.Seg` — runs with a side condition;
  a segment is at least one step with every intermediate configuration within `B` cells and
  non-accepting.  Composition lemmas `Path.trans`, `Seg.trans`, `Seg.single`, `Seg.mono`.
* `Complexity.Space.Realizes M A code B` — **the single bridge statement**: the initial abstract
  state is encoded by the initial configuration; encodings of reachable states respect acceptance
  and the bound; halting states are encoded by halting configurations; each step `s ↦ s'` from a
  reachable state is a segment from `code s` to `code s'`.
* `Complexity.Space.Machine.steps_det` — determinism of runs.
* `Complexity.Space.Realizes.onRun` — every reachable configuration is an encoding of a reachable
  abstract state or a quiet configuration inside a segment.
* `Complexity.Space.Realizes.accepts_iff`, `.spaceBoundedOn`, `.dspace`, `.pspace` — acceptance,
  the bound on every reachable configuration, `DSPACE s`, `PSPACE`.
* `Complexity.Space.realizes_self`, `Complexity.Space.dspace_iff_realizes` — the interface is
  lossless: `DSPACE s L` holds iff `L` is the language of some abstract machine realized within
  `s |x|` by a well-formed deterministic machine.

`Start/SpaceProg.lean` — the step level made writable:

* `Complexity.Space.Prog` — actions (write/move computed from what the heads read), sequencing,
  conditionals and while loops; `Prog.size` its number of control states.
* `Complexity.Space.Prog.Exec` — big-step semantics with a side condition on every configuration
  before the last; `Exec.mono`; `Exec.loop_of_variant`, the while rule with an invariant and a
  decreasing measure.
* `Complexity.Space.Prog.delta`, `Complexity.Space.Prog.machine` — the compiled table; the
  machine of a program has one extra final state, accepting and halting.
* `Complexity.Space.Prog.path_of_exec` — **compiler correctness**: an execution is a run of any
  machine hosting the compiled table, through configurations satisfying the side condition and
  lying in the program's states.
* `Complexity.Space.Prog.machine_wellFormed`, `.machine_deterministic`.
* `Complexity.Space.Prog.loop_seg`, `.loop_exit` — one iteration of a main loop is a segment;
  leaving it reaches the final state.
* `Complexity.Space.Prog.realizes_loop`, `.dspace_loop` — **the loop form of the bridge**: for a
  program `loop t body` the client proves only that `t` fails exactly on halting states and that
  `body` executes each abstract step on the encoding within the bound.

`Start/SpaceProgDemo.lean` — an end-to-end client: `Complexity.Space.Demo.exec_step` is the bridge
lemma for a scanner, and `Complexity.Space.Demo.dspace_hasTrue` puts `{x | true ∈ x}` in
`DSPACE 1` through the compiled machine.  It is small, but it exercises every hypothesis of
`realizes_loop`, so the interface is known to be satisfiable and usable.

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.

## What this does not do

The expectation that `M14-TQBF-IN-PSPACE` and `M14-KRIVINE-SPACE-CLASS` become one-line instances
does not hold, for the reason above: each client still owes its step-level bridge lemma, which
for the QBF evaluator means laying its state (a pointer into the code, the assignment, the stack
of records) out on a binary tape and writing and verifying a tape program for one step.  That gap
is named and opened as the head-of-queue task `M14-QBF-STEP-PROG`; `M14-TQBF-IN-PSPACE` now
depends on it and is, after it, the instance `Complexity.Space.Prog.dspace_loop` with the bound of
`M14-QBF-CODE-SPACE`.  `M14-KRIVINE-SPACE-CLASS` has the same shape (its boundary now names the
Krivine bridge lemma), and `M14-SPACE-REASONABLE` remains the converse compiler, untouched.

## Gates

```
lake build                        # Build completed successfully (9184 jobs), 0 errors
python3 scripts/check_sorry.py    # OK: no sorry/admit in 465 modules
python3 scripts/check_closure.py  # OK: 464 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
python3 scripts/check_manifest.py
scripts/pack_gate.sh HEAD
```
