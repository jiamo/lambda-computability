# M21-COBHAM-TO-SPACE — Cobham terms run in polynomial space: P ⊆ PSPACE

**Status:** DONE_STRONG

The library measures time on Cobham's function algebra (`Complexity.InP L` :
`∃ c : Cob, ∀ x, L x ↔ c.eval [x] ≠ []`) and space on the offline machine of
`Start/SpaceMachine.lean` (`Complexity.Space.PSPACE`).  The inclusion P ⊆ PSPACE therefore needs a
compiler from Cobham terms into space-bounded offline machines.  This task builds it, and builds it
on a reusable combinator layer for tape programs so that later tape-program tasks
(`M14-QBF-STEP-PROG`, the deterministic parts of `M22-NONDET-PROG`, the oracle version needed by
`M15-ORACLE-PROG`) do not start from raw configurations.

## Terminal statement

```lean
theorem Complexity.Space.pspace_of_inP {L : Language} (hL : Complexity.InP L) :
    Complexity.Space.PSPACE L
```

(`Start/CobhamPspace.lean`; `#print axioms` gives `propext, Classical.choice, Quot.sound`.)

## The layers

### 1. Exact-state specifications — `Start/SpaceProgLib.lean`

* `Complexity.Space.TState`, `Complexity.Space.Config.abs` — the observable state of a
  configuration: the work tape as a function `ℕ → Bool`, the work head, the input head.  The tape
  as a growing list never appears in client proofs.
* `Complexity.Space.Prog.Runs x B p s s'` — from every configuration with observable state `s`
  within `B` cells, `p` executes to one with observable state `s'`, every configuration on the way
  within `B` cells.
* Composition: `Runs.seq`, `Runs.of_eq`, `Runs.act`, `Runs.iteT`, `Runs.iteF`, `Runs.ite`, and
  `Runs.loop_stages` (a while loop through a numbered family of stages, the test failing exactly at
  the last one — the loop rule every client uses).
* Head movement by constants: `Prog.mvR`, `Prog.mvL`, `Prog.moveTo`.
* Tracks: `Complexity.Space.Tracks.mk`, `Tracks.lay K R` — a register file `R : ℕ → Word` laid out
  in `K` tracks of blocks of `2K + 1` cells (a ruler cell, then presence/value bits per track).

### 2. Register primitives — `Start/SpaceProgTracks.lean`

Each primitive has a specification of the form
`Runs x B prog ⟨lay K R, 0, i⟩ ⟨lay K R', 0, i⟩` under the single space hypothesis
`(N + 3) · (2K + 1) ≤ B` for register lengths `≤ N`:

`goHome`, `clear`, `copyOff`/`runs_copy`, `assign`, `seekEnd`, `append`, `popBranch` (remove the
last bit and branch on it), `truncate`, `prepend`, `whileNE` (loop while a register is non-empty,
through stages of register files), `copyInput` (copy the input into a register).

### 3. From a specification to a space class — `Start/SpaceProgDecide.lean`

* `Complexity.Space.Prog.decider p` — `p`, then accept if the bit under the head is set.
* `Complexity.Space.Prog.dspace_of_runs`, `.pspace_of_runs` — if `p` runs on every input `x` from
  the blank tape within `B x ≤ s |x|` cells to a state whose scanned bit says `x ∈ L`, then
  `L ∈ DSPACE s` (resp. `PSPACE` for polynomial `s`).  The run-level argument (determinism, every
  reachable configuration within the bound) is done once, through `Complexity.Space.Realizes`.

### 4. The compiler — `Start/CobhamSpace.lean`

* `Complexity.Cob.spaceW c N` — a bound, polynomial in `N` (`Cob.spaceW_polyBound`), on the
  length of every word handled while evaluating `c` on arguments of length `≤ N`
  (`Cob.eval_length_le`).
* `Complexity.Cob.need c` — the number of scratch registers the compiled program uses.
* `Complexity.Space.compile K c as d fr` — projections/constants are copies, `app` a prepend,
  `smash` two nested counting loops, composition evaluates the arguments into fresh registers,
  bounded recursion runs over the recursion word from its end (registers: the remaining prefix,
  the suffix read so far, the value on it, the step result, the bound).
* `Complexity.Space.compileOK` — **correctness**: for every term `c`, on registers of length
  `≤ N` with the scratch registers empty, the program sets register `d` to `c.eval (as.map R)`,
  leaves every other register unchanged, and stays within `(Cob.spaceW c N + 3) · (2K + 1)` cells.

### 5. The decider — `Start/CobhamPspace.lean`

`Complexity.Space.cobDecider c` sets the ruler, copies the input into register 0, runs the
compiled term into register 1 and moves to the presence bit of its first cell
(`Complexity.Space.runs_cobDecider`); `pspace_of_runs` with the bound
`(Cob.spaceW c n + 3) · (2 (Cob.need c + 2) + 1)` gives `pspace_of_inP`.

## Gates

* `lake build Start Start.Capstones` — passes; the new modules build without warnings.
* `python3 scripts/check_sorry.py`, `python3 scripts/check_closure.py`,
  `python3 scripts/goal_state.py validate` — pass.
* Registered in `Start/Capstones.lean`: `Prog.Runs`, `Prog.Runs.loop_stages`,
  `Tracks.runs_whileNE`, `Prog.dspace_of_runs`, `compileOK`, `runs_cobDecider`, `pspace_of_inP`.

## What this unblocks, and what it does not

* `M21-IP-SUBSET-PSPACE` — no longer blocked on the model gap; still needs the recursion over
  transcripts as a tape program.
* `M15-ORACLE-CLASSES` (NP^A ⊆ PSPACE^A) is **not** closed by this task alone: the relativized
  classes use a different machine (`Complexity.Space.OMachine`, with a query tape), and the
  tape-program language and its compiler exist only for the oracle-free machine.  What is missing
  is named as `M15-ORACLE-PROG`: tape programs with query-tape instructions compiled into
  `OMachine`, the compiler of this task extended by the `query` constructor of `CobQ`, and a loop
  enumerating all witnesses of polynomially bounded length.  The combinator layer above is
  written against the observable state and carries over verbatim once that machine layer exists.
* `M14-QBF-STEP-PROG` — can now be written with the register primitives (the QBF evaluator state
  in registers, one step as a composition of `popBranch`, `append`, `assign`, `whileNE`).
* `M22-NONDET-PROG` — needs a new constructor of `Prog` and a new compiler; the deterministic
  combinators apply unchanged to the deterministic parts of nondeterministic programs.
