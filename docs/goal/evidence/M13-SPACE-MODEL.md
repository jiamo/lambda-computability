# M13-SPACE-MODEL — a machine model for space, and the classes it defines

Polynomial *time* in this library is Cobham's class (`Start/ComplexityClasses.lean`), where
closure under composition is a constructor rather than a theorem.  Space cannot be treated that
way: a space bound is a statement about the storage a computation uses, not about its length, so
it has to be read off a machine.  `Start/SpaceMachine.lean` gives the standard model for sublinear
space.

## The model

* `Complexity.Space.Config` — a configuration: control state, position of the read-only input
  head, contents of the work tape, position of the work head.
* `Complexity.Space.Machine` — the machine: a number of control states (`0` is initial),
  a predicate marking the accepting ones, and a transition function
  `delta q a b : List (ℕ × Bool × Dir × Dir)` returning the instructions available when the input
  head reads `a` (`none` at the end marker) and the work head reads `b`.  The empty list is
  halting, and `Complexity.Space.Machine.Deterministic` — at most one instruction — is a property
  of the same model, not a second model.
* `Complexity.Space.moveIn` clamps the input head to `0, …, |x|`, so the input tape is read-only
  and bounded; `Complexity.Space.writeAt` writes a work cell, extending the used part of the tape
  with blanks when needed (`Complexity.Space.writeAt_length`,
  `Complexity.Space.getD_writeAt_self`).
* `Complexity.Space.Machine.Step`, `.Accepts` — the one-step relation and acceptance by some
  finite run, counted with `Complexity.Reach.steps` of `Start/SavitchReach.lean`.
* `Complexity.Space.Config.space`, `Complexity.Space.Machine.SpaceBounded`,
  `.SpaceBoundedOn` — the used part of the work tape, and the bound on every reachable
  configuration.

## Invariants of a run

* `Complexity.Space.Machine.inHead_le_of_steps` — the input head never leaves the input and its
  end marker.
* `Complexity.Space.Machine.state_lt_of_steps` — a well-formed machine
  (`Complexity.Space.Machine.WellFormed`) never leaves its state set.

These two are what makes the configuration count of `M13-SPACE-CONFIG-COUNT` finite.

## The classes

`Complexity.Space.DSPACE`, `.NSPACE`, `.LOGSPACE`, `.PSPACE`, `.NPSPACE`; the polynomial bound is
the `Complexity.PolyBound` of `Start/ComplexityClasses.lean`, so the two halves of the library
measure polynomials the same way.

* `Complexity.Space.nspace_of_dspace`, `Complexity.Space.npspace_of_pspace` — determinism is a
  special case of nondeterminism.
* `Complexity.Space.DSPACE.mono`, `Complexity.Space.NSPACE.mono` — monotonicity in the bound.
* `Complexity.Space.pspace_of_logspace` — `L ⊆ PSPACE`.
* `Complexity.Space.dspace_const_decidable` — the machine that halts at once puts the two constant
  languages in `DSPACE 1`, so none of the classes is empty.  (One cell is the least a
  configuration can occupy: the work head always stands on some cell.)

## Gates

`lake build`, `python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`.
`#print axioms` on the results above reports only `propext`, `Classical.choice`, `Quot.sound`.
