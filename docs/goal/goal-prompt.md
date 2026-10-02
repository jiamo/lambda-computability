# Goal Protocol

This repository uses one structured task board for follow-up work.

## Task Source of Truth

`docs/goal/task-board.yaml` is the executable task queue.

- Put new actionable work into the task board instead of leaving it only in
  chat.
- Keep tasks finite. Each row should describe one bounded claim or refactor
  step.
- `DONE_WEAK` is still unfinished.
- `DONE_STRONG` means the listed gates prove the exact claim and
  `open_boundary` is empty.
- `DONE_WEAK` is not an acceptable outcome, **except** when the gap is identified, named
  (the missing lemma or construction, stated precisely in `open_boundary`), and opened as a new
  task at the head of the queue on which the weak task depends.  In that case `DONE_WEAK` is the
  correct delivery, and it must not be upgraded to `DONE_STRONG` to satisfy a quota.

## Delivery

Package with exactly

```bash
scripts/pack_gate.sh HEAD && git archive --format=tar.gz HEAD -o delivery.tar.gz
```

so that the tree the gates run on and the tree that is shipped are the same commit.

## Required Commands

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render --write docs/current-goal-state.md
```

## Repository-Specific Scope

The modular split that the first milestones were about is finished: `Start.lean`
is the entrypoint, every module under `Start/` is in its import closure, and the
library is `sorry`-free.  The board is now a research queue for the theory
itself.  Current scope:

- untyped semantics: the residual conditional statements of
  `M9-UNTYPED-FULL-ABSTRACTION` (`ScottDinf.TagBelowSound` is the last one), and
  further models of the untyped calculus
- typed calculi: the open items of `M9-LAMBDAPI-LCCC` (initiality, universes
  closed under the pushforward product), and eta for `λΠ`
- complexity and algorithmic information theory: reasonable cost models, the
  hard half of Kolmogorov–Levin, further NP-complete languages and reductions
- consolidation: replacing families of near-duplicate modules by a single
  general interface, where doing so makes the library smaller

Current queue (in order; ranks on the board follow it):

1. `M14-SPACE-COMPILE` — the general bridge from a bounded-memory abstract machine to an offline
   machine of `Start/SpaceMachine.lean` (done: `Start/SpaceCompile.lean`, `Start/SpaceProg.lean`).
2. `M14-QBF-STEP-PROG` — the one bridge lemma the QBF evaluator owes: a tape program for one
   step of `Start/Qbf.lean` on a binary encoding of its state (named gap of 1 → 3).
3. `M14-TQBF-IN-PSPACE` — the instance of 1 with 2; then `Complexity.Qbf.pspaceComplete_TQBF`.
4. `M14-TQBF-PSPACE-HARD` — closed from `DONE_WEAK` by 3.
5. `M15-BGS-EQUAL` — unlocked by 4.
6. `M15-NO-RELATIVIZING-PROOF` — closed by 5; the relativization barrier complete.
7. `M14-KRIVINE-SPACE-CLASS` — the same kind of instance of 1 (its bridge lemma: a tape program
   for one pass of the binary Krivine implementation); then `M14-SPACE-REASONABLE`, the converse.
8. `M16-FRIEDBERG-MUCHNIK`
9. `M19-SYMMETRY-HARD-HALF`
10. `M20-GANDY`

Two mechanical gates back this up and must keep passing:
`python3 scripts/check_closure.py` (every module is in the import closure of
`Start.lean` and every terminal statement is registered in
`Start/Capstones.lean`) and `python3 scripts/goal_state.py validate`.

Task rows should stay tied to real Lean files and real build gates.
