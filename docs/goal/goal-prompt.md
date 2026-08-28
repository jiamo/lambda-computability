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

Two mechanical gates back this up and must keep passing:
`python3 scripts/check_closure.py` (every module is in the import closure of
`Start.lean` and every terminal statement is registered in
`Start/Capstones.lean`) and `python3 scripts/goal_state.py validate`.

Task rows should stay tied to real Lean files and real build gates.
