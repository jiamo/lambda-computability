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

The current task board is for finishing the modular split of the Lean lambda
calculus development:

- close the remaining `sorry` / placeholder gaps in modular files
- switch the canonical entrypoint away from the monolithic `Start.Basic`
- reduce `Start/Basic.lean` to a compatibility layer once extraction is done

Task rows should stay tied to real Lean files and real build gates.
