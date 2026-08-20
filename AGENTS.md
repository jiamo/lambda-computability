# AGENTS.md

This file is for humans and coding agents working in this repository.

## Startup Route

1. Read `docs/goal/goal-prompt.md` for the execution protocol.
2. Read `docs/current-goal-state.md` for the active summarized task state.
3. Inspect `docs/goal/task-board.yaml` through `python3 scripts/goal_state.py next`
   before choosing follow-up work.
4. Validate task-board edits with `python3 scripts/goal_state.py validate`.

## Task Board Rule

`docs/goal/task-board.yaml` is the machine-readable task queue for this
repository.

- New actionable work should be normalized into the task board instead of being
  left only in chat.
- `DONE_STRONG` means the listed gates prove the exact claim and the
  `open_boundary` is empty.
- `DONE_WEAK` remains unfinished.

## Commands

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render --write docs/current-goal-state.md
```
