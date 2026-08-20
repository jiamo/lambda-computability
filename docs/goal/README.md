# Goal Task Workflow

This directory owns the repository's structured task board.

The workflow is agent-neutral. A human, Codex, or another coding agent should
be able to use the same task board, protocol, and shell commands.

Files:

- `docs/goal/goal-prompt.md`: protocol and status definitions
- `docs/goal/task-board.yaml`: machine-readable task queue
- `docs/current-goal-state.md`: generated current summary

Use:

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render --write docs/current-goal-state.md
```

Do not mark a task `DONE_STRONG` unless the listed gates prove the exact claim
and the `open_boundary` is empty.
