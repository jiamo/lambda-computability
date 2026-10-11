# AGENTS.md

This file is for humans and coding agents working in this repository.

## Startup Route

1. Read `docs/goal/goal-prompt.md` for the execution protocol.
2. Read `docs/current-goal-state.md` for the active summarized task state.
3. Inspect `docs/goal/task-board.yaml` through `python3 scripts/goal_state.py next`
   before choosing follow-up work.
4. Validate task-board edits with `python3 scripts/goal_state.py validate`.

## Delivery Rule

A delivery is produced by exactly one command, run from the repository root:

```bash
scripts/pack_gate.sh HEAD && git archive --format=tar.gz HEAD -o delivery.tar.gz
```

Both halves name the same tree, `HEAD`: the gates run on what `git archive HEAD` ships, and the
archive is only written if they pass.  Do not package any other way (no `tar` of the working
tree, no archive of a different revision), and do not report the gates as run on a tree other
than the one delivered: an earlier delivery listed `check_manifest.py` as passed while the
shipped archive failed it, because the gated tree and the packed tree were not the same.  Commit
first — uncommitted work is not in `HEAD` and is not delivered.  `pack_gate.sh` is also the only
thing that catches a `lake-manifest.json` disagreeing with `lakefile.toml`.  Run
`scripts/install_hooks.sh` once per clone so that `.githooks/pre-commit` calls the gate on every
commit; see `docs/RELEASING.md`.  `lake build --wfail` must pass before packaging, because that
is what CI builds.

## Task Board Rule

`docs/goal/task-board.yaml` is the machine-readable task queue for this
repository.

- New actionable work should be normalized into the task board instead of being
  left only in chat.
- `DONE_STRONG` means the listed gates prove the exact claim and the
  `open_boundary` is empty.
- `DONE_WEAK` remains unfinished.  It is nevertheless an acceptable *delivery* when, and only
  when, the gap that keeps the task from `DONE_STRONG` has been identified, named precisely (the
  missing lemma or construction), and opened as a new task at the head of the queue that the
  weak task depends on.  Reporting `DONE_WEAK` in that way is the correct outcome; claiming
  `DONE_STRONG` for a task whose `open_boundary` is not empty is not.

## Commands

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render --write docs/current-goal-state.md
```
