#!/usr/bin/env python3
"""Small helper for the structured goal task board.

The parser intentionally supports only the narrow YAML subset used by
docs/goal/task-board.yaml so the workflow has no PyYAML dependency.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
TASK_BOARD = ROOT / "docs" / "goal" / "task-board.yaml"
CANONICAL_GOAL_PROTOCOL = "docs/goal/goal-prompt.md"

VALID_PRIORITIES = {"P0": 0, "P1": 1, "P2": 2, "P3": 3}
VALID_STATUSES = {
    "DISCOVERED",
    "TODO_READY",
    "TODO_NEEDS_DESIGN",
    "CLAIM_RISK",
    "IN_PROGRESS",
    "BLOCKED",
    "TESTING",
    "DONE_WEAK",
    "BACKEND_PARTIAL",
    "DONE_STRONG",
}

REQUIRED_V2_TASK_FIELDS = {
    "milestone",
    "depends_on",
    "rank",
    "exit_criteria",
}

MAX_OPEN_BOUNDARY_CHARS = 2000
MAX_TASK_EXPANSION_LIMIT = 6
REQUIRED_OPEN_PERFORMANCE_FIELDS = {
    "scope_limit",
    "baseline_metric",
    "success_threshold",
    "failure_disposition",
}
PERFORMANCE_EXECUTION_STATUSES = VALID_STATUSES - {
    "DISCOVERED",
    "TODO_NEEDS_DESIGN",
    "DONE_STRONG",
}


def _parse_scalar(raw: str) -> Any:
    raw = raw.strip()
    if raw == "":
        return ""
    if raw in {"[]", "{}"}:
        return [] if raw == "[]" else {}
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return raw


def load_task_board(path: Path = TASK_BOARD) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(path)
    data: dict[str, Any] = {"tasks": []}
    current: dict[str, Any] | None = None
    current_list_key: str | None = None

    for line_no, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw_line.rstrip()
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        indent = len(line) - len(line.lstrip(" "))

        if stripped.startswith("- id:"):
            current = {"id": _parse_scalar(stripped[len("- id:") :])}
            data["tasks"].append(current)
            current_list_key = None
            continue

        if current is not None and indent >= 4:
            if stripped.startswith("- "):
                if current_list_key is None:
                    raise ValueError(f"{path}:{line_no}: list item without list key")
                current[current_list_key].append(_parse_scalar(stripped[2:]))
                continue
            if ":" not in stripped:
                raise ValueError(f"{path}:{line_no}: expected key: value")
            key, value = stripped.split(":", 1)
            key = key.strip()
            value = value.strip()
            if value == "":
                current[key] = []
                current_list_key = key
            else:
                current[key] = _parse_scalar(value)
                current_list_key = None
            continue

        if ":" not in stripped:
            raise ValueError(f"{path}:{line_no}: expected top-level key: value")
        key, value = stripped.split(":", 1)
        key = key.strip()
        value = value.strip()
        if key == "tasks" and value == "":
            data["tasks"] = []
        else:
            data[key] = _parse_scalar(value)

    return data


def validate(board: dict[str, Any], root: Path = ROOT) -> list[str]:
    errors: list[str] = []
    seen: set[str] = set()
    tasks = board.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        return ["task board has no tasks"]

    version = board.get("version", 1)
    milestone_order = board.get("milestone_order", [])
    active_milestone = board.get("active_milestone", "")
    milestone_indexes: dict[str, int] = {}
    if version >= 2:
        if board.get("source_protocol") != CANONICAL_GOAL_PROTOCOL:
            errors.append(
                "version 2 board source_protocol must be "
                + CANONICAL_GOAL_PROTOCOL
            )
        if (
            not isinstance(milestone_order, list)
            or not milestone_order
            or not all(isinstance(value, str) and value for value in milestone_order)
        ):
            errors.append("version 2 board requires a non-empty milestone_order list")
        elif len(set(milestone_order)) != len(milestone_order):
            errors.append("milestone_order contains duplicates")
        else:
            milestone_indexes = {
                milestone: index for index, milestone in enumerate(milestone_order)
            }
        if not isinstance(active_milestone, str) or not active_milestone:
            errors.append("version 2 board requires active_milestone")
        elif milestone_indexes and active_milestone not in milestone_indexes:
            errors.append(f"unknown active_milestone {active_milestone!r}")

    for index, task in enumerate(tasks, 1):
        task_id = task.get("id")
        if not isinstance(task_id, str) or not task_id:
            errors.append(f"task #{index}: missing id")
            continue
        if task_id in seen:
            errors.append(f"{task_id}: duplicate id")
        seen.add(task_id)

        priority = task.get("priority")
        if priority not in VALID_PRIORITIES:
            errors.append(f"{task_id}: invalid priority {priority!r}")

        status = task.get("status")
        if status not in VALID_STATUSES:
            errors.append(f"{task_id}: invalid status {status!r}")

        gates = task.get("required_gates")
        if not isinstance(gates, list):
            errors.append(f"{task_id}: required_gates must be a list")

        evidence = task.get("latest_evidence", "")
        if evidence:
            evidence_path = root / str(evidence)
            if not evidence_path.exists():
                errors.append(f"{task_id}: latest_evidence missing: {evidence}")

        open_boundary = task.get("open_boundary", "")
        if status == "DONE_STRONG" and open_boundary:
            errors.append(f"{task_id}: DONE_STRONG must have empty open_boundary")
        if (
            isinstance(open_boundary, str)
            and len(open_boundary) > MAX_OPEN_BOUNDARY_CHARS
        ):
            errors.append(
                f"{task_id}: open_boundary exceeds "
                f"{MAX_OPEN_BOUNDARY_CHARS} characters"
            )

        track = task.get("track", "")
        is_open_performance = (
            status != "DONE_STRONG"
            and isinstance(track, str)
            and track.startswith("performance/")
        )
        if is_open_performance:
            scope_limit = task.get("scope_limit")
            if not isinstance(scope_limit, str) or not scope_limit.strip():
                errors.append(
                    f"{task_id}: unfinished performance task missing scope_limit"
                )
        if is_open_performance and status in PERFORMANCE_EXECUTION_STATUSES:
            for field in sorted(REQUIRED_OPEN_PERFORMANCE_FIELDS - {"scope_limit"}):
                value = task.get(field)
                if not isinstance(value, str) or not value.strip():
                    errors.append(
                        f"{task_id}: execution-ready performance task missing {field}"
                    )
            baseline_evidence = task.get("baseline_evidence")
            if not isinstance(baseline_evidence, str) or not baseline_evidence.strip():
                errors.append(
                    f"{task_id}: execution-ready performance task missing "
                    "baseline_evidence"
                )
            elif not (root / baseline_evidence).exists():
                errors.append(
                    f"{task_id}: baseline_evidence missing: {baseline_evidence}"
                )

        if task.get("produces_tasks") is True:
            expansion_limit = task.get("task_expansion_limit")
            if (
                not isinstance(expansion_limit, int)
                or isinstance(expansion_limit, bool)
                or expansion_limit < 1
                or expansion_limit > MAX_TASK_EXPANSION_LIMIT
            ):
                errors.append(
                    f"{task_id}: produces_tasks requires a positive "
                    "task_expansion_limit no greater than "
                    f"{MAX_TASK_EXPANSION_LIMIT}"
                )

        if version >= 2:
            missing = sorted(REQUIRED_V2_TASK_FIELDS - task.keys())
            if missing:
                errors.append(f"{task_id}: missing version 2 fields: {', '.join(missing)}")

            milestone = task.get("milestone")
            if milestone_indexes and milestone not in milestone_indexes:
                errors.append(f"{task_id}: unknown milestone {milestone!r}")

            dependencies = task.get("depends_on")
            if not isinstance(dependencies, list) or not all(
                isinstance(dependency, str) and dependency for dependency in dependencies
            ):
                errors.append(f"{task_id}: depends_on must be a list of task ids")

            rank = task.get("rank")
            if not isinstance(rank, int) or isinstance(rank, bool) or rank < 0:
                errors.append(f"{task_id}: rank must be a non-negative integer")

            exit_criteria = task.get("exit_criteria")
            if not isinstance(exit_criteria, list) or not exit_criteria or not all(
                isinstance(criterion, str) and criterion for criterion in exit_criteria
            ):
                errors.append(f"{task_id}: exit_criteria must be a non-empty list")

    if version >= 2:
        task_by_id = {
            task.get("id"): task
            for task in tasks
            if isinstance(task.get("id"), str) and task.get("id")
        }
        for task_id, task in task_by_id.items():
            dependencies = task.get("depends_on")
            if not isinstance(dependencies, list):
                continue
            for dependency in dependencies:
                if dependency not in task_by_id:
                    errors.append(f"{task_id}: unknown dependency {dependency!r}")
                    continue
                if dependency == task_id:
                    errors.append(f"{task_id}: task cannot depend on itself")
                    continue
                task_milestone = task.get("milestone")
                dependency_milestone = task_by_id[dependency].get("milestone")
                if (
                    task_milestone in milestone_indexes
                    and dependency_milestone in milestone_indexes
                    and milestone_indexes[dependency_milestone]
                    > milestone_indexes[task_milestone]
                ):
                    errors.append(
                        f"{task_id}: dependency {dependency!r} belongs to later "
                        f"milestone {dependency_milestone}"
                    )

        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(task_id: str, path: list[str]) -> None:
            if task_id in visited:
                return
            if task_id in visiting:
                cycle_start = path.index(task_id)
                cycle = path[cycle_start:] + [task_id]
                errors.append(f"dependency cycle: {' -> '.join(cycle)}")
                return
            visiting.add(task_id)
            path.append(task_id)
            dependencies = task_by_id[task_id].get("depends_on")
            if isinstance(dependencies, list):
                for dependency in dependencies:
                    if dependency in task_by_id:
                        visit(dependency, path)
            path.pop()
            visiting.remove(task_id)
            visited.add(task_id)

        for task_id in task_by_id:
            visit(task_id, [])

    return errors


def sorted_open_tasks(
    board: dict[str, Any], *, active_only: bool = True
) -> list[dict[str, Any]]:
    tasks = board["tasks"]
    task_by_id = {task["id"]: task for task in tasks}
    active_milestone = board.get("active_milestone")
    indexed = list(enumerate(tasks))
    indexed.sort(
        key=lambda item: (
            item[1].get("rank", item[0]),
            VALID_PRIORITIES.get(item[1].get("priority"), 99),
            item[1].get("id", ""),
        )
    )
    open_tasks: list[dict[str, Any]] = []
    for _, task in indexed:
        if task.get("status") == "DONE_STRONG":
            continue
        if active_only and active_milestone and task.get("milestone") != active_milestone:
            continue
        dependencies = task.get("depends_on", [])
        if any(
            task_by_id[dependency].get("status") != "DONE_STRONG"
            for dependency in dependencies
        ):
            continue
        open_tasks.append(task)
    return open_tasks


def blocked_open_tasks(board: dict[str, Any]) -> list[tuple[dict[str, Any], list[str]]]:
    tasks = board["tasks"]
    task_by_id = {task["id"]: task for task in tasks}
    active_milestone = board.get("active_milestone")
    blocked: list[tuple[dict[str, Any], list[str]]] = []
    for task in tasks:
        if task.get("status") == "DONE_STRONG":
            continue
        if active_milestone and task.get("milestone") != active_milestone:
            continue
        unmet = [
            dependency
            for dependency in task.get("depends_on", [])
            if task_by_id[dependency].get("status") != "DONE_STRONG"
        ]
        if unmet:
            blocked.append((task, unmet))
    blocked.sort(key=lambda item: (item[0].get("rank", 0), item[0]["id"]))
    return blocked


def render_markdown(board: dict[str, Any]) -> str:
    lines = [
        "# Current goal state",
        "",
        f"- Active milestone: `{board.get('active_milestone', '')}`",
        "",
        "| Rank | ID | Priority | Status | Depends on | Evidence | Open Boundary |",
        "|---:|---|---|---|---|---|---|",
    ]
    for task in board["tasks"]:
        dependencies = ", ".join(task.get("depends_on", [])) or "-"
        evidence = task.get("latest_evidence") or "-"
        boundary = task.get("open_boundary") or ""
        lines.append(
            "| {rank} | `{id}` | `{priority}` | `{status}` | {deps} | {evidence} | {boundary} |".format(
                rank=task.get("rank", ""),
                id=task.get("id", ""),
                priority=task.get("priority", ""),
                status=task.get("status", ""),
                deps=dependencies,
                evidence=evidence,
                boundary=str(boundary).replace("|", "\\|"),
            )
        )
    lines.append("")
    open_tasks = sorted_open_tasks(board)
    if open_tasks:
        next_task = open_tasks[0]
        lines.append(f"Next: `{next_task['id']}`")
        lines.append("")
        lines.append(f"- Title: {next_task.get('title', '')}")
        lines.append(f"- Status: `{next_task.get('status', '')}`")
        lines.append(f"- Open boundary: {next_task.get('open_boundary', '')}")
    else:
        lines.append("Next: all tasks in the active milestone are `DONE_STRONG`.")
    lines.append("")
    return "\n".join(lines)


def command_next(args: argparse.Namespace) -> int:
    board = load_task_board(Path(args.board))
    errors = validate(board)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 2
    open_tasks = sorted_open_tasks(board)
    if not open_tasks:
        active_milestone = board.get("active_milestone")
        blocked_tasks = blocked_open_tasks(board)
        if blocked_tasks:
            print(f"No dependency-ready tasks in active milestone {active_milestone}.")
            for task, dependencies in blocked_tasks:
                print(f"blocked: {task['id']} <- {', '.join(dependencies)}")
            return 3
        if active_milestone:
            print(f"Active milestone {active_milestone} is DONE_STRONG.")
        else:
            print("All migrated task-board rows are DONE_STRONG.")
        return 0
    task = open_tasks[0]
    print(f"id: {task['id']}")
    if task.get("milestone"):
        print(f"milestone: {task['milestone']}")
    if "rank" in task:
        print(f"rank: {task['rank']}")
    print(f"priority: {task['priority']}")
    print(f"status: {task['status']}")
    print(f"title: {task.get('title', '')}")
    if task.get("latest_evidence"):
        print(f"latest_evidence: {task['latest_evidence']}")
    if task.get("open_boundary"):
        print(f"open_boundary: {task['open_boundary']}")
    dependencies = task.get("depends_on") or []
    if dependencies:
        print("depends_on:")
        for dependency in dependencies:
            print(f"  - {dependency}")
    exit_criteria = task.get("exit_criteria") or []
    if exit_criteria:
        print("exit_criteria:")
        for criterion in exit_criteria:
            print(f"  - {criterion}")
    gates = task.get("required_gates") or []
    if gates:
        print("required_gates:")
        for gate in gates:
            print(f"  - {gate}")
    return 0


def command_validate(args: argparse.Namespace) -> int:
    board = load_task_board(Path(args.board))
    errors = validate(board)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 2
    print(f"OK: {len(board['tasks'])} tasks validated")
    return 0


def command_render(args: argparse.Namespace) -> int:
    board = load_task_board(Path(args.board))
    errors = validate(board)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 2
    rendered = render_markdown(board)
    if args.write:
        out = Path(args.write)
        out.write_text(rendered, encoding="utf-8")
        print(f"wrote {out}")
    else:
        print(rendered, end="")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--board", default=str(TASK_BOARD), help="task-board.yaml path")
    sub = parser.add_subparsers(dest="command", required=True)

    next_parser = sub.add_parser("next", help="print the next task")
    next_parser.set_defaults(func=command_next)

    validate_parser = sub.add_parser("validate", help="validate task-board shape")
    validate_parser.set_defaults(func=command_validate)

    render_parser = sub.add_parser("render", help="render a markdown task-board summary")
    render_parser.add_argument("--write", help="optional output path")
    render_parser.set_defaults(func=command_render)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
