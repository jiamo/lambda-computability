from __future__ import annotations

import unittest
from copy import deepcopy

from scripts import goal_state


def _task(
    task_id: str,
    *,
    milestone: str,
    rank: int,
    status: str = "TODO_READY",
    depends_on: list[str] | None = None,
) -> dict[str, object]:
    return {
        "id": task_id,
        "priority": "P0",
        "status": status,
        "track": "test",
        "title": task_id,
        "milestone": milestone,
        "depends_on": depends_on or [],
        "rank": rank,
        "exit_criteria": [f"Complete {task_id}"],
        "latest_evidence": "",
        "open_boundary": "" if status == "DONE_STRONG" else "Not complete",
        "required_gates": ["test gate"],
    }


def _board(tasks: list[dict[str, object]]) -> dict[str, object]:
    return {
        "version": 2,
        "source_protocol": goal_state.CANONICAL_GOAL_PROTOCOL,
        "active_milestone": "M1",
        "milestone_order": ["M1", "M2"],
        "tasks": tasks,
    }


class GoalStateTests(unittest.TestCase):
    def test_sorted_open_tasks_uses_active_milestone_rank_and_dependencies(self) -> None:
        board = _board(
            [
                _task("M1-BLOCKER", milestone="M1", rank=90),
                _task(
                    "M1-BLOCKED-FIRST",
                    milestone="M1",
                    rank=1,
                    depends_on=["M1-BLOCKER"],
                ),
                _task("M1-READY", milestone="M1", rank=20),
                _task("M2-HIGH-PRIORITY", milestone="M2", rank=0),
            ]
        )

        self.assertEqual(goal_state.validate(board), [])
        self.assertEqual(
            [task["id"] for task in goal_state.sorted_open_tasks(board)],
            ["M1-READY", "M1-BLOCKER"],
        )

        completed = deepcopy(board)
        completed["tasks"][0]["status"] = "DONE_STRONG"
        completed["tasks"][0]["open_boundary"] = ""
        self.assertEqual(
            [task["id"] for task in goal_state.sorted_open_tasks(completed)],
            ["M1-BLOCKED-FIRST", "M1-READY"],
        )

    def test_validate_rejects_unknown_later_and_cyclic_dependencies(self) -> None:
        board = _board(
            [
                _task("M1-A", milestone="M1", rank=1, depends_on=["M1-B"]),
                _task("M1-B", milestone="M1", rank=2, depends_on=["M1-A"]),
                _task("M1-LATER", milestone="M1", rank=3, depends_on=["M2-TASK"]),
                _task("M1-UNKNOWN", milestone="M1", rank=4, depends_on=["MISSING"]),
                _task("M2-TASK", milestone="M2", rank=1),
            ]
        )

        errors = goal_state.validate(board)

        self.assertIn(
            "M1-LATER: dependency 'M2-TASK' belongs to later milestone M2",
            errors,
        )
        self.assertIn("M1-UNKNOWN: unknown dependency 'MISSING'", errors)
        self.assertTrue(any(error.startswith("dependency cycle: ") for error in errors))

    def test_validate_requires_version_2_execution_fields(self) -> None:
        task = _task("M1-TASK", milestone="M1", rank=1)
        del task["exit_criteria"]

        errors = goal_state.validate(_board([task]))

        self.assertIn(
            "M1-TASK: missing version 2 fields: exit_criteria",
            errors,
        )

    def test_validate_requires_traceable_baseline_evidence_for_ready_performance_rows(
        self,
    ) -> None:
        task = _task("PERF-M1-READY", milestone="M1", rank=1)
        task["track"] = "performance/runtime"
        task["scope_limit"] = "One finite runtime shape."
        task["baseline_metric"] = "Recorded wall time and peak RSS."
        task["success_threshold"] = "Beat the recorded baseline without higher RSS."
        task["failure_disposition"] = "Remove the experiment and record rejection evidence."

        errors = goal_state.validate(_board([task]))
        self.assertIn(
            "PERF-M1-READY: execution-ready performance task missing baseline_evidence",
            errors,
        )

        task["baseline_evidence"] = "docs/goal/does-not-exist.md"
        errors = goal_state.validate(_board([task]))
        self.assertIn(
            "PERF-M1-READY: baseline_evidence missing: docs/goal/does-not-exist.md",
            errors,
        )

        task["baseline_evidence"] = "docs/goal/task-board.yaml"
        self.assertEqual(goal_state.validate(_board([task])), [])


if __name__ == "__main__":
    unittest.main()
