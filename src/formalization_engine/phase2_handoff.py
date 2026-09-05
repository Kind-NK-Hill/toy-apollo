"""Machine-readable handoffs without changing legacy two-value results."""

from __future__ import annotations

import json
from typing import Any, Literal


NextAction = Literal[
    "author_repair",
    "reviewer_write_result",
    "diagnoser_read_only",
    "resolve_blocker",
    "completed",
    "stopped",
]


class ReviewLoopOutcome(tuple):
    """A legacy ``(success, detail)`` pair with explicit orchestration fields.

    ``success`` retains its operation-level meaning; it is not a completion
    verdict. Only ``is_terminal`` decides whether this repair workflow has
    ended. A diagnostic handoff remains nonterminal even though the legacy
    loop ledger records ``stopped / diagnoser_required``.
    """

    def __new__(
        cls,
        success: bool,
        detail: str,
        *,
        next_action: NextAction,
        stop_reason: str = "",
        request_path: str = "",
        expected_result_path: str = "",
    ) -> ReviewLoopOutcome:
        result = super().__new__(cls, (success, detail))
        result.next_action = next_action
        result.stop_reason = stop_reason
        result.request_path = request_path
        result.expected_result_path = expected_result_path
        return result

    @property
    def success(self) -> bool:
        return self[0]

    @property
    def detail(self) -> str:
        return self[1]

    @property
    def is_terminal(self) -> bool:
        return self.next_action in {"completed", "stopped"}

    @property
    def status(self) -> str:
        if self.is_terminal:
            return self.next_action
        return "blocked" if self.next_action == "resolve_blocker" else "handoff"

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "success": self.success,
            "detail": self.detail,
            "status": self.status,
            "next_action": self.next_action,
            "is_terminal": self.is_terminal,
            "stop_reason": self.stop_reason,
            "request_path": self.request_path,
            "expected_result_path": self.expected_result_path,
        }


def render_handoff_line(task_id: str, outcome: ReviewLoopOutcome) -> str:
    """One JSON record after the existing human-readable CLI output."""
    return "PHASE2_HANDOFF_JSON=" + json.dumps(
        {"task_id": task_id, **outcome.to_dict()}, ensure_ascii=True, sort_keys=True
    )
