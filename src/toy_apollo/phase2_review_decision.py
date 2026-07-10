from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .phase2_semantic_review import normalize_reviewer_result
from .phase2_task_status import Phase2TaskStatusClassification, classify_phase2_task_status


_REVIEWER_STATUS_AUTHORITY_FIELDS = {
    "phase2_status",
    "phase2_status_reason",
    "phase2_status_evidence_type",
    "phase2_task_status",
    "phase2_task_status_reason",
    "phase2_task_status_evidence_type",
    "phase2_task_role",
    "phase2_proof_class",
    "phase2_completion_class",
    "phase2_needs_class_normalization",
    "phase2_review_verdict",
    "task_status",
    "task_status_reason",
    "task_status_evidence_type",
    "task_role",
}


@dataclass(frozen=True)
class SemanticReviewDecision:
    result: dict[str, Any]
    task_status_projection: Phase2TaskStatusClassification | None

    @property
    def is_semantic_verdict(self) -> bool:
        return str(self.result.get("cache_class", "") or "").strip().lower() == "semantic_verdict"

    @property
    def is_clean_pass(self) -> bool:
        return bool(
            self.is_semantic_verdict
            and self.task_status_projection is not None
            and self.task_status_projection.task_status == "pass"
        )


def project_normalized_semantic_review_result(
    normalized_result: dict[str, Any],
    *,
    task: dict[str, Any],
) -> SemanticReviewDecision:
    """Attach the authoritative task-status projection to a normalized review.

    Reviewer-supplied status fields are never authoritative. Invalid/operational
    results have those fields removed and receive no task-level projection.
    """

    result = dict(normalized_result)
    for field in _REVIEWER_STATUS_AUTHORITY_FIELDS:
        result.pop(field, None)

    if str(result.get("cache_class", "") or "").strip().lower() != "semantic_verdict":
        return SemanticReviewDecision(result=result, task_status_projection=None)

    task_payload = task if isinstance(task, dict) else {}
    projection = classify_phase2_task_status(
        task_id=str(task_payload.get("block_id", "") or result.get("task_id", "") or ""),
        task_type=str(task_payload.get("type", "") or ""),
        review_verdict=str(result.get("verdict", "") or ""),
        proof_class=result.get("proof_class", ""),
        completion_class=result.get("completion_class", ""),
    )
    result.update(projection.as_metadata())
    result.update(
        {
            "phase2_review_verdict": projection.review_verdict,
            "phase2_completion_class": str(result.get("completion_class", "") or ""),
            "task_status": projection.task_status,
            "task_status_reason": projection.reason,
            "task_status_evidence_type": projection.evidence_type,
            "task_role": projection.task_role,
        }
    )
    return SemanticReviewDecision(result=result, task_status_projection=projection)


def evaluate_semantic_review_result(
    raw: Any,
    *,
    review_input: dict[str, Any],
    runner_metadata: dict[str, Any],
) -> SemanticReviewDecision:
    """Normalize reviewer JSON and project its only authoritative task status."""

    normalized = normalize_reviewer_result(
        raw,
        review_input=review_input,
        runner_metadata=runner_metadata,
    )
    task = review_input.get("task", {}) if isinstance(review_input.get("task", {}), dict) else {}
    return project_normalized_semantic_review_result(normalized, task=task)
