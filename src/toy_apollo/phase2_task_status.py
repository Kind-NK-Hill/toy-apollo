from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.block_id_naming import canonicalize_block_id


TASK_STATUS_PASS = "pass"
TASK_STATUS_FAIL = "fail"
TASK_STATUS_BLOCKED = "blocked"
TASK_STATUS_ALLOWED_EXCEPTION = "allowed_exception"

PROOF_BEARING_ROLE = "proof_bearing"
DEFINITION_INTERFACE_ROLE = "definition_interface"
REMARK_ROLE = "remark"
UNKNOWN_ROLE = "unknown"

PROOF_BEARING_TYPE_MARKERS = ("theorem", "problem", "exercise", "example", "obligation")
DEFINITION_INTERFACE_TYPE_MARKERS = ("definition", "notation", "interface", "bridge")
REMARK_TYPE_MARKERS = ("remark",)
PROOF_BEARING_ID_PREFIXES = ("thm_", "prob_", "ex_")
DEFINITION_INTERFACE_ID_PREFIXES = ("def_", "notation_", "interface_", "bridge_")
REMARK_ID_PREFIXES = ("rem_", "intro_")

LOCAL_DEFECT_MARKERS = (
    "open_math_debt",
    "needs_decision",
    "adapter",
    "statement_weakened",
    "weakened",
    "public_premise",
    "reassumption",
    "semantic_fail",
    "source_route_mismatch",
    "local_defect",
)
BLOCKED_CLASS_MARKERS = (
    "dependency_blocked",
    "dependency_failed",
    "fresh_review_refused_by_dependency_gate",
)
PROOF_BEARING_PASS_PREFIXES = (
    "textbook_proof_completed",
    "textbook_problem_completed",
    "textbook_exercise_completed",
    "textbook_source_route_completed",
    "source_route_proof_completed",
    "source_faithful_proof_completed",
    "normal_proof_source_route",
    "source_route_theorem",
)
DEFINITION_INTERFACE_PASS_PREFIXES = (
    "textbook_definition_completed",
    "definition_only_completed",
    "source_faithful_definition_bridge_completed",
    "source_faithful_notation_bridge_completed",
    "interface_bridge_completed",
)
REMARK_PASS_PREFIXES = (
    "textbook_remark_completed",
    "source_faithful_textual_remark_completed",
    "source_faithful_non_theorem_artifact",
    "non_proof_textual_remark_carrier",
)
BRIDGE_CLASSES = (
    "interface_bridge_completed",
    "source_faithful_definition_bridge_completed",
    "source_faithful_notation_bridge_completed",
)
OBLIGATION_CHILD_PASS_CLASSES = (
    "focused_child_obligation_completed",
    "focused_child_source_route_theorem",
    "focused_obligation_closed",
    "source_route_support_predicate_completed",
    "source_route_support_completed",
)
ALLOWED_EXCEPTION_TASK_CLASSES = {
    "thm_11_8": {"cited_external_proof_exception"},
    "thm_14_8": {"beyond_book_exception"},
}


@dataclass(frozen=True)
class Phase2TaskStatusClassification:
    task_id: str
    task_type: str
    task_role: str
    review_verdict: str
    proof_class: str
    task_status: str
    reason: str
    evidence_type: str
    needs_class_normalization: bool = False

    def as_metadata(self) -> dict[str, Any]:
        return {
            "phase2_status": self.task_status,
            "phase2_status_reason": self.reason,
            "phase2_status_evidence_type": self.evidence_type,
            "phase2_task_status": self.task_status,
            "phase2_task_status_reason": self.reason,
            "phase2_task_status_evidence_type": self.evidence_type,
            "phase2_task_role": self.task_role,
            "phase2_proof_class": self.proof_class,
            "phase2_needs_class_normalization": self.needs_class_normalization,
        }


def classify_phase2_task_status(
    *,
    task_id: str,
    task_type: str = "",
    review_verdict: str,
    proof_class: Any = "",
    completion_class: Any = "",
) -> Phase2TaskStatusClassification:
    canonical_task_id = canonicalize_block_id(str(task_id or ""))
    normalized_task_type = str(task_type or "").strip()
    verdict = str(review_verdict or "").strip().lower()
    normalized_proof_class = _normalize_class(proof_class) or _normalize_class(completion_class)
    task_role = infer_phase2_task_role(canonical_task_id, normalized_task_type)

    if not normalized_proof_class:
        needs_normalization = verdict == "pass"
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class="",
            task_status=TASK_STATUS_FAIL,
            reason=(
                "review verdict has no proof_class/completion_class; needs_class_normalization before task-level pass"
                if needs_normalization
                else "review did not provide a proof_class/completion_class"
            ),
            evidence_type="needs_class_normalization" if needs_normalization else "review_without_completion_class",
            needs_class_normalization=needs_normalization,
        )

    if _has_local_defect(normalized_proof_class):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_FAIL,
            reason=f"proof_class {normalized_proof_class} contains local open debt/adapter/weakening evidence",
            evidence_type="local_open_debt",
        )

    if _is_dependency_blocked(normalized_proof_class):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_BLOCKED,
            reason=f"proof_class {normalized_proof_class} is dependency-gate blocked without local open debt",
            evidence_type="blocked_by_dependency_gate",
        )

    if verdict != "pass":
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_FAIL,
            reason=f"review verdict {verdict or '(missing)'} is not pass",
            evidence_type="review_verdict_not_pass",
        )

    if normalized_proof_class in ALLOWED_EXCEPTION_TASK_CLASSES.get(canonical_task_id, set()):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_ALLOWED_EXCEPTION,
            reason=f"{normalized_proof_class} is the explicit allowed Phase2 exception for {canonical_task_id}",
            evidence_type="explicit_allowed_exception",
        )

    if _is_obligation_child_task(canonical_task_id, normalized_task_type) and (
        normalized_proof_class in OBLIGATION_CHILD_PASS_CLASSES
        or _normalize_class(completion_class) in OBLIGATION_CHILD_PASS_CLASSES
    ):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_PASS,
            reason=f"{normalized_proof_class} is focused completion for an internal Phase2 obligation-child task",
            evidence_type="fresh_review_task_projection",
        )

    if task_role == DEFINITION_INTERFACE_ROLE and _starts_with_any(normalized_proof_class, DEFINITION_INTERFACE_PASS_PREFIXES):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_PASS,
            reason=f"{normalized_proof_class} is task-level completion for a definition/interface/notation task",
            evidence_type="fresh_review_task_projection",
        )

    if task_role == REMARK_ROLE and _starts_with_any(normalized_proof_class, REMARK_PASS_PREFIXES):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_PASS,
            reason=f"{normalized_proof_class} is task-level completion for a non-proof remark task",
            evidence_type="fresh_review_task_projection",
        )

    if task_role == PROOF_BEARING_ROLE and _starts_with_any(normalized_proof_class, PROOF_BEARING_PASS_PREFIXES):
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_PASS,
            reason=f"{normalized_proof_class} is source-route completion for a proof-bearing task",
            evidence_type="fresh_review_task_projection",
        )

    if task_role == PROOF_BEARING_ROLE and normalized_proof_class in BRIDGE_CLASSES:
        return Phase2TaskStatusClassification(
            task_id=canonical_task_id,
            task_type=normalized_task_type,
            task_role=task_role,
            review_verdict=verdict,
            proof_class=normalized_proof_class,
            task_status=TASK_STATUS_FAIL,
            reason=f"bridge proof_class {normalized_proof_class} cannot make a proof-bearing task pass",
            evidence_type="bridge_not_task_pass",
        )

    return Phase2TaskStatusClassification(
        task_id=canonical_task_id,
        task_type=normalized_task_type,
        task_role=task_role,
        review_verdict=verdict,
        proof_class=normalized_proof_class,
        task_status=TASK_STATUS_FAIL,
        reason=f"proof_class {normalized_proof_class} is not a task-level pass class for role {task_role}",
        evidence_type="class_not_task_pass",
    )


def infer_phase2_task_role(task_id: str, task_type: str = "") -> str:
    normalized_type = str(task_type or "").strip().lower().replace("-", "_")
    if any(marker in normalized_type for marker in PROOF_BEARING_TYPE_MARKERS):
        return PROOF_BEARING_ROLE
    if any(marker in normalized_type for marker in DEFINITION_INTERFACE_TYPE_MARKERS):
        return DEFINITION_INTERFACE_ROLE
    if any(marker in normalized_type for marker in REMARK_TYPE_MARKERS):
        return REMARK_ROLE

    canonical_task_id = canonicalize_block_id(str(task_id or ""))
    if canonical_task_id.startswith(PROOF_BEARING_ID_PREFIXES):
        return PROOF_BEARING_ROLE
    if canonical_task_id.startswith(DEFINITION_INTERFACE_ID_PREFIXES):
        return DEFINITION_INTERFACE_ROLE
    if canonical_task_id.startswith(REMARK_ID_PREFIXES):
        return REMARK_ROLE
    return UNKNOWN_ROLE


def _is_obligation_child_task(task_id: str, task_type: str = "") -> bool:
    normalized_type = str(task_type or "").strip().lower().replace("-", "_").replace(" ", "_")
    canonical_task_id = canonicalize_block_id(str(task_id or ""))
    return normalized_type in {"phase2obligationtask", "phase2_obligation_task"} or canonical_task_id.startswith("obl_")


def _normalize_class(value: Any) -> str:
    return str(value or "").strip().lower().replace("-", "_").replace("/", "_").replace(" ", "_")


def _starts_with_any(value: str, prefixes: tuple[str, ...]) -> bool:
    return any(
        value == prefix or value.startswith(prefix if prefix.endswith("_") else prefix + "_")
        for prefix in prefixes
    )


def _has_local_defect(proof_class: str) -> bool:
    return any(marker in proof_class for marker in LOCAL_DEFECT_MARKERS)


def _is_dependency_blocked(proof_class: str) -> bool:
    return any(marker in proof_class for marker in BLOCKED_CLASS_MARKERS)
