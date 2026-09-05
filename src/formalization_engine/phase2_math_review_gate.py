from __future__ import annotations

from dataclasses import dataclass
import os
import re
from pathlib import Path
from typing import Any

from formalization_engine.block_id_naming import canonicalize_block_id

from .phase2_pack_shared.io import fs_path, path_exists, read_file_safely, read_json_safely, sha256_text


MATH_REVIEW_GATE_PILOT_TASK_IDS = frozenset({"prob_14_1", "prob_14_8"})
MATH_REVIEW_GATE_TRIAGE_CATEGORIES = frozenset(
    {
        "public_premise",
        "statement_or_source_mismatch",
        "source_mismatch",
        "wrong_route",
        "mathlib_adapter",
        "private_axiom_or_open_math_debt",
        "unclear_semantic_failure",
    }
)
MATH_REVIEW_GATE_TEXT_MARKERS = (
    ("semantic_fail_public_premise", "semantic_fail_public_premise"),
    ("public-premise relocation", "public_premise_relocation"),
    ("public premise relocation", "public_premise_relocation"),
    ("public setup field", "public_setup_field"),
    ("caller-supplied public field", "public_setup_field"),
    ("caller supplied public field", "public_setup_field"),
    ("source_mismatch", "source_mismatch"),
    ("source mismatch", "source_mismatch"),
    ("statement mismatch", "statement_mismatch"),
    ("dirty family", "family_dirty_or_blocked"),
    ("family blocked", "family_dirty_or_blocked"),
)
MATH_REVIEW_PROOF_SKELETON_PREFIX = "math_proof_skeleton"
MATH_REVIEW_RESULT_PREFIX = "math_review_result"
MATH_REVIEW_PRE_AUTHOR_CHECKLIST = (
    "pre-author checklist: source statement identified; "
    "no public premise relocation; "
    "math proof skeleton reviewed go; "
    "independent semantic review after build"
)


@dataclass(frozen=True)
class MathReviewGateState:
    required: bool
    status: str
    verdict: str
    stop_mode: str
    reason: str
    triggers: tuple[str, ...]
    proof_skeleton_file: str = ""
    proof_skeleton_hash: str = ""
    review_result_file: str = ""
    review_result_hash: str = ""
    blocking_theorems: tuple[str, ...] = ()
    allowed_next_targets: tuple[str, ...] = ()
    forbidden_work: tuple[str, ...] = ()

    def blocks_authoring(self) -> bool:
        return self.required and self.status != "go"

    def as_metadata(self) -> dict[str, Any]:
        return {
            "math_review_gate_required": self.required,
            "math_review_gate_status": self.status,
            "latest_math_review_verdict": self.verdict,
            "latest_math_review_stop_mode": self.stop_mode,
            "latest_math_review_reason": self.reason,
            "latest_math_review_triggers": list(self.triggers),
            "latest_math_proof_skeleton_file": self.proof_skeleton_file,
            "latest_math_proof_skeleton_hash": self.proof_skeleton_hash,
            "latest_math_review_result_file": self.review_result_file,
            "latest_math_review_result_hash": self.review_result_hash,
            "latest_math_review_blocking_theorems": list(self.blocking_theorems),
            "latest_math_review_allowed_next_targets": list(self.allowed_next_targets),
            "latest_math_review_forbidden_work": list(self.forbidden_work),
        }


def math_review_gate_state(
    task_id: str,
    record: dict[str, Any] | None = None,
    *,
    pack_dir: Path | str | None = None,
) -> MathReviewGateState:
    record = record if isinstance(record, dict) else {}
    canonical_task_id = canonicalize_block_id(task_id)
    triggers = _math_review_gate_triggers(canonical_task_id, record)
    skeleton_path = _latest_artifact_path(
        record,
        pack_dir=pack_dir,
        record_keys=("latest_math_proof_skeleton_file", "math_proof_skeleton_file"),
        prefix=MATH_REVIEW_PROOF_SKELETON_PREFIX,
        suffix=".md",
    )
    review_path = _latest_artifact_path(
        record,
        pack_dir=pack_dir,
        record_keys=("latest_math_review_result_file", "math_review_result_file"),
        prefix=MATH_REVIEW_RESULT_PREFIX,
        suffix=".json",
    )
    skeleton_hash = _file_hash(skeleton_path)
    review_hash = _file_hash(review_path)
    review_payload = read_json_safely(review_path, {}) if review_path is not None else {}
    review_payload = review_payload if isinstance(review_payload, dict) else {}
    verdict = _math_review_verdict(review_payload or record)
    stop_mode = _math_review_stop_mode(review_payload or record, verdict=verdict)
    blocking_theorems = _string_tuple((review_payload or record).get("blocking_theorems", ()))
    allowed_next_targets = _string_tuple((review_payload or record).get("allowed_next_targets", ()))
    forbidden_work = _string_tuple((review_payload or record).get("forbidden_work", ()))

    if not triggers:
        return MathReviewGateState(
            required=False,
            status="not_required",
            verdict=verdict,
            stop_mode=stop_mode,
            reason="Math Review Gate is not required for this task.",
            triggers=(),
            proof_skeleton_file=str(skeleton_path or ""),
            proof_skeleton_hash=skeleton_hash,
            review_result_file=str(review_path or ""),
            review_result_hash=review_hash,
            blocking_theorems=blocking_theorems,
            allowed_next_targets=allowed_next_targets,
            forbidden_work=forbidden_work,
        )
    if skeleton_path is None:
        return MathReviewGateState(
            required=True,
            status="missing_skeleton",
            verdict=verdict,
            stop_mode=stop_mode,
            reason=_with_pre_author_checklist(
                "Math Review Gate requires a natural language proof skeleton before Lean author/build."
            ),
            triggers=triggers,
            review_result_file=str(review_path or ""),
            review_result_hash=review_hash,
            blocking_theorems=blocking_theorems,
            allowed_next_targets=allowed_next_targets,
            forbidden_work=forbidden_work,
        )
    if review_path is None:
        return MathReviewGateState(
            required=True,
            status="missing_review",
            verdict=verdict,
            stop_mode=stop_mode,
            reason=_with_pre_author_checklist(
                "Math Review Gate requires an independent three-round math review before Lean author/build."
            ),
            triggers=triggers,
            proof_skeleton_file=str(skeleton_path),
            proof_skeleton_hash=skeleton_hash,
            blocking_theorems=blocking_theorems,
            allowed_next_targets=allowed_next_targets,
            forbidden_work=forbidden_work,
        )
    if verdict == "go":
        return MathReviewGateState(
            required=True,
            status="go",
            verdict=verdict,
            stop_mode=stop_mode,
            reason="Math Review Gate verdict is go; Lean author/build may start.",
            triggers=triggers,
            proof_skeleton_file=str(skeleton_path),
            proof_skeleton_hash=skeleton_hash,
            review_result_file=str(review_path),
            review_result_hash=review_hash,
            blocking_theorems=blocking_theorems,
            allowed_next_targets=allowed_next_targets,
            forbidden_work=forbidden_work,
        )
    if verdict == "stop":
        if stop_mode == "blocking_proof":
            reason = "Math Review Gate verdict is stop in blocking_proof mode; prove only the listed blocking theorem targets."
            if blocking_theorems:
                reason += f" Blocking theorems: {', '.join(blocking_theorems)}."
            if allowed_next_targets:
                reason += f" Allowed next targets: {', '.join(allowed_next_targets)}."
            if forbidden_work:
                reason += f" Forbidden work: {', '.join(forbidden_work)}."
        else:
            reason = "Math Review Gate verdict is stop; do not author Lean, rewrite the parent/support theorem shape first."
        return MathReviewGateState(
            required=True,
            status="stop",
            verdict=verdict,
            stop_mode=stop_mode,
            reason=_with_pre_author_checklist(reason),
            triggers=triggers,
            proof_skeleton_file=str(skeleton_path),
            proof_skeleton_hash=skeleton_hash,
            review_result_file=str(review_path),
            review_result_hash=review_hash,
            blocking_theorems=blocking_theorems,
            allowed_next_targets=allowed_next_targets,
            forbidden_work=forbidden_work,
        )
    return MathReviewGateState(
        required=True,
        status="invalid_verdict",
        verdict=verdict,
        stop_mode=stop_mode,
        reason=_with_pre_author_checklist(
            "Math Review Gate result must use verdict `go` or `stop` before Lean author/build."
        ),
        triggers=triggers,
        proof_skeleton_file=str(skeleton_path),
        proof_skeleton_hash=skeleton_hash,
        review_result_file=str(review_path),
        review_result_hash=review_hash,
        blocking_theorems=blocking_theorems,
        allowed_next_targets=allowed_next_targets,
        forbidden_work=forbidden_work,
    )


def math_review_gate_blocker(
    task_id: str,
    record: dict[str, Any] | None = None,
    *,
    pack_dir: Path | str | None = None,
) -> str:
    state = math_review_gate_state(task_id, record, pack_dir=pack_dir)
    if not state.blocks_authoring():
        return ""
    parts = [
        "Math Review Gate required before Lean author/build",
        f"status `{state.status}`",
        f"triggers `{', '.join(state.triggers)}`" if state.triggers else "",
        f"skeleton={state.proof_skeleton_file}" if state.proof_skeleton_file else "write `math_proof_skeleton_vN.md`",
        f"review={state.review_result_file}" if state.review_result_file else "obtain independent read-only xhigh three-round `math_review_result_vN.json`",
        f"verdict `{state.verdict}`" if state.verdict else "verdict must be `go` before authoring",
    ]
    if state.status == "stop":
        if state.stop_mode == "blocking_proof":
            parts.append("verdict is `stop` with stop_mode `blocking_proof`; prove only listed blocking theorem targets")
            if state.blocking_theorems:
                parts.append(f"blocking_theorems `{', '.join(state.blocking_theorems)}`")
            if state.allowed_next_targets:
                parts.append(f"allowed_next_targets `{', '.join(state.allowed_next_targets)}`")
            if state.forbidden_work:
                parts.append(f"forbidden_work `{', '.join(state.forbidden_work)}`")
        else:
            parts.append("verdict is `stop`; output minimal parent/support rewrite direction instead of Lean")
    parts.append(MATH_REVIEW_PRE_AUTHOR_CHECKLIST)
    return "; ".join(part for part in parts if part)


def _with_pre_author_checklist(reason: str) -> str:
    if MATH_REVIEW_PRE_AUTHOR_CHECKLIST in reason:
        return reason
    return f"{reason} {MATH_REVIEW_PRE_AUTHOR_CHECKLIST}."


def _math_review_gate_triggers(task_id: str, record: dict[str, Any]) -> tuple[str, ...]:
    triggers: list[str] = []
    if task_id in MATH_REVIEW_GATE_PILOT_TASK_IDS:
        triggers.append(f"pilot_task:{task_id}")

    category = str(record.get("latest_semantic_fail_triage_category", "") or "").strip().lower()
    if category in MATH_REVIEW_GATE_TRIAGE_CATEGORIES:
        triggers.append(f"semantic_fail_triage:{category}")
    if category.startswith("semantic_fail_public_premise"):
        triggers.append("semantic_fail_public_premise")


    text = _record_text(record)
    for marker, trigger in MATH_REVIEW_GATE_TEXT_MARKERS:
        if marker in text:
            triggers.append(trigger)

    return tuple(dict.fromkeys(trigger for trigger in triggers if trigger))


def _record_text(record: dict[str, Any]) -> str:
    keys = (
        "phase2_status_reason",
        "task_status_reason",
        "reason",
        "issue",
        "next_action",
        "current_class",
        "stop_reason",
        "proof_class",
        "completion_class",
        "phase2_proof_class",
        "phase2_completion_class",
        "latest_semantic_fail_triage_category",
    )
    chunks = [str(record.get(key, "") or "") for key in keys]
    return "\n".join(chunks).lower()




def _latest_artifact_path(
    record: dict[str, Any],
    *,
    pack_dir: Path | str | None,
    record_keys: tuple[str, ...],
    prefix: str,
    suffix: str,
) -> Path | None:
    root = _pack_dir(pack_dir)
    latest_versioned = None
    if root is not None:
        candidates = _versioned_artifact_paths(root, prefix, suffix)
        if candidates:
            latest_versioned = candidates[-1]
    for key in record_keys:
        raw = str(record.get(key, "") or "").strip()
        if not raw:
            continue
        path = Path(raw)
        candidates = [path]
        if root is not None and not path.is_absolute():
            candidates.append(root / path)
        for candidate in candidates:
            if path_exists(candidate):
                if _versioned_artifact_is_newer(
                    latest_versioned,
                    candidate,
                    root=root,
                    prefix=prefix,
                    suffix=suffix,
                ):
                    return latest_versioned
                return candidate
    if root is None:
        return None
    if latest_versioned is not None:
        return latest_versioned
    alias = root / f"{prefix}{suffix}"
    if path_exists(alias):
        return alias
    return None


def _pack_dir(pack_dir: Path | str | None) -> Path | None:
    if pack_dir is None:
        return None
    path = Path(pack_dir)
    return path if path_exists(path) else None


def _versioned_artifact_paths(root: Path, prefix: str, suffix: str) -> list[Path]:
    try:
        names = os.listdir(fs_path(root))
    except OSError:
        return []
    paths = [
        root / name
        for name in names
        if _versioned_artifact_match(name, prefix, suffix) and path_exists(root / name)
    ]
    return sorted(paths, key=lambda path: (_versioned_artifact_number(path.name, prefix, suffix), path.name))


def _versioned_artifact_match(name: str, prefix: str, suffix: str) -> bool:
    return re.fullmatch(rf"{re.escape(prefix)}_v\d+{re.escape(suffix)}", name) is not None


def _versioned_artifact_number(name: str, prefix: str, suffix: str) -> int:
    match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+){re.escape(suffix)}", name)
    if not match:
        return -1
    return int(match.group(1))


def _versioned_artifact_is_newer(
    latest: Path | None,
    candidate: Path,
    *,
    root: Path,
    prefix: str,
    suffix: str,
) -> bool:
    if latest is None:
        return False
    try:
        if candidate.resolve().parent != root.resolve():
            return False
    except OSError:
        return False
    latest_number = _versioned_artifact_number(latest.name, prefix, suffix)
    candidate_number = _versioned_artifact_number(candidate.name, prefix, suffix)
    return latest_number > candidate_number


def _file_hash(path: Path | None) -> str:
    if path is None:
        return ""
    text = read_file_safely(path)
    return sha256_text(text) if text else ""


def _math_review_verdict(payload: dict[str, Any]) -> str:
    for key in ("verdict", "math_review_verdict", "gate_verdict", "stop_go_verdict"):
        verdict = str(payload.get(key, "") or "").strip().lower()
        if verdict:
            return verdict
    route_inspection = payload.get("route_inspection", {})
    if isinstance(route_inspection, dict):
        verdict = str(route_inspection.get("stop_go_verdict", "") or "").strip().lower()
        if verdict:
            return verdict
    return ""


def _math_review_stop_mode(payload: dict[str, Any], *, verdict: str) -> str:
    if verdict != "stop":
        return ""
    stop_mode = str(payload.get("stop_mode", "") or "").strip().lower()
    if stop_mode in {"blocking_proof", "interface_rewrite"}:
        return stop_mode
    return "interface_rewrite"


def _string_tuple(value: Any) -> tuple[str, ...]:
    if isinstance(value, str):
        return (value,) if value.strip() else ()
    if not isinstance(value, list):
        return ()
    items: list[str] = []
    for item in value:
        text = str(item or "").strip()
        if text:
            items.append(text)
    return tuple(items)
