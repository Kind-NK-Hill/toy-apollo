from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from formalization_engine.block_id_naming import canonicalize_block_id, is_canonical_block_id

from .phase2_semantic_review import (
    _validate_review_input_internal_binding,
    render_semantic_review_prompt,
)
from .phase2_review_decision import evaluate_semantic_review_result
from .state_store import SubjectBundle, sha256_bytes, sha256_file, sha256_json


RECOVERY_SCHEMA = "toy-apollo.historical-review-apply-recovery.v1"
RECOVERY_AUTHORITY_SCOPE = "recovered_historical_phase2_review_apply"
SUPPORTED_PROMPTS = frozenset({9, 10, 11})
SUPPORTED_DISPOSITIONS = frozenset(
    {"official_output_review_pass", "codex_review_pass_promoted"}
)
_VERSIONED_RESULT = re.compile(r"semantic_review_result_v(\d+)\.json$", re.IGNORECASE)
_VERSIONED_VERIFY = re.compile(r"verify_result_v(\d+)\.json$", re.IGNORECASE)


class HistoricalReviewApplyRecoveryError(ValueError):
    pass


def _read_json(path: Path) -> Mapping[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise HistoricalReviewApplyRecoveryError(f"cannot read JSON evidence {path}: {exc}") from exc
    if not isinstance(payload, Mapping):
        raise HistoricalReviewApplyRecoveryError(f"JSON evidence is not an object: {path}")
    return payload


def _versioned(path: Path, pattern: re.Pattern[str], label: str) -> int:
    match = pattern.fullmatch(path.name)
    if match is None:
        raise HistoricalReviewApplyRecoveryError(f"{label} must be an immutable versioned artifact")
    return int(match.group(1))


def _same_pack_artifact(pack_dir: Path, owner: Path, raw: Any, label: str) -> Path:
    raw_text = str(raw or "").strip()
    if not raw_text:
        raise HistoricalReviewApplyRecoveryError(f"{label} path is missing")
    candidate = Path(raw_text).expanduser()
    candidates = [candidate if candidate.is_absolute() else owner.parent / candidate]
    candidates.append(owner.parent / candidate.name)
    for item in candidates:
        resolved = item.resolve()
        if resolved.is_file() and resolved.parent == pack_dir:
            return resolved
    raise HistoricalReviewApplyRecoveryError(f"{label} is missing from the recovery pack")


def _artifact(path: Path, *, json_payload: Mapping[str, Any] | None = None) -> dict[str, str]:
    result = {"path": path.name, "sha256": sha256_file(path)}
    if json_payload is not None:
        result["canonical_sha256"] = sha256_json(json_payload)
    return result


def _subject_payload(subject: SubjectBundle) -> dict[str, Any]:
    return {
        "task_id": subject.task_id,
        "subject_id": subject.subject_id,
        "subject_kind": subject.subject_kind,
        "source_repo": subject.source_repo,
        "source_commit": subject.source_commit,
        "layout": subject.layout,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path,
        "files": subject.manifest(),
    }


def _subject_from_input(task_id: str, review_input: Mapping[str, Any]) -> SubjectBundle:
    raw = review_input.get("subject_bundle")
    if not isinstance(raw, Mapping):
        candidate = review_input.get("candidate")
        candidate = candidate if isinstance(candidate, Mapping) else {}
        subject_hash = str(review_input.get("review_subject_hash", "") or "")
        candidate_hash = str(candidate.get("hash", "") or "")
        candidate_lean = candidate.get("lean")
        if (
            not subject_hash
            or candidate_hash != subject_hash
            or not isinstance(candidate_lean, str)
            or sha256_bytes(candidate_lean.encode("utf-8")) != subject_hash
        ):
            raise HistoricalReviewApplyRecoveryError(
                f"{task_id}: legacy review input lacks an exact embedded subject"
            )
        # Match the legacy semantic-artifact subject identity used by the
        # state importer.  The canonical input hash immutably binds the full
        # Lean text; size=0 is the historical manifest convention.
        return SubjectBundle.from_manifest(
            task_id=task_id,
            files=[
                {
                    "path": f"legacy/{task_id}.lean",
                    "content_sha256": subject_hash,
                    "git_blob_sha": "",
                    "size": 0,
                }
            ],
            primary_path=f"legacy/{task_id}.lean",
            source_repo="toy_apollo",
            source_commit="",
            layout="phase2_review_artifact",
            subject_kind="legacy_bound",
        )
    try:
        subject = SubjectBundle.from_manifest(
            task_id=task_id,
            files=raw.get("files", []),
            primary_path=str(raw.get("primary_path", "") or ""),
            source_repo=str(raw.get("source_repo", "") or ""),
            source_commit=str(raw.get("source_commit", "") or ""),
            layout=str(raw.get("layout", "") or ""),
            subject_kind=str(raw.get("subject_kind", "") or "review_input_bundle"),
            parent_subject_id=str(raw.get("parent_subject_id", "") or ""),
        )
    except (TypeError, ValueError) as exc:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: invalid source subject: {exc}") from exc
    for key, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
    ):
        declared = str(raw.get(key, "") or "")
        if declared and declared != actual:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: source subject {key} mismatch")
    return subject


def _assert_request_binding(
    *,
    task_id: str,
    request: Mapping[str, Any],
    review_input: Mapping[str, Any],
    input_hash: str,
    result_path: Path,
    input_path: Path,
    prompt_path: Path,
    context_path: Path,
) -> None:
    subject_hash = str(review_input.get("review_subject_hash", "") or "")
    expected = {
        "task_id": task_id,
        "review_input_hash": input_hash,
        "review_subject_hash": subject_hash,
        "review_basis_hash": str(review_input.get("review_basis_hash", "") or ""),
        "prompt_version": int(review_input.get("prompt_version", 0) or 0),
        "rubric_version": int(review_input.get("rubric_version", 0) or 0),
    }
    for key, value in expected.items():
        actual = request.get(key)
        # The earliest request.v1 writer did not serialize this redundant
        # field.  The versioned result still binds the canonical input hash,
        # while the request independently binds subject, basis, paths and
        # prompt/rubric.  A present-but-different value always fails.
        if key == "review_input_hash" and actual in (None, ""):
            continue
        if actual != value:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: review request {key} mismatch")
    for key, path in (
        ("review_input_file", input_path),
        ("review_prompt_file", prompt_path),
        ("review_context_file", context_path),
        ("expected_result_file", result_path),
    ):
        if Path(str(request.get(key, "") or "")).name != path.name:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: review request {key} mismatch")


def _marker_is_active(payload: Mapping[str, Any]) -> str:
    for key, value in payload.items():
        if key in {"invalidated_by", "quarantined_by", "quarantine_reason"} and str(
            value or ""
        ).strip():
            return key
        if key in {
            "quarantined",
            "dependency_reconciliation_requires_fresh_review",
            "dependency_drift",
        } and value is True:
            return key
        if isinstance(value, Mapping):
            nested = _marker_is_active(value)
            if nested:
                return nested
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, Mapping):
                    nested = _marker_is_active(item)
                    if nested:
                        return nested
    return ""


def _projects_clean_pass(
    result: Mapping[str, Any],
    review_input: Mapping[str, Any],
    *,
    runner_status: str,
) -> bool:
    """Accept a PASS only through the canonical status projection.

    Early prompt-9 results did not always persist ``phase2_status`` back into
    the result JSON.  Their versioned review-apply evidence did, however,
    record the canonical projection.  Re-running the same normalizer here
    preserves the fail-closed semantic gate without treating a missing legacy
    serialization field as a failed review.
    """

    serialized_phase2 = str(result.get("phase2_status", "") or "").lower()
    if serialized_phase2 and serialized_phase2 != "pass":
        return False
    decision = evaluate_semantic_review_result(
        dict(result),
        review_input=dict(review_input),
        runner_metadata={"status": runner_status},
    )
    return bool(
        decision.is_semantic_verdict
        and decision.is_clean_pass
        and decision.task_status_projection is not None
        and decision.task_status_projection.task_status == "pass"
    )


def _later_result_projects_same_clean_pass(
    pack_dir: Path,
    path: Path,
    payload: Mapping[str, Any],
    *,
    input_hash: str,
    candidate_hash: str,
) -> bool:
    if (
        str(payload.get("verdict", "") or "").lower() != "pass"
        or str(payload.get("review_input_hash", "") or "") != input_hash
        or str(payload.get("candidate_hash", "") or "") != candidate_hash
    ):
        return False
    try:
        later_input_path = _same_pack_artifact(
            pack_dir,
            path,
            payload.get("review_input_file"),
            "later review input",
        )
        later_input = _read_json(later_input_path)
    except HistoricalReviewApplyRecoveryError:
        return False
    if sha256_json(later_input) != input_hash:
        return False
    if _validate_review_input_internal_binding(dict(later_input)):
        return False
    return _projects_clean_pass(
        payload,
        later_input,
        runner_status="historical_review_apply_recovery_later_result_validation",
    )


def _assert_no_later_conflict(
    pack_dir: Path,
    *,
    task_id: str,
    result_version: int,
    verify_attempt: int,
    input_hash: str,
    candidate_hash: str,
) -> list[dict[str, str]]:
    observed: list[dict[str, str]] = []
    for path in sorted(pack_dir.glob("semantic_review_result_v*.json")):
        match = _VERSIONED_RESULT.fullmatch(path.name)
        if match is None:
            continue
        payload = _read_json(path)
        observed.append(_artifact(path, json_payload=payload))
        marker = _marker_is_active(payload)
        if marker:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: {path.name} carries {marker}")
        if int(match.group(1)) <= result_version:
            continue
        if not _later_result_projects_same_clean_pass(
            pack_dir,
            path,
            payload,
            input_hash=input_hash,
            candidate_hash=candidate_hash,
        ):
            raise HistoricalReviewApplyRecoveryError(
                f"{task_id}: later semantic result conflicts with the recovered apply"
            )
    for path in sorted(pack_dir.glob("verify_result_v*.json")):
        match = _VERSIONED_VERIFY.fullmatch(path.name)
        if match is None:
            continue
        payload = _read_json(path)
        observed.append(_artifact(path, json_payload=payload))
        marker = _marker_is_active(payload)
        if marker:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: {path.name} carries {marker}")
        attempt = int(payload.get("attempt", match.group(1)) or match.group(1))
        if attempt <= verify_attempt:
            continue
        disposition = str(payload.get("disposition", "") or "").lower()
        semantic = payload.get("semantic_review")
        semantic = semantic if isinstance(semantic, Mapping) else {}
        if (
            payload.get("success") is not True
            or "quarant" in disposition
            or str(semantic.get("verdict", "") or "").lower() not in {"", "pass"}
        ):
            raise HistoricalReviewApplyRecoveryError(
                f"{task_id}: later verify evidence conflicts with the recovered apply"
            )
    metadata_path = pack_dir / "metadata.json"
    if metadata_path.is_file():
        metadata = _read_json(metadata_path)
        observed.append(_artifact(metadata_path, json_payload=metadata))
        marker = _marker_is_active(metadata)
        if marker:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: metadata carries {marker}")
        status = str(metadata.get("phase2_status", "") or "").lower()
        if status and status != "pass":
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: metadata has non-pass phase2 status")
    history_path = pack_dir / "attempt_history.json"
    if history_path.is_file():
        history = _read_json(history_path)
        observed.append(_artifact(history_path, json_payload=history))
        marker = _marker_is_active(history)
        if marker:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: attempt history carries {marker}")
        attempts = history.get("attempts")
        if isinstance(attempts, list):
            for raw in attempts:
                if not isinstance(raw, Mapping):
                    continue
                attempt = int(raw.get("attempt", 0) or 0)
                if attempt <= verify_attempt:
                    continue
                verdict = str(raw.get("review_verdict", "") or "").lower()
                disposition = str(raw.get("disposition", "") or "").lower()
                if (
                    raw.get("success") is not True
                    or verdict not in {"", "pass"}
                    or "quarant" in disposition
                ):
                    raise HistoricalReviewApplyRecoveryError(
                        f"{task_id}: later attempt history conflicts with the recovered apply"
                    )
    return observed


def build_historical_review_apply_recovery(
    *,
    pack_dir: Path,
    result_path: Path,
    verify_path: Path,
    created_at: str | None = None,
) -> dict[str, Any]:
    pack_dir = pack_dir.resolve()
    result_path = result_path.resolve()
    verify_path = verify_path.resolve()
    if result_path.parent != pack_dir or verify_path.parent != pack_dir:
        raise HistoricalReviewApplyRecoveryError("recovery artifacts must be in one task-local pack")
    result_version = _versioned(result_path, _VERSIONED_RESULT, "review result")
    _versioned(verify_path, _VERSIONED_VERIFY, "verify result")
    result = _read_json(result_path)
    verify = _read_json(verify_path)
    task_id = canonicalize_block_id(str(result.get("task_id", "") or ""))
    if not task_id or not is_canonical_block_id(task_id):
        raise HistoricalReviewApplyRecoveryError("review result contains an invalid task id")
    if canonicalize_block_id(str(verify.get("task_id", "") or "")) != task_id:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: verify task mismatch")
    if not re.fullmatch(
        r"phase2\.semantic_review\.result\.v\d+",
        str(result.get("schema_version", "") or ""),
    ):
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result schema is unsupported")

    prompt_version = int(result.get("prompt_version", 0) or 0)
    rubric_version = int(result.get("rubric_version", 0) or 0)
    if prompt_version not in SUPPORTED_PROMPTS or rubric_version != 9:
        raise HistoricalReviewApplyRecoveryError(
            f"{task_id}: unsupported prompt/rubric {prompt_version}/{rubric_version}"
        )
    if (
        str(result.get("verdict", "") or "").lower() != "pass"
        or not str(result.get("proof_class", "") or "").strip()
        or not str(result.get("completion_class", "") or "").strip()
    ):
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result is not a canonical clean PASS")
    independence = result.get("reviewer_independence")
    if (
        not isinstance(independence, Mapping)
        or independence.get("read_only") is not True
        or independence.get("did_edit_candidate") is not False
        or independence.get("used_current_review_request") is not True
    ):
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: reviewer independence is invalid")
    backend = str(result.get("reviewer_backend_id", "") or "").lower()
    if not backend or "rescue" in backend or "sidecar" in backend:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: rescue/sidecar review is ineligible")
    marker = _marker_is_active(result)
    if marker:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result carries {marker}")

    input_path = _same_pack_artifact(pack_dir, result_path, result.get("review_input_file"), "review input")
    prompt_path = _same_pack_artifact(pack_dir, result_path, result.get("review_prompt_file"), "review prompt")
    context_path = _same_pack_artifact(pack_dir, result_path, result.get("review_context_file"), "review context")
    input_version = _versioned(input_path, re.compile(r"semantic_review_input_v(\d+)\.json$", re.I), "review input")
    _versioned(prompt_path, re.compile(r"semantic_review_prompt_v(\d+)\.md$", re.I), "review prompt")
    _versioned(context_path, re.compile(r"semantic_review_context_v(\d+)\.md$", re.I), "review context")
    if input_version != result_version:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result/input versions differ")
    request_path = pack_dir / f"semantic_review_request_v{result_version}.json"
    if not request_path.is_file():
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: versioned review request is missing")
    review_input = _read_json(input_path)
    request = _read_json(request_path)
    if str(request.get("schema_version", "") or "") != "phase2.semantic_review.request.v1":
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: review request schema is unsupported")
    input_hash = sha256_json(review_input)
    if str(result.get("review_input_hash", "") or "") != input_hash:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result review input hash mismatch")
    if int(review_input.get("prompt_version", 0) or 0) != prompt_version:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: input/result prompt versions differ")
    if int(review_input.get("rubric_version", 0) or 0) != rubric_version:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: input/result rubric versions differ")
    binding_error = _validate_review_input_internal_binding(dict(review_input))
    if binding_error:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: invalid review input binding: {binding_error}")
    decision = evaluate_semantic_review_result(
        dict(result),
        review_input=dict(review_input),
        runner_metadata={"status": "historical_review_apply_recovery_validation"},
    )
    if not _projects_clean_pass(
        result,
        review_input,
        runner_status="historical_review_apply_recovery_validation",
    ):
        reason = str(decision.result.get("normalization_reason", "") or "not a clean projected PASS")
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: canonical review decision failed: {reason}")
    _assert_request_binding(
        task_id=task_id,
        request=request,
        review_input=review_input,
        input_hash=input_hash,
        result_path=result_path,
        input_path=input_path,
        prompt_path=prompt_path,
        context_path=context_path,
    )
    if prompt_path.read_text(encoding="utf-8").strip() != render_semantic_review_prompt(dict(review_input)).strip():
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: prompt is not an exact input render")
    if context_path.read_text(encoding="utf-8").strip() != str(
        review_input.get("review_context_markdown", "") or ""
    ).strip():
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: context does not match review input")

    subject = _subject_from_input(task_id, review_input)
    candidate_hash = str(result.get("candidate_hash", "") or "")
    if candidate_hash != subject.primary_hash:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result candidate hash mismatch")
    result_runner = result.get("runner")
    if (
        not isinstance(result_runner, Mapping)
        or str(result_runner.get("status", "") or "") != "codex_handoff_applied"
        or Path(str(result_runner.get("result_file", "") or "")).name != result_path.name
    ):
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: result runner is not the applied canonical handoff")
    semantic = verify.get("semantic_review")
    semantic = semantic if isinstance(semantic, Mapping) else {}
    final_build = verify.get("final_build")
    final_build = final_build if isinstance(final_build, Mapping) else {}
    if (
        str(verify.get("mode", "") or "") != "review-apply"
        or verify.get("success") is not True
        or str(verify.get("disposition", "") or "") not in SUPPORTED_DISPOSITIONS
        or str(semantic.get("runner_status", "") or "") != "codex_handoff_applied"
        or str(semantic.get("verdict", "") or "").lower() != "pass"
        or str(semantic.get("phase2_status", "") or "").lower() != "pass"
        or final_build.get("success") is not True
    ):
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: verify evidence is not a successful review-apply")
    for key in ("proof_class", "completion_class"):
        if str(semantic.get(key, "") or "") != str(result.get(key, "") or ""):
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: verify {key} mismatch")
    for key, expected in (
        ("review_result_file", result_path.name),
        ("review_input_file", input_path.name),
        ("review_prompt_file", prompt_path.name),
    ):
        if Path(str(semantic.get(key, "") or "")).name != expected:
            raise HistoricalReviewApplyRecoveryError(f"{task_id}: verify {key} mismatch")
    if str(verify.get("candidate_hash", "") or "") != subject.primary_hash:
        raise HistoricalReviewApplyRecoveryError(f"{task_id}: verify candidate hash mismatch")
    verify_attempt = int(verify.get("attempt", 0) or 0)
    observed = _assert_no_later_conflict(
        pack_dir,
        task_id=task_id,
        result_version=result_version,
        verify_attempt=verify_attempt,
        input_hash=input_hash,
        candidate_hash=subject.primary_hash,
    )
    result_hash = sha256_file(result_path)
    review_id = sha256_json(
        {
            "schema": "toy-apollo.review.v1",
            "task_id": task_id,
            "subject_id": subject.subject_id,
            "evidence_hash": result_hash,
            "authority_scope": RECOVERY_AUTHORITY_SCOPE,
        }
    )
    timestamp = created_at or datetime.now(timezone.utc).isoformat()
    checks = {
        "canonical_binding": "pass",
        "review_apply": "pass",
        "final_build": "pass",
        "independence": "pass",
        "no_rescue_or_sidecar": "pass",
        "no_later_conflicting_evidence": "pass",
        "no_invalidation_or_quarantine": "pass",
        "no_dependency_drift": "pass",
        "observed_pack_artifacts": observed,
    }
    if not str(result.get("phase2_status", "") or "").strip():
        checks["phase2_projection_source"] = (
            "canonical_review_decision_plus_versioned_review_apply"
        )
    if request.get("review_input_hash") in (None, ""):
        checks["request_input_binding_source"] = (
            "versioned_result_hash_plus_request_subject_basis_paths"
        )
    return {
        "schema": RECOVERY_SCHEMA,
        "task_id": task_id,
        "created_at": timestamp,
        "recovery_kind": "historical_canonical_review_apply",
        "authority_scope": RECOVERY_AUTHORITY_SCOPE,
        "semantic_upgrade": False,
        "current_target_binding": False,
        "source_review": {
            "review_id": review_id,
            "verdict": "pass",
            "phase2_status": "pass",
            "proof_class": str(result.get("proof_class", "") or ""),
            "completion_class": str(result.get("completion_class", "") or ""),
            "prompt_version": prompt_version,
            "rubric_version": rubric_version,
            "reviewer_independence": dict(independence),
            "reviewer_backend_id": str(result.get("reviewer_backend_id", "") or ""),
            "applied_at": str(verify.get("verified_at", "") or timestamp),
        },
        "source_subject": _subject_payload(subject),
        "artifacts": {
            "result": _artifact(result_path, json_payload=result),
            "input": _artifact(input_path, json_payload=review_input),
            "request": _artifact(request_path, json_payload=request),
            "prompt": _artifact(prompt_path),
            "context": _artifact(context_path),
            "verify": _artifact(verify_path, json_payload=verify),
        },
        "checks": checks,
    }


def validate_historical_review_apply_recovery(
    receipt_path: Path,
    receipt: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any], SubjectBundle]:
    receipt_path = receipt_path.resolve()
    payload = dict(receipt or _read_json(receipt_path))
    if payload.get("schema") != RECOVERY_SCHEMA:
        raise HistoricalReviewApplyRecoveryError("historical review-apply recovery has an unsupported schema")
    artifacts = payload.get("artifacts")
    if not isinstance(artifacts, Mapping):
        raise HistoricalReviewApplyRecoveryError("historical review-apply recovery lacks artifacts")
    result_ref = artifacts.get("result")
    verify_ref = artifacts.get("verify")
    if not isinstance(result_ref, Mapping) or not isinstance(verify_ref, Mapping):
        raise HistoricalReviewApplyRecoveryError("historical review-apply recovery lacks result/verify references")
    result_path = _same_pack_artifact(receipt_path.parent, receipt_path, result_ref.get("path"), "review result")
    verify_path = _same_pack_artifact(receipt_path.parent, receipt_path, verify_ref.get("path"), "verify result")
    rebuilt = build_historical_review_apply_recovery(
        pack_dir=receipt_path.parent,
        result_path=result_path,
        verify_path=verify_path,
        created_at=str(payload.get("created_at", "") or ""),
    )
    if sha256_json(payload) != sha256_json(rebuilt):
        raise HistoricalReviewApplyRecoveryError("historical review-apply recovery receipt does not match validated evidence")
    subject = _subject_from_input(
        str(rebuilt["task_id"]),
        _read_json(receipt_path.parent / str(rebuilt["artifacts"]["input"]["path"])),
    )
    return rebuilt, subject
