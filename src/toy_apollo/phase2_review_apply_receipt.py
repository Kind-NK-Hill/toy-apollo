"""Immutable, profile-neutral evidence for a successful Phase 2 review apply."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Mapping

from .state_store import SubjectBundle, sha256_file, sha256_json, utc_now


RECEIPT_SCHEMA_VERSION = "toy-apollo.phase2-review-apply-receipt.v1"


def _subject_payload(subject: SubjectBundle) -> dict[str, Any]:
    return {
        "schema": "toy-apollo.subject-bundle.v1",
        "subject_id": subject.subject_id,
        "task_id": subject.task_id,
        "subject_kind": subject.subject_kind,
        "source_repo": subject.source_repo,
        "source_commit": subject.source_commit,
        "layout": subject.layout,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path,
        "files": subject.manifest(),
    }


def _attempt(
    review_input: Mapping[str, Any],
    semantic_review: Mapping[str, Any],
    evidence_path: Path,
) -> int:
    for raw in (semantic_review.get("attempt"), review_input.get("attempt")):
        try:
            value = int(raw)
        except (TypeError, ValueError):
            continue
        if value > 0:
            return value
    match = re.search(r"_v(\d+)\.json$", evidence_path.name.lower())
    return int(match.group(1)) if match else 1


def write_phase2_review_apply_receipt(
    *,
    settings: Any,
    task_id: str,
    review_input: Mapping[str, Any],
    semantic_review: Mapping[str, Any],
    review_subject: SubjectBundle,
    projected_subject: SubjectBundle,
    review_id: str,
    transformation_id: str,
    evidence_path: Path,
    evidence_hash: str,
    disposition: str,
    final_build_success: bool,
    reviewed_head_role: str,
) -> tuple[Path, dict[str, Any]]:
    """Write one idempotent receipt after a clean authority-eligible apply."""

    profile = str(getattr(settings, "profile", "mat") or "mat").strip().lower()
    attempt = _attempt(review_input, semantic_review, evidence_path)
    pack_dir = Path(settings.phase2_prompt_packs_dir) / task_id
    receipt_path = pack_dir / f"review_apply_receipt_v{attempt}.json"
    identity = {
        "schema_version": RECEIPT_SCHEMA_VERSION,
        "profile": profile,
        "task_id": task_id,
        "attempt": attempt,
        "review_id": review_id,
        "transformation_id": transformation_id,
        "review_result_file": str(evidence_path.resolve()),
        "review_result_hash": evidence_hash,
        "review_input_hash": str(semantic_review.get("review_input_hash", "") or ""),
        "review_subject_id": review_subject.subject_id,
        "projected_subject_id": projected_subject.subject_id,
        "disposition": disposition,
    }
    receipt = {
        **identity,
        "receipt_id": sha256_json(identity),
        "applied_at": utc_now(),
        "success": True,
        "final_build_success": bool(final_build_success),
        "authority_scope": "phase2_review_apply",
        "reviewed_head_role": reviewed_head_role,
        "review_input_file": str(semantic_review.get("review_input_file", "") or ""),
        "review_basis_hash": str(review_input.get("review_basis_hash", "") or ""),
        "review": {
            "verdict": str(semantic_review.get("verdict", "") or ""),
            "phase2_status": str(semantic_review.get("phase2_status", "") or ""),
            "proof_class": str(semantic_review.get("proof_class", "") or ""),
            "completion_class": str(semantic_review.get("completion_class", "") or ""),
            "prompt_version": review_input.get("prompt_version"),
            "rubric_version": review_input.get("rubric_version"),
            "reviewer_independence": semantic_review.get("reviewer_independence", ""),
            "reviewer_backend_id": str(review_input.get("reviewer_backend_id", "") or ""),
        },
        "review_subject": _subject_payload(review_subject),
        "projected_subject": _subject_payload(projected_subject),
        "transformation": {
            "kind": "review_apply_output_relocation",
            "mechanical_status": "pass",
            "build_status": "pass" if final_build_success else "not_required",
        },
    }
    if receipt_path.is_file():
        existing = json.loads(receipt_path.read_text(encoding="utf-8"))
        if not isinstance(existing, dict) or existing.get("receipt_id") != receipt["receipt_id"]:
            raise ValueError(f"Conflicting immutable review-apply receipt: {receipt_path}")
        return receipt_path, existing
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    temporary = receipt_path.with_name(receipt_path.name + ".tmp")
    temporary.write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(receipt_path)
    if sha256_file(evidence_path) != evidence_hash:
        raise ValueError(f"Review evidence changed while writing receipt: {evidence_path}")
    return receipt_path, receipt
