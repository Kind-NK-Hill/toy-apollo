from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping

from .phase2_review_apply_receipt import write_phase2_review_apply_receipt
from .state_store import (
    SubjectBundle,
    StateDatabaseMissingError,
    WorkspaceStateStore,
    canonical_subject_bytes,
    sha256_bytes,
    sha256_file,
    sha256_json,
    utc_now,
)


def _subject_from_review_input(
    *,
    task_id: str,
    review_input: Mapping[str, Any],
    candidate_path: Path,
    candidate_code: str,
    source_repo: str,
) -> SubjectBundle:
    raw_bundle = review_input.get("subject_bundle")
    if isinstance(raw_bundle, Mapping) and isinstance(raw_bundle.get("files"), list):
        subject = SubjectBundle.from_manifest(
            task_id=task_id,
            files=raw_bundle["files"],
            primary_path=str(raw_bundle.get("primary_path", "") or candidate_path),
            source_repo=source_repo,
            layout=f"review_{review_input.get('review_subject_kind', 'candidate')}",
            subject_kind="review_bundle",
        )
        recorded_hash = str(raw_bundle.get("bundle_hash", "") or "")
        if recorded_hash and subject.bundle_hash != recorded_hash:
            raise ValueError("Review subject bundle manifest does not match its recorded bundle hash.")
        candidate_hash = sha256_bytes(
            canonical_subject_bytes(str(candidate_path), candidate_code.encode("utf-8"))
        )
        if subject.primary_hash != candidate_hash:
            raise ValueError("Review subject bundle primary file does not match the applied candidate.")
        return subject
    return SubjectBundle.from_files(
        task_id=task_id,
        files={str(candidate_path): candidate_code},
        primary_path=str(candidate_path),
        source_repo=source_repo,
        layout=f"legacy_review_{review_input.get('review_subject_kind', 'candidate')}",
        subject_kind="review_bundle",
    )


def _output_subject(
    *,
    task_id: str,
    output_path: Path,
    runtime_root: Path,
    source_subject: SubjectBundle,
    source_repo: str,
    layout: str,
) -> SubjectBundle:
    resolved_output = output_path.resolve()
    try:
        logical_path = resolved_output.relative_to(runtime_root.resolve()).as_posix()
    except ValueError:
        logical_path = resolved_output.as_posix()
    files: dict[str, bytes] = {logical_path: resolved_output.read_bytes()}
    resolved_runtime = runtime_root.resolve()
    for item in source_subject.files:
        if item.path == source_subject.primary_path:
            continue
        support_path = Path(item.path)
        if not support_path.is_absolute():
            support_path = resolved_runtime / support_path
        support_path = support_path.resolve()
        try:
            support_path.relative_to(resolved_runtime)
        except ValueError as exc:
            raise ValueError(
                f"Reviewed support path escapes the runtime repository: {support_path}"
            ) from exc
        if not support_path.is_file():
            raise FileNotFoundError(
                f"Reviewed support file is missing during review apply: {support_path}"
            )
        files[item.path] = support_path.read_bytes()
    return SubjectBundle.from_files(
        task_id=task_id,
        files=files,
        primary_path=logical_path,
        source_repo=source_repo,
        layout=layout,
        subject_kind="reviewed_output",
        parent_subject_id=source_subject.subject_id,
    )


def _mechanically_equivalent_bundles(source: SubjectBundle, target: SubjectBundle) -> bool:
    if source.primary_hash != target.primary_hash:
        return False
    source_support = sorted(
        (item.path, item.content_sha256)
        for item in source.files
        if item.path != source.primary_path
    )
    target_support = sorted(
        (item.path, item.content_sha256)
        for item in target.files
        if item.path != target.primary_path
    )
    return source_support == target_support


def record_review_apply_state(
    *,
    settings,
    task_id: str,
    review_input: Mapping[str, Any],
    semantic_review: Mapping[str, Any],
    candidate_path: Path,
    candidate_code: str,
    success: bool,
    final_build_success: bool,
    disposition: str,
    output_path: Path | None,
    store: WorkspaceStateStore | None = None,
) -> None:
    """Project one completed review-apply operation into workspace state.

    Immutable JSON remains the evidence. SQLite stores only its hash and the
    exact review subject bundle. A clean output relocation is represented as a
    verified mechanical transformation so review coverage can cross paths
    without pretending the two observations have the same identity.
    """

    profile = str(getattr(settings, "profile", "mat") or "mat").strip().lower()
    if store is None:
        state_path = getattr(settings, "state_db_file", None)
        if state_path is None:
            return
        store = WorkspaceStateStore(Path(state_path), review_profile=profile)
        if not store.exists:
            raise StateDatabaseMissingError(
                f"Workspace state database is missing: {store.path}. "
                "Run `formalize state rebuild` before applying a review."
            )
        store.assert_integrity()
    is_mat_profile = profile == "mat"
    source_repo = "formalization_engine" if is_mat_profile else profile
    output_layout = "toy" if is_mat_profile else profile
    reviewed_head_role = "toy_reviewed" if is_mat_profile else f"{profile}_reviewed"
    subject = _subject_from_review_input(
        task_id=task_id,
        review_input=review_input,
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        source_repo=source_repo,
    )
    store.upsert_subject(subject)

    evidence_raw = str(semantic_review.get("review_result_file", "") or "").strip()
    evidence_path = Path(evidence_raw).expanduser() if evidence_raw else Path()
    if evidence_raw and not evidence_path.is_absolute():
        evidence_path = (Path(settings.phase2_prompt_packs_dir) / task_id / evidence_path).resolve()
    if not evidence_raw or not evidence_path.is_file():
        raise FileNotFoundError(f"Applied semantic review evidence is missing: {evidence_path}")
    evidence_hash = sha256_file(evidence_path)
    phase2_status = str(
        semantic_review.get("phase2_status", "")
        or semantic_review.get("task_status", "")
        or ""
    ).strip().lower()
    verdict = str(semantic_review.get("verdict", "") or "").strip().lower()
    reviewer_independence = semantic_review.get("reviewer_independence", "")
    if isinstance(reviewer_independence, Mapping):
        reviewer_independence = json.dumps(reviewer_independence, ensure_ascii=False, sort_keys=True)
    prompt_version = (
        int(review_input.get("prompt_version"))
        if str(review_input.get("prompt_version", "") or "").isdigit()
        else None
    )
    rubric_version = (
        int(review_input.get("rubric_version"))
        if str(review_input.get("rubric_version", "") or "").isdigit()
        else None
    )
    supported_prompt_versions = {
        int(value)
        for value in getattr(settings, "supported_prompt_versions", (9, 10, 11))
    }
    supported_rubric_version = int(getattr(settings, "supported_rubric_version", 9))
    current_compatible = (
        prompt_version in supported_prompt_versions
        and rubric_version == supported_rubric_version
    )
    if success and not current_compatible:
        raise ValueError(
            "A successful review apply requires metadata compatible with the active "
            f"{profile} profile: prompt in {sorted(supported_prompt_versions)} and "
            f"rubric {supported_rubric_version}."
        )
    review_id = store.record_review(
        task_id=task_id,
        subject_id=subject.subject_id,
        verdict=verdict,
        proof_class=str(semantic_review.get("proof_class", "") or ""),
        completion_class=str(semantic_review.get("completion_class", "") or ""),
        phase2_status=phase2_status,
        evidence_path=evidence_path,
        evidence_hash=evidence_hash,
        reviewer_independence=str(reviewer_independence),
        authority_scope="phase2_review_apply",
        authority_eligible=bool(
            success
            and verdict == "pass"
            and phase2_status == "pass"
            and current_compatible
        ),
        prompt_version=prompt_version,
        rubric_version=rubric_version,
        review_input_path=str(semantic_review.get("review_input_file", "") or ""),
        review_input_hash=str(
            semantic_review.get("review_input_hash", "") or sha256_json(dict(review_input))
        ),
        reviewer_backend_id=str(review_input.get("reviewer_backend_id", "") or ""),
        provenance={"projection": "live_review_apply"},
    )
    store.set_task_head(
        task_id=task_id,
        role="reviewed_subject",
        subject_id=subject.subject_id,
        detail={"disposition": disposition, "review_result_file": str(evidence_path)},
    )

    projected_subject = subject
    transformation_id = ""
    if success and output_path is not None and output_path.is_file():
        projected_subject = _output_subject(
            task_id=task_id,
            output_path=output_path,
            runtime_root=Path(settings.runtime_root),
            source_subject=subject,
            source_repo=source_repo,
            layout=output_layout,
        )
        store.upsert_subject(projected_subject)
        mechanical_status = (
            "pass" if _mechanically_equivalent_bundles(subject, projected_subject) else "fail"
        )
        transformation_id = store.record_transformation(
            task_id=task_id,
            source_subject_id=subject.subject_id,
            target_subject_id=projected_subject.subject_id,
            transformation_kind="review_apply_output_relocation",
            mechanical_status=mechanical_status,
            build_status="pass" if final_build_success else "not_required",
            evidence_path=evidence_path,
            evidence_hash=evidence_hash,
        )
        if mechanical_status != "pass":
            raise ValueError(
                "Review-apply output or one of its task-owned support files differs from the reviewed bundle."
            )
        store.set_task_head(
            task_id=task_id,
            role=reviewed_head_role,
            subject_id=projected_subject.subject_id,
            detail={"review_subject_id": subject.subject_id},
        )
        if is_mat_profile:
            store.record_integration(
                task_id=task_id,
                subject_id=projected_subject.subject_id,
                target_repo="mat",
                integration_kind="mat_promotion",
                state="ready",
                remote_freshness="local",
                detail={"source": "phase2_review_apply", "automatic_push": False},
            )

    store.record_run(
        run_id=sha256_json(
            {
                "operation": "review_apply",
                "task_id": task_id,
                "subject_id": subject.subject_id,
                "evidence_hash": evidence_hash,
            }
        ),
        task_id=task_id,
        operation="review_apply",
        status="completed" if success else "failed",
        subject_id=projected_subject.subject_id,
        artifact_path=evidence_path,
        detail={"disposition": disposition, "phase2_status": phase2_status},
        completed_at=utc_now(),
    )
    if success and output_path is not None and output_path.is_file():
        receipt_path, receipt = write_phase2_review_apply_receipt(
            settings=settings,
            task_id=task_id,
            review_input=review_input,
            semantic_review=semantic_review,
            review_subject=subject,
            projected_subject=projected_subject,
            review_id=review_id,
            transformation_id=transformation_id,
            evidence_path=evidence_path,
            evidence_hash=evidence_hash,
            disposition=disposition,
            final_build_success=final_build_success,
            reviewed_head_role=reviewed_head_role,
        )
        store.record_event(
            event_type="phase2_review_apply_receipt_written",
            task_id=task_id,
            subject_id=projected_subject.subject_id,
            evidence_path=receipt_path,
            evidence_hash=sha256_file(receipt_path),
            occurred_at=str(receipt.get("applied_at", "") or utc_now()),
            payload={
                "receipt_id": receipt.get("receipt_id", ""),
                "review_id": review_id,
                "transformation_id": transformation_id,
                "profile": profile,
            },
        )
