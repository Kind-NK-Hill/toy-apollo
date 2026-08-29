#!/usr/bin/env python3
"""Validate and apply one exact-current MAT catalog semantic review.

The reviewer prepares a canonical prompt-11/rubric-9 handoff pack and writes
its result without touching SQLite.  This command is the serialized apply
boundary: it re-derives the pinned MAT task-owned bundle from Git, validates all
bound artifacts, normalizes the result through the Phase 2 decision code, and
records either a non-authoritative failure or an exact-bundle PASS.  A clean
PASS emits the immutable receipt schema understood by ``state rebuild``.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_review_decision import evaluate_semantic_review_result
from src.toy_apollo.phase2_semantic_review import (
    _validate_review_input_internal_binding,
    render_semantic_review_prompt,
    render_semantic_review_report,
)
from src.toy_apollo.state_reconcile import git_file_at_ref
from src.toy_apollo.state_exact_build_batch import (
    ExactBuildBatchError,
    catalog_owned_build_modules,
    validate_current_exact_build_receipt,
)
from src.toy_apollo.state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
    utc_now,
)
from src.toy_apollo.task_catalog import TaskCatalog, load_catalog


RECEIPT_SCHEMA = "mat.rubric78.review-apply-receipt.v1"
FAILURE_RECEIPT_SCHEMA = "mat.catalog.review-apply-failure-receipt.v1"
AUTHORITY_SCOPE = "mat_final_exact_bundle_review"
REVIEW_SUPPLEMENT_EVIDENCE_SCHEMA = "mat.catalog.review-supplement-evidence.v1"


class ApplyError(RuntimeError):
    pass


def _read_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ApplyError(f"Invalid JSON {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ApplyError(f"JSON must contain an object: {path}")
    return payload


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(
        json.dumps(dict(payload), indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _git_text(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise ApplyError(f"Git command failed: git {' '.join(args)}: {detail}")
    return completed.stdout.decode("utf-8", errors="replace").strip()


def _catalog_subject(catalog: TaskCatalog, *, task_id: str, mat_repo: Path) -> SubjectBundle:
    task = next((item for item in catalog.tasks if item.task_id == task_id), None)
    if task is None:
        raise ApplyError(f"Task is not in the pinned catalog: {task_id}")
    paths = catalog.owned_paths(task_id)
    if not paths or task.primary_path not in paths:
        raise ApplyError(f"Catalog has no complete task-owned MAT bundle for {task_id}")
    files = {
        path: git_file_at_ref(mat_repo, catalog.mat_commit, path)
        for path in paths
    }
    return SubjectBundle.from_files(
        task_id=task_id,
        files=files,
        primary_path=task.primary_path,
        source_repo="mat",
        source_commit=catalog.mat_commit,
        layout="mat",
        subject_kind="catalog_git_bundle",
    )


def _candidate_subject(
    catalog: TaskCatalog,
    *,
    task_id: str,
    candidate_root: Path,
    parent: SubjectBundle,
) -> SubjectBundle:
    task = next((item for item in catalog.tasks if item.task_id == task_id), None)
    if task is None:
        raise ApplyError(f"Task is not in the pinned catalog: {task_id}")
    paths = catalog.owned_paths(task_id)
    if not paths or task.primary_path not in paths:
        raise ApplyError(f"Catalog has no complete task-owned MAT bundle for {task_id}")
    files: dict[str, bytes] = {}
    for path in paths:
        candidate_path = candidate_root / Path(path)
        if not candidate_path.is_file():
            raise ApplyError(f"Candidate task-owned file is missing: {candidate_path}")
        files[path] = candidate_path.read_bytes()
    return SubjectBundle.from_files(
        task_id=task_id,
        files=files,
        primary_path=task.primary_path,
        source_repo="mat",
        source_commit=f"{catalog.mat_commit}+local-candidate",
        layout="mat",
        subject_kind="mat_candidate_bundle",
        parent_subject_id=parent.subject_id,
    )


def _path_from_metadata(pack_dir: Path, metadata: Mapping[str, Any], key: str) -> Path:
    raw = str(metadata.get(key, "") or "")
    if not raw:
        raise ApplyError(f"Pack metadata is missing {key}")
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = pack_dir / path
    path = path.resolve()
    if not path.is_file():
        raise ApplyError(f"Bound artifact is missing: {key}={path}")
    return path


def _assert_hash(path: Path, expected: Any, label: str) -> None:
    expected_text = str(expected or "")
    if not expected_text or sha256_file(path) != expected_text:
        raise ApplyError(f"Bound artifact hash mismatch: {label}")


def _validate_build_receipt(
    path: Path,
    *,
    metadata: Mapping[str, Any],
    subject: SubjectBundle,
    catalog: TaskCatalog,
) -> dict[str, Any]:
    if metadata.get("schema") == "mat.catalog.exact-review-pack.v1":
        checkout_text = str(metadata.get("build_checkout", "") or "")
        checkout = Path(checkout_text)
        if not checkout.is_absolute():
            raise ApplyError("Pack build_checkout must be absolute")
        primary_modules, owned_modules = catalog_owned_build_modules(
            catalog, [subject.task_id]
        )
        try:
            return validate_current_exact_build_receipt(
                path,
                subject=subject,
                primary_module=primary_modules[subject.task_id],
                task_modules=owned_modules[subject.task_id],
                commit=catalog.mat_commit,
                checkout=checkout,
            )
        except ExactBuildBatchError as exc:
            raise ApplyError(f"Exact build receipt is invalid: {exc}") from exc

    receipt = _read_json(path)
    if (
        metadata.get("schema") != "mat.catalog.candidate-exact-review-pack.v1"
        or receipt.get("schema") != "mat.catalog.candidate-exact-build.v1"
    ):
        raise ApplyError("Unsupported review pack/build receipt schema pairing")
    focused = receipt.get("focused_build")
    scan = receipt.get("forbidden_token_scan")
    if isinstance(focused, Mapping):
        build_ok = int(focused.get("exit_code", -1)) == 0
    else:
        build_ok = receipt.get("success") is True and int(receipt.get("exit_code", -1)) == 0
    if not build_ok:
        raise ApplyError("Focused MAT build receipt is not successful")
    if isinstance(scan, Mapping):
        findings = scan.get("findings")
        if int(scan.get("exit_code", -1)) != 0 or not isinstance(findings, Mapping) or findings:
            raise ApplyError("Forbidden-token scan is missing or not clean")
    else:
        findings = receipt.get("forbidden_findings")
        if not isinstance(findings, Mapping) or findings:
            raise ApplyError("Forbidden-token scan is missing or not clean")
    for field, expected in (
        ("task_id", subject.task_id),
        ("commit", subject.source_commit),
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
        ("primary_path", subject.primary_path),
    ):
        if str(receipt.get(field, "") or "") != expected:
            raise ApplyError(f"Build receipt exact-subject field mismatch: {field}")
    if receipt.get("subject_files") != subject.manifest():
        raise ApplyError("Candidate build receipt subject manifest mismatch")
    equivalence = receipt.get("lean_tree_equivalence")
    if isinstance(equivalence, Mapping):
        if (
            str(equivalence.get("target_commit", "") or "") != subject.source_commit
            or list(equivalence.get("changed_lean_files", []))
        ):
            raise ApplyError("Build checkout is not Lean-tree-equivalent to the reviewed MAT commit")
    return receipt


def _validate_build_receipt_provenance(
    *,
    metadata: Mapping[str, Any],
    review_input: Mapping[str, Any],
    actual_build_hash: str,
) -> None:
    mode = str(metadata.get("build_receipt_mode", "") or "")
    if mode not in {"built_during_prepare", "reused_prebuilt"}:
        raise ApplyError("Pack build_receipt_mode is missing or invalid")
    declared_build_hash = str(metadata.get("build_result_hash", "") or "")
    if declared_build_hash != actual_build_hash:
        raise ApplyError("Pack-local build receipt hash mismatch")
    basis = review_input.get("review_basis")
    if not isinstance(basis, Mapping):
        raise ApplyError("Review input lacks build receipt provenance")
    if basis.get("build_receipt_mode") != mode:
        raise ApplyError("Review input build receipt mode mismatch")
    if basis.get("build_checkout") != metadata.get("build_checkout"):
        raise ApplyError("Review input build checkout binding mismatch")
    external = basis.get("external_subject")
    if not isinstance(external, Mapping):
        raise ApplyError("Review input lacks pack-local build receipt binding")
    if (
        external.get("focused_build_receipt") != metadata.get("build_result_file")
        or external.get("focused_build_receipt_hash") != declared_build_hash
    ):
        raise ApplyError("Review input pack-local build receipt binding mismatch")
    source_path = str(metadata.get("prebuilt_exact_build_receipt_source", "") or "")
    source_hash = str(
        metadata.get("prebuilt_exact_build_receipt_source_hash", "") or ""
    )
    if mode == "reused_prebuilt":
        if not Path(source_path).is_absolute():
            raise ApplyError("Prebuilt exact-build source path must be absolute")
        if source_hash != declared_build_hash:
            raise ApplyError("Prebuilt source/copy build receipt hash mismatch")
        if (
            basis.get("prebuilt_exact_build_receipt_source") != source_path
            or basis.get("prebuilt_exact_build_receipt_source_hash") != source_hash
        ):
            raise ApplyError("Review input prebuilt receipt provenance mismatch")
    elif any(
        key in metadata or key in basis
        for key in (
            "prebuilt_exact_build_receipt_source",
            "prebuilt_exact_build_receipt_source_hash",
        )
    ):
        raise ApplyError("Built-during-prepare pack contains stray prebuilt provenance")


def _render_review_supplement_context(
    supplement: Mapping[str, Any], *, file_hash: str, content_hash: str
) -> str:
    rendered = json.dumps(dict(supplement), indent=2, ensure_ascii=False, sort_keys=True)
    return "\n".join(
        [
            "# Bound review supplement evidence",
            "",
            "This material is review context only. It does not grant a verdict or expand task ownership.",
            f"- Supplement file SHA-256: `{file_hash}`",
            f"- Supplement content SHA-256: `{content_hash}`",
            "- Historical risks marked `resolved` or `superseded` below must be evaluated using the embedded evidence, not silently carried forward.",
            "",
            "~~~~json",
            rendered,
            "~~~~",
        ]
    )


def _validate_review_supplement_binding(
    *,
    pack_dir: Path,
    metadata: Mapping[str, Any],
    review_input: Mapping[str, Any],
    subject: SubjectBundle,
) -> dict[str, Any] | None:
    keys = {
        "review_supplement_file",
        "review_supplement_hash",
        "review_supplement_content_hash",
    }
    present = {key for key in keys if str(metadata.get(key, "") or "")}
    if not present:
        return None
    if present != keys:
        raise ApplyError("Pack metadata has an incomplete review supplement binding")
    supplement_path = _path_from_metadata(pack_dir, metadata, "review_supplement_file")
    _assert_hash(
        supplement_path,
        metadata.get("review_supplement_hash"),
        "review_supplement_file",
    )
    supplement = _read_json(supplement_path)
    content_hash = sha256_json(supplement)
    if content_hash != str(metadata.get("review_supplement_content_hash", "") or ""):
        raise ApplyError("Review supplement content hash does not match pack metadata")
    for field, expected in (
        ("schema", REVIEW_SUPPLEMENT_EVIDENCE_SCHEMA),
        ("task_id", subject.task_id),
        ("target_commit", subject.source_commit),
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
        ("primary_path", subject.primary_path),
    ):
        if str(supplement.get(field, "") or "") != expected:
            raise ApplyError(f"Review supplement exact-subject field mismatch: {field}")

    basis = review_input.get("review_basis")
    if not isinstance(basis, Mapping):
        raise ApplyError("Review input lacks a review basis for the supplement")
    if basis.get("review_supplement") != supplement:
        raise ApplyError("Review input basis does not embed the bound review supplement")
    file_hash = str(metadata.get("review_supplement_hash", "") or "")
    for field, expected in (
        ("review_supplement_file", str(supplement_path)),
        ("review_supplement_file_sha256", file_hash),
        ("review_supplement_content_sha256", content_hash),
    ):
        if str(basis.get(field, "") or "") != expected:
            raise ApplyError(f"Review input supplement basis mismatch: {field}")
    expected_context = _render_review_supplement_context(
        supplement,
        file_hash=file_hash,
        content_hash=content_hash,
    )
    context = str(review_input.get("review_context_markdown", "") or "")
    if expected_context not in context:
        raise ApplyError("Review input context does not embed the bound review supplement")
    return supplement


def _validate_pack(
    *,
    pack_dir: Path,
    metadata: Mapping[str, Any],
    subject: SubjectBundle,
    catalog: TaskCatalog,
    require_expected_result: bool = True,
) -> tuple[dict[str, Any], Path, Path]:
    for field, expected in (
        ("task_id", subject.task_id),
        ("commit", subject.source_commit),
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
        ("primary_path", subject.primary_path),
    ):
        if str(metadata.get(field, "") or "") != expected:
            raise ApplyError(f"Pack exact-subject field mismatch: {field}")
    if metadata.get("subject_files") != subject.manifest():
        raise ApplyError("Pack task-owned subject manifest does not match the current catalog bundle")

    raw_build_path = Path(str(metadata.get("build_result_file", "") or ""))
    if not raw_build_path.is_absolute():
        raise ApplyError("Pack build_result_file must be absolute")
    build_path = _path_from_metadata(pack_dir, metadata, "build_result_file")
    _assert_hash(build_path, metadata.get("build_result_hash"), "build_result_file")
    actual_build_hash = sha256_file(build_path)
    _validate_build_receipt(
        build_path, metadata=metadata, subject=subject, catalog=catalog
    )

    input_path = _path_from_metadata(pack_dir, metadata, "review_input_file")
    review_input = _read_json(input_path)
    expected_input_hash = str(metadata.get("review_input_hash", "") or "")
    if sha256_json(review_input) != expected_input_hash:
        raise ApplyError("Review input hash does not match pack metadata")
    _validate_build_receipt_provenance(
        metadata=metadata,
        review_input=review_input,
        actual_build_hash=actual_build_hash,
    )
    internal_error = _validate_review_input_internal_binding(review_input)
    if internal_error:
        raise ApplyError(f"Review input internal binding is invalid: {internal_error}")
    if int(review_input.get("prompt_version", 0) or 0) != 11:
        raise ApplyError("Exact-current catalog review must use prompt version 11")
    if int(review_input.get("rubric_version", 0) or 0) != 9:
        raise ApplyError("Exact-current catalog review must use rubric version 9")
    bundle = review_input.get("subject_bundle")
    if not isinstance(bundle, Mapping):
        raise ApplyError("Review input lacks a bound subject bundle")
    for field, expected in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
        ("primary_path", subject.primary_path),
        ("source_commit", subject.source_commit),
    ):
        if str(bundle.get(field, "") or "") != expected:
            raise ApplyError(f"Review input subject bundle mismatch: {field}")
    if bundle.get("files") != subject.manifest():
        raise ApplyError("Review input subject files do not match the current catalog bundle")
    _validate_review_supplement_binding(
        pack_dir=pack_dir,
        metadata=metadata,
        review_input=review_input,
        subject=subject,
    )

    request_path = _path_from_metadata(pack_dir, metadata, "review_request_file")
    _assert_hash(request_path, metadata.get("review_request_hash"), "review_request_file")
    request = _read_json(request_path)
    for field, expected in (
        ("task_id", subject.task_id),
        ("review_input_hash", expected_input_hash),
        ("review_subject_hash", subject.primary_hash),
        ("prompt_version", 11),
        ("rubric_version", 9),
    ):
        if request.get(field) != expected:
            raise ApplyError(f"Review request binding mismatch: {field}")

    prompt_path = _path_from_metadata(pack_dir, metadata, "review_prompt_file")
    _assert_hash(prompt_path, metadata.get("review_prompt_hash"), "review_prompt_file")
    if prompt_path.read_text(encoding="utf-8").strip() != render_semantic_review_prompt(review_input).strip():
        raise ApplyError("Review prompt is not an exact render of the bound input")
    context_path = _path_from_metadata(pack_dir, metadata, "review_context_file")
    _assert_hash(context_path, metadata.get("review_context_hash"), "review_context_file")
    if context_path.read_text(encoding="utf-8").strip() != str(
        review_input.get("review_context_markdown", "")
    ).strip():
        raise ApplyError("Review context does not match the bound input")

    template_path = _path_from_metadata(
        pack_dir, metadata, "review_result_template_file"
    )
    _assert_hash(
        template_path,
        metadata.get("review_result_template_hash"),
        "review_result_template_file",
    )

    result_text = str(metadata.get("expected_review_result_file", "") or "")
    result_path = Path(result_text).expanduser()
    if not result_path.is_absolute():
        raise ApplyError("Pack expected_review_result_file must be absolute")
    result_path = result_path.resolve()
    if result_path.exists() and not result_path.is_file():
        raise ApplyError("Expected review result path is not a regular file")
    if require_expected_result and not result_path.is_file():
        raise ApplyError(f"Bound artifact is missing: expected_review_result_file={result_path}")
    return review_input, input_path, result_path


def _validate_prepare_complete_pack(
    *,
    pack_dir: Path,
    metadata: Mapping[str, Any],
    subject: SubjectBundle,
    catalog: TaskCatalog,
) -> tuple[dict[str, Any], Path, Path]:
    """Validate a complete prepared pack while allowing review result absence."""

    return _validate_pack(
        pack_dir=pack_dir,
        metadata=metadata,
        subject=subject,
        catalog=catalog,
        require_expected_result=False,
    )


def _revalidate_current_subject_before_state_mutation(
    *,
    catalog: TaskCatalog,
    mat_repo: Path,
    task_id: str,
    expected_parent: SubjectBundle,
) -> None:
    if _git_text(mat_repo, "rev-parse", "origin/main") != catalog.mat_commit:
        raise ApplyError("MAT origin/main changed before state mutation")
    fresh = _catalog_subject(catalog, task_id=task_id, mat_repo=mat_repo)
    fields = (
        "task_id",
        "source_commit",
        "subject_id",
        "bundle_hash",
        "primary_hash",
        "primary_path",
    )
    if any(getattr(fresh, field) != getattr(expected_parent, field) for field in fields):
        raise ApplyError("Current MAT subject changed before state mutation")
    if fresh.manifest() != expected_parent.manifest():
        raise ApplyError("Current MAT subject files changed before state mutation")


def apply_review(
    *,
    task_id: str,
    pack_dir: Path,
    workspace_root: Path,
    runtime_root: Path,
    state_path: Path,
    candidate_root: Path | None = None,
) -> dict[str, Any]:
    mat_repo = (workspace_root / "MAT3280-formalization-output").resolve()
    catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    resolved_ref = _git_text(mat_repo, "rev-parse", "origin/main")
    if resolved_ref != catalog.mat_commit:
        raise ApplyError(
            f"Pinned catalog MAT commit is not current origin/main: {catalog.mat_commit} != {resolved_ref}"
        )
    parent_subject = _catalog_subject(catalog, task_id=task_id, mat_repo=mat_repo)
    subject = (
        parent_subject
        if candidate_root is None
        else _candidate_subject(
            catalog,
            task_id=task_id,
            candidate_root=candidate_root,
            parent=parent_subject,
        )
    )
    metadata_path = (pack_dir / "mat_exact_subject.json").resolve()
    metadata = _read_json(metadata_path)
    review_input, input_path, result_path = _validate_pack(
        pack_dir=pack_dir,
        metadata=metadata,
        subject=subject,
        catalog=catalog,
    )

    raw_result = _read_json(result_path)
    # Reviewers may run the canonical normalizer before handoff.  Its persisted
    # decision envelope keeps the actual semantic result under ``result``;
    # validate that inner result again against the exact current input here.
    if (
        raw_result.get("schema_version") == "phase2.review_decision.v1"
        and isinstance(raw_result.get("result"), Mapping)
    ):
        raw_result = dict(raw_result["result"])
    decision = evaluate_semantic_review_result(
        raw_result,
        review_input=review_input,
        runner_metadata={
            "status": "mat_catalog_exact_bundle_apply",
            "campaign_id": metadata.get("campaign_id", "modern_catalog_gap_closure_20260807"),
            "metadata_file": str(metadata_path),
        },
    )
    if not decision.is_semantic_verdict or decision.task_status_projection is None:
        reason = str(decision.result.get("normalization_reason", "") or "invalid semantic result")
        raise ApplyError(reason)
    raw_backup = result_path.with_name(result_path.stem + "_raw.json")
    if not raw_backup.exists():
        shutil.copyfile(result_path, raw_backup)
    normalized = decision.result
    _write_json(result_path, normalized)
    report_path = result_path.with_name(
        result_path.name.replace("result", "report").replace(".json", ".md")
    )
    report_path.write_text(
        render_semantic_review_report(normalized).rstrip()
        + "\n\n## Exact current MAT catalog binding\n\n"
        + f"- Commit: `{subject.source_commit}`\n"
        + f"- Subject ID: `{subject.subject_id}`\n"
        + f"- Bundle hash: `{subject.bundle_hash}`\n"
        + f"- Primary hash: `{subject.primary_hash}`\n",
        encoding="utf-8",
    )

    phase2_status = decision.task_status_projection.task_status
    clean_pass = bool(decision.is_clean_pass)
    independence = normalized.get("reviewer_independence")
    if not isinstance(independence, Mapping):
        raise ApplyError("Normalized semantic result lacks structured reviewer independence")
    if independence.get("read_only") is not True or independence.get("did_edit_candidate") is not False:
        raise ApplyError("Reviewer independence attestation is invalid")

    store = WorkspaceStateStore(state_path)
    store.assert_integrity()
    current_report = store.task_report(task_id)
    current_head = (current_report.get("heads") or {}).get("mat_main") or {}
    if (
        str(current_head.get("subject_id", "") or "") != subject.subject_id
        or str(current_head.get("bundle_hash", "") or "") != subject.bundle_hash
    ) and candidate_root is None:
        raise ApplyError("Live SQLite MAT head is stale relative to the exact reviewed catalog bundle")
    if candidate_root is not None and (
        str(current_head.get("subject_id", "") or "") != parent_subject.subject_id
        or str(current_head.get("bundle_hash", "") or "") != parent_subject.bundle_hash
    ):
        raise ApplyError("Live SQLite MAT head is stale relative to the repaired candidate parent")
    _revalidate_current_subject_before_state_mutation(
        catalog=catalog,
        mat_repo=mat_repo,
        task_id=task_id,
        expected_parent=parent_subject,
    )
    store.upsert_subject(subject)
    evidence_hash = sha256_file(result_path)
    review_id = store.record_review(
        task_id=task_id,
        subject_id=subject.subject_id,
        verdict=str(normalized.get("verdict", "") or ""),
        proof_class=str(normalized.get("proof_class", "") or ""),
        completion_class=str(normalized.get("completion_class", "") or ""),
        phase2_status=phase2_status,
        evidence_path=result_path,
        evidence_hash=evidence_hash,
        reviewer_independence=json.dumps(dict(independence), ensure_ascii=False, sort_keys=True),
        authority_scope=AUTHORITY_SCOPE,
        authority_eligible=clean_pass,
        prompt_version=11,
        rubric_version=9,
        review_input_path=input_path,
        review_input_hash=sha256_json(review_input),
        reviewer_backend_id=str(normalized.get("reviewer_backend_id", "") or ""),
        provenance={
            "projection": "serialized_mat_catalog_review_apply",
            "metadata_path": str(metadata_path),
            "campaign_id": metadata.get("campaign_id", "modern_catalog_gap_closure_20260807"),
        },
    )
    store.set_task_head(
        task_id=task_id,
        role="mat_main" if candidate_root is None else "mat_candidate",
        subject_id=subject.subject_id,
        detail={
            "ref": "origin/main" if candidate_root is None else "local-candidate",
            "commit": subject.source_commit,
            "review_id": review_id,
            "campaign_id": metadata.get("campaign_id", "modern_catalog_gap_closure_20260807"),
        },
    )
    applied_at = utc_now()
    store.record_run(
        task_id=task_id,
        operation=(
            "mat_catalog_exact_review_apply"
            if candidate_root is None
            else "mat_catalog_candidate_exact_review_apply"
        ),
        status="completed" if clean_pass else "failed",
        campaign_id=str(metadata.get("campaign_id", "modern_catalog_gap_closure_20260807")),
        subject_id=subject.subject_id,
        artifact_path=result_path,
        detail={"review_id": review_id, "phase2_status": phase2_status},
        completed_at=applied_at,
    )
    coverage = store.review_coverage(subject.subject_id)
    exact_bundle_covered = bool(
        coverage
        and coverage.get("coverage_kind") == "exact_bundle"
        and coverage.get("covered_subject_id") == subject.subject_id
    )
    receipt = {
        "schema": RECEIPT_SCHEMA if clean_pass else FAILURE_RECEIPT_SCHEMA,
        "campaign_id": metadata.get("campaign_id", "modern_catalog_gap_closure_20260807"),
        "task_id": task_id,
        "attempt": int(metadata.get("attempt", normalized.get("attempt", 1)) or 1),
        "dependency_wave": metadata.get("dependency_wave", -1),
        "review_reason": metadata.get("review_reason", "all_catalog_modern_gap_closure"),
        "invalidated_by": "",
        "commit": subject.source_commit,
        "subject_id": subject.subject_id,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "review_input_hash": sha256_json(review_input),
        "review_result_file": str(result_path),
        "review_result_hash": evidence_hash,
        "review_report_file": str(report_path),
        "review_id": review_id,
        "verdict": normalized.get("verdict", ""),
        "proof_class": normalized.get("proof_class", ""),
        "completion_class": normalized.get("completion_class", ""),
        "phase2_status": phase2_status,
        "clean_pass": clean_pass,
        "exact_bundle_covered": exact_bundle_covered,
        "authority_eligible": clean_pass,
        "applied_at": applied_at,
    }
    attempt = int(receipt["attempt"])
    receipt_name = (
        f"review_apply_receipt_v{attempt}.json"
        if clean_pass
        else f"review_apply_failure_receipt_v{attempt}.json"
    )
    receipt_path = pack_dir / receipt_name
    _write_json(receipt_path, receipt)
    if clean_pass:
        if not exact_bundle_covered:
            raise ApplyError("Clean PASS did not produce exact-current MAT coverage")
        _write_json(pack_dir / "review_apply_receipt.json", receipt)
    return {**receipt, "receipt_file": str(receipt_path)}


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Apply one independently reviewed exact-current MAT catalog bundle"
    )
    parser.add_argument("--task", required=True)
    parser.add_argument("--pack-dir", type=Path, required=True)
    parser.add_argument("--workspace-root", type=Path, default=REPO_ROOT.parent)
    parser.add_argument("--runtime-root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--state",
        type=Path,
        default=REPO_ROOT.parent / "toy-apollo-artifacts" / "state.sqlite3",
    )
    parser.add_argument(
        "--candidate-root",
        type=Path,
        help="Apply a review for an exact repaired candidate from this local MAT worktree",
    )
    args = parser.parse_args()
    result = apply_review(
        task_id=args.task,
        pack_dir=args.pack_dir.resolve(),
        workspace_root=args.workspace_root.resolve(),
        runtime_root=args.runtime_root.resolve(),
        state_path=args.state.resolve(),
        candidate_root=args.candidate_root.resolve() if args.candidate_root else None,
    )
    print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ApplyError as exc:
        print(f"MAT_CATALOG_REVIEW_APPLY_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
