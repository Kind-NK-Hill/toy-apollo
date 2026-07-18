from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping

from src.block_id_naming import canonicalize_block_id

from .state_reconcile import refresh_workspace_state
from .state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
    utc_now,
)


TASK_ID_RE = re.compile(r"^(?:def|thm|ex|prob|rem|intro)_\d+(?:_\d+)+$", re.IGNORECASE)


@dataclass
class MigrationReport:
    database: str
    backup: str = ""
    ledgers: int = 0
    ledger_tasks: int = 0
    reviews: int = 0
    review_bindings: int = 0
    external_pr_receipts: int = 0
    sidecar_rows: int = 0
    skipped: int = 0
    local_subjects: int = 0
    remote_subjects: int = 0
    warnings: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)

    def as_dict(self) -> dict[str, Any]:
        return {
            "database": self.database,
            "backup": self.backup,
            "ledgers": self.ledgers,
            "ledger_tasks": self.ledger_tasks,
            "reviews": self.reviews,
            "review_bindings": self.review_bindings,
            "external_pr_receipts": self.external_pr_receipts,
            "sidecar_rows": self.sidecar_rows,
            "skipped": self.skipped,
            "local_subjects": self.local_subjects,
            "remote_subjects": self.remote_subjects,
            "warnings": list(self.warnings),
            "errors": list(self.errors),
        }


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _file_time(path: Path) -> str:
    return datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc).isoformat()


def _looks_like_task_id(value: str) -> bool:
    return bool(TASK_ID_RE.match(value))


def _task_id(payload: Mapping[str, Any], fallback: str = "") -> str:
    candidates = [
        payload.get("task_id"),
        payload.get("block_id"),
        payload.get("canonical_block_id"),
    ]
    task = payload.get("task")
    if isinstance(task, Mapping):
        candidates.extend([task.get("block_id"), task.get("task_id")])
    task_review = payload.get("task_review")
    if isinstance(task_review, Mapping):
        candidates.extend([task_review.get("task_id"), task_review.get("block_id")])
    candidates.append(fallback)
    for candidate in candidates:
        canonical = canonicalize_block_id(str(candidate or ""))
        if canonical and _looks_like_task_id(canonical):
            return canonical
    return ""


def _review_payloads(payload: Any) -> Iterator[tuple[str, Mapping[str, Any], Mapping[str, Any]]]:
    if not isinstance(payload, Mapping):
        return
    direct_task = _task_id(payload)
    direct_verdict = str(payload.get("verdict", "") or "")
    if direct_task and direct_verdict:
        yield direct_task, payload, payload
        return
    for key, value in payload.items():
        if not isinstance(value, Mapping):
            continue
        task_id = _task_id(value, fallback=str(key))
        if not task_id:
            continue
        task_review = value.get("task_review")
        if isinstance(task_review, Mapping) and task_review.get("verdict"):
            yield task_id, task_review, value
        elif value.get("verdict"):
            yield task_id, value, value


def _candidate_hash(review: Mapping[str, Any], wrapper: Mapping[str, Any]) -> str:
    for payload in (review, wrapper):
        for key in (
            "candidate_hash",
            "review_subject_hash",
            "subject_hash",
            "latest_applied_review_subject_hash",
        ):
            value = str(payload.get(key, "") or "").strip()
            if value:
                return value
        candidate = payload.get("candidate")
        if isinstance(candidate, Mapping):
            value = str(candidate.get("hash", "") or "").strip()
            if value:
                return value
        binding = payload.get("mechanical_subject_binding")
        if isinstance(binding, Mapping):
            value = str(binding.get("norm_hash", "") or "").strip()
            if value:
                return f"normalized:{value}"
    return ""


def _candidate_path(review: Mapping[str, Any], wrapper: Mapping[str, Any]) -> str:
    for payload in (review, wrapper):
        for key in ("review_subject_file", "subject_file", "candidate_file"):
            value = str(payload.get(key, "") or "").strip()
            if value:
                return value
        candidate = payload.get("candidate")
        if isinstance(candidate, Mapping):
            value = str(candidate.get("file", "") or "").strip()
            if value:
                return value
    return ""


def _authority_scope(path: Path) -> str:
    normalized = path.as_posix().lower()
    if "full_review_harness" in normalized or path.name.startswith(("state_ch", "reviews_ch")):
        return "historical_sidecar"
    if "/gate2/" in normalized:
        return "gate2_exact_evidence"
    if "semantic_review_result" in path.name.lower() and "phase2_prompt_packs" in normalized:
        return "phase2_review_artifact"
    return "historical_review"


def _resolved_receipt_path(raw: str, ledger_path: Path) -> str:
    if not raw.strip():
        return ""
    path = Path(raw)
    if not path.is_absolute():
        path = ledger_path.parent / path
    return str(path.resolve())


def _applied_review_receipts(ledger_paths: Iterable[Path]) -> dict[str, list[dict[str, str]]]:
    receipts: dict[str, list[dict[str, str]]] = {}
    for ledger_path in ledger_paths:
        try:
            payload = _read_json(ledger_path)
        except Exception:
            continue
        tasks = payload.get("tasks", {}) if isinstance(payload, Mapping) else {}
        if not isinstance(tasks, Mapping):
            continue
        for raw_task_id, raw_record in tasks.items():
            if not isinstance(raw_record, Mapping):
                continue
            task_id = canonicalize_block_id(str(raw_task_id))
            result_file = str(raw_record.get("latest_applied_review_result_file", "") or "")
            receipt = {
                "result_file": _resolved_receipt_path(result_file, ledger_path),
                "result_hash": str(raw_record.get("latest_applied_review_result_hash", "") or ""),
                "input_hash": str(raw_record.get("latest_applied_review_input_hash", "") or ""),
                "subject_hash": str(raw_record.get("latest_applied_review_subject_hash", "") or ""),
                "post_basis_hash": str(raw_record.get("latest_applied_review_post_basis_hash", "") or ""),
                "subject_kind": str(raw_record.get("latest_applied_review_subject_kind", "") or ""),
                "ledger_file": str(ledger_path.resolve()),
            }
            if task_id and all(
                receipt[key]
                for key in ("result_file", "result_hash", "input_hash", "subject_hash", "post_basis_hash", "subject_kind")
            ):
                receipts.setdefault(task_id, []).append(receipt)
    return receipts


def _matches_applied_receipt(
    *,
    path: Path,
    payload: Any,
    task_id: str,
    review: Mapping[str, Any],
    candidate_hash: str,
    receipts: Mapping[str, list[dict[str, str]]],
) -> bool:
    result_hash = sha256_json(payload)
    review_input_hash = str(review.get("review_input_hash", "") or "")
    resolved_path = str(path.resolve())
    return any(
        receipt["result_file"] == resolved_path
        and receipt["result_hash"] == result_hash
        and receipt["input_hash"] == review_input_hash
        and receipt["subject_hash"] == candidate_hash
        for receipt in receipts.get(task_id, [])
    )


def _source_repo(path: Path) -> str:
    normalized = path.as_posix().lower()
    if "kenneth" in normalized:
        return "kenneth"
    if "mat3280" in normalized:
        return "mat"
    return "toy_apollo"


def _review_files(roots: Iterable[Path], *, always_include: Iterable[Path] = ()) -> Iterator[Path]:
    selected: set[Path] = {
        path.resolve() for path in always_include if path.is_file()
    }
    latest_versioned: dict[Path, tuple[int, Path]] = {}
    latest_alias: dict[Path, tuple[int, int, Path]] = {}
    for root in roots:
        if not root.exists():
            continue
        for directory, names, files in os.walk(root):
            names[:] = [name for name in names if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}]
            for filename in files:
                lowered = filename.lower()
                if "template" in lowered or not lowered.endswith(".json") or not (
                    "semantic_review_result" in lowered or lowered.startswith("reviews_ch")
                ):
                    continue
                path = Path(directory) / filename
                resolved = path.resolve()
                if lowered.startswith("reviews_ch"):
                    selected.add(resolved)
                    continue
                version_match = re.search(r"_v(\d+)\.json$", lowered)
                directory_key = resolved.parent
                if version_match:
                    version = int(version_match.group(1))
                    current = latest_versioned.get(directory_key)
                    if current is None or version > current[0]:
                        latest_versioned[directory_key] = (version, resolved)
                    continue
                is_canonical_alias = 1 if lowered == "semantic_review_result.json" else 0
                try:
                    modified = resolved.stat().st_mtime_ns
                except OSError:
                    modified = 0
                current_alias = latest_alias.get(directory_key)
                rank = (is_canonical_alias, modified)
                if current_alias is None or rank > current_alias[:2]:
                    latest_alias[directory_key] = (rank[0], rank[1], resolved)
    selected.update(path for _version, path in latest_versioned.values())
    selected.update(path for _rank, _mtime, path in latest_alias.values())
    yield from sorted(selected)


def _sidecar_state_files(roots: Iterable[Path]) -> Iterator[Path]:
    seen: set[Path] = set()
    for root in roots:
        if not root.exists():
            continue
        for directory, names, files in os.walk(root):
            names[:] = [name for name in names if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}]
            for filename in files:
                if not filename.lower().startswith("state_ch") or not filename.lower().endswith(".json"):
                    continue
                path = Path(directory) / filename
                resolved = path.resolve()
                if resolved in seen:
                    continue
                seen.add(resolved)
                yield path


def _workspace_review_binding_files(roots: Iterable[Path]) -> Iterator[Path]:
    seen: set[Path] = set()
    for root in roots:
        if not root.exists():
            continue
        for directory, names, files in os.walk(root):
            names[:] = [
                name
                for name in names
                if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}
            ]
            for filename in files:
                lowered = filename.lower()
                if not lowered.startswith("workspace_review_binding_") or not lowered.endswith(".json"):
                    continue
                path = (Path(directory) / filename).resolve()
                if path in seen:
                    continue
                seen.add(path)
                yield path


def _external_pr_review_receipt_files(roots: Iterable[Path]) -> Iterator[Path]:
    seen: set[Path] = set()
    for root in roots:
        if not root.exists():
            continue
        for directory, names, files in os.walk(root):
            names[:] = [
                name
                for name in names
                if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}
            ]
            if "external_pr_review_apply_receipt.json" not in files:
                continue
            path = (Path(directory) / "external_pr_review_apply_receipt.json").resolve()
            if path in seen:
                continue
            seen.add(path)
            yield path


def _ledger_files(roots: Iterable[Path]) -> Iterator[Path]:
    seen: set[Path] = set()
    for root in roots:
        if not root.exists():
            continue
        for directory, names, files in os.walk(root):
            names[:] = [name for name in names if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}]
            if "project_ledger.json" not in files:
                continue
            path = Path(directory) / "project_ledger.json"
            resolved = path.resolve()
            if resolved in seen:
                continue
            seen.add(resolved)
            yield path


def import_legacy_ledger(store: WorkspaceStateStore, path: Path, report: MigrationReport) -> None:
    if store.import_is_current(path):
        report.skipped += 1
        return
    payload = _read_json(path)
    if not isinstance(payload, Mapping):
        raise ValueError("ledger root is not a JSON object")
    campaign_root = path.parent.resolve()
    campaign_id = f"legacy:{sha256_json(str(campaign_root).lower())[:20]}"
    store.import_campaign_ledger(
        campaign_id=campaign_id,
        artifact_root=campaign_root,
        ledger=payload,
        legacy_ledger_path=path,
        imported_from=str(path),
    )
    task_count = 0
    tasks = payload.get("tasks", {})
    if isinstance(tasks, Mapping):
        for raw_task_id, raw_record in tasks.items():
            if not isinstance(raw_record, Mapping):
                continue
            task_id = canonicalize_block_id(str(raw_task_id))
            if not task_id:
                continue
            status = str(raw_record.get("status", "") or "unknown")
            artifact_path = str(
                raw_record.get("latest_operation_file", "")
                or raw_record.get("latest_semantic_review_result_file", "")
                or path
            )
            store.record_run(
                run_id=sha256_json({"ledger": sha256_file(path), "task_id": task_id}),
                task_id=task_id,
                operation="legacy_ledger_snapshot",
                status=status,
                campaign_id=campaign_id,
                artifact_path=artifact_path,
                detail={
                    "phase2_status": raw_record.get("phase2_status", ""),
                    "pack_candidate_state": raw_record.get("pack_candidate_state", ""),
                    "source_ledger": str(path),
                },
                started_at=_file_time(path),
                completed_at=_file_time(path) if status in {"COMPLETED", "COMPLETED_WITH_PROOF_DEBT"} else "",
            )
            task_count += 1
    store.mark_imported(source_path=path, source_kind="legacy_ledger", record_count=task_count)
    report.ledgers += 1
    report.ledger_tasks += task_count


def import_review_file(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    applied_receipts: Mapping[str, list[dict[str, str]]],
) -> None:
    if store.import_is_current(path):
        report.skipped += 1
        return
    payload = _read_json(path)
    evidence_hash = sha256_file(path)
    scope = _authority_scope(path)
    count = 0
    for task_id, review, wrapper in _review_payloads(payload):
        verdict = str(review.get("verdict", "") or "").strip().lower()
        if not verdict:
            continue
        candidate_hash = _candidate_hash(review, wrapper)
        candidate_path = _candidate_path(review, wrapper)
        subject = SubjectBundle.from_legacy_hash(
            task_id=task_id,
            candidate_hash=candidate_hash,
            evidence_hash=evidence_hash,
            source_repo=_source_repo(path),
            primary_path=candidate_path,
            authority_scope=scope,
            created_at=_file_time(path),
        )
        store.upsert_subject(subject)
        proof_class = str(review.get("proof_class", "") or wrapper.get("proof_class", "") or "")
        completion_class = str(
            review.get("completion_class", "")
            or wrapper.get("completion_class", "")
            or proof_class
        )
        phase2_status = str(
            review.get("phase2_status", "")
            or review.get("projected_phase2_status", "")
            or wrapper.get("phase2_status", "")
            or wrapper.get("projected", "")
            or ""
        ).strip().lower()
        reviewer_independence = review.get("reviewer_independence", "")
        if isinstance(reviewer_independence, Mapping):
            reviewer_independence = json.dumps(reviewer_independence, ensure_ascii=False, sort_keys=True)
        store.record_review(
            task_id=task_id,
            subject_id=subject.subject_id,
            verdict=verdict,
            proof_class=proof_class,
            completion_class=completion_class,
            phase2_status=phase2_status,
            evidence_path=path,
            evidence_hash=evidence_hash,
            reviewer_independence=str(reviewer_independence),
            authority_scope=scope,
            authority_eligible=(
                bool(candidate_hash)
                and phase2_status == "pass"
                and _matches_applied_receipt(
                    path=path,
                    payload=payload,
                    task_id=task_id,
                    review=review,
                    candidate_hash=candidate_hash,
                    receipts=applied_receipts,
                )
            ),
            reviewed_at=_file_time(path),
        )
        count += 1
    store.mark_imported(source_path=path, source_kind=scope, record_count=count)
    report.reviews += count


def import_sidecar_state(store: WorkspaceStateStore, path: Path, report: MigrationReport) -> None:
    if store.import_is_current(path):
        report.skipped += 1
        return
    payload = _read_json(path)
    count = 0
    if isinstance(payload, Mapping):
        for raw_task_id, raw_record in payload.items():
            if not isinstance(raw_record, Mapping):
                continue
            task_id = canonicalize_block_id(str(raw_task_id))
            if not task_id:
                continue
            store.record_run(
                run_id=sha256_json({"sidecar": sha256_file(path), "task_id": task_id}),
                task_id=task_id,
                operation="historical_sidecar_snapshot",
                status=str(raw_record.get("status", "") or "unknown"),
                artifact_path=path,
                detail={
                    "verdict": raw_record.get("verdict", ""),
                    "projected": raw_record.get("projected", ""),
                    "version": raw_record.get("version", ""),
                    "historical_only": True,
                },
                started_at=_file_time(path),
                completed_at=_file_time(path),
            )
            count += 1
    store.mark_imported(source_path=path, source_kind="historical_sidecar_state", record_count=count)
    report.sidecar_rows += count


def import_workspace_review_binding(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
) -> None:
    """Import a narrow, immutable rebind from an applied legacy review to exact bundles."""

    if store.import_is_current(path):
        report.skipped += 1
        return
    payload = _read_json(path)
    if not isinstance(payload, Mapping) or payload.get("schema_version") != "toy-apollo.workspace-review-binding.v1":
        raise ValueError("workspace review binding has an unsupported schema")
    tasks = payload.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        raise ValueError("workspace review binding must contain a non-empty tasks list")
    evidence_hash = sha256_file(path)
    reviewed_at = str(payload.get("created_at", "") or _file_time(path))
    reviewer_independence = payload.get("reviewer_independence", "")
    if isinstance(reviewer_independence, Mapping):
        reviewer_independence = json.dumps(
            reviewer_independence,
            ensure_ascii=False,
            sort_keys=True,
        )
    count = 0
    for raw in tasks:
        if not isinstance(raw, Mapping):
            raise ValueError("workspace review binding task entry is not an object")
        task_id = canonicalize_block_id(str(raw.get("task_id", "") or ""))
        if not task_id or not _looks_like_task_id(task_id):
            raise ValueError("workspace review binding contains an invalid task id")
        basis = raw.get("basis_review")
        checks = raw.get("checks")
        subjects = raw.get("subjects")
        if not isinstance(basis, Mapping) or not isinstance(checks, Mapping):
            raise ValueError(f"{task_id}: basis_review and checks are required")
        if not isinstance(subjects, list) or not subjects:
            raise ValueError(f"{task_id}: exact subject manifests are required")
        basis_evidence_hash = str(basis.get("evidence_hash", "") or "")
        basis_primary_hash = str(basis.get("primary_hash", "") or "")
        basis_review = store.eligible_review_basis(
            task_id=task_id,
            evidence_hash=basis_evidence_hash,
            primary_hash=basis_primary_hash,
        )
        if basis_review is None:
            raise ValueError(f"{task_id}: basis is not an applied eligible pass")
        binding_kind = str(raw.get("binding_kind", "") or "")
        required_checks = {
            "build_status": "pass",
            "forbidden_scan_status": "pass",
            "support_scope_status": "pass",
            "mat_relocation_status": "pass",
        }
        for key, expected in required_checks.items():
            if str(checks.get(key, "") or "") != expected:
                raise ValueError(f"{task_id}: {key} must be {expected}")
        if binding_kind == "verified_boundary_delta":
            if str(checks.get("declaration_delta_status", "") or "") != "unchanged":
                raise ValueError(f"{task_id}: boundary delta changed declarations")
        elif binding_kind != "legacy_primary_scope_rebind":
            raise ValueError(f"{task_id}: unsupported binding kind {binding_kind!r}")
        for raw_subject in subjects:
            if not isinstance(raw_subject, Mapping):
                raise ValueError(f"{task_id}: subject entry is not an object")
            subject = SubjectBundle.from_manifest(
                task_id=task_id,
                files=raw_subject.get("files", []),
                primary_path=str(raw_subject.get("primary_path", "") or ""),
                source_repo=str(raw_subject.get("source_repo", "") or ""),
                source_commit=str(raw_subject.get("source_commit", "") or ""),
                layout=str(raw_subject.get("layout", "") or ""),
                subject_kind="workspace_review_binding",
                created_at=reviewed_at,
            )
            if subject.bundle_hash != str(raw_subject.get("bundle_hash", "") or ""):
                raise ValueError(f"{task_id}: subject bundle hash mismatch")
            if subject.primary_hash != str(raw_subject.get("primary_hash", "") or ""):
                raise ValueError(f"{task_id}: subject primary hash mismatch")
            if binding_kind == "legacy_primary_scope_rebind" and subject.primary_hash != basis_primary_hash:
                raise ValueError(f"{task_id}: ordinary scope rebind changed the primary file")
            store.upsert_subject(subject)
            store.record_review(
                task_id=task_id,
                subject_id=subject.subject_id,
                verdict="pass",
                proof_class=str(basis_review.get("proof_class", "") or ""),
                completion_class=str(basis_review.get("completion_class", "") or ""),
                phase2_status="pass",
                evidence_path=path,
                evidence_hash=evidence_hash,
                reviewer_independence=str(reviewer_independence),
                authority_scope=f"workspace_bundle_rebind:{binding_kind}",
                authority_eligible=True,
                reviewed_at=reviewed_at,
            )
            count += 1
    store.mark_imported(
        source_path=path,
        source_kind="workspace_review_binding",
        record_count=count,
    )
    report.reviews += count
    report.review_bindings += count


def _receipt_artifact(
    receipt_path: Path,
    raw: Any,
    *,
    label: str,
) -> tuple[Path, dict[str, Any]]:
    if not isinstance(raw, Mapping):
        raise ValueError(f"external PR receipt {label} reference is missing")
    artifact_path = Path(str(raw.get("path", "") or "")).expanduser()
    if not artifact_path.is_absolute():
        artifact_path = receipt_path.parent / artifact_path
    artifact_path = artifact_path.resolve()
    expected_hash = str(raw.get("sha256", "") or "")
    if not artifact_path.is_file() or not expected_hash:
        raise ValueError(f"external PR receipt {label} artifact is missing")
    if sha256_file(artifact_path) != expected_hash:
        raise ValueError(f"external PR receipt {label} artifact hash mismatch")
    payload = _read_json(artifact_path)
    if not isinstance(payload, dict):
        raise ValueError(f"external PR receipt {label} artifact is not a JSON object")
    return artifact_path, payload


def import_external_pr_review_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
) -> None:
    """Restore an eligible review that was applied to one exact external PR head."""

    if store.import_is_current(path):
        report.skipped += 1
        return
    payload = _read_json(path)
    if not isinstance(payload, Mapping) or payload.get("schema") != "toy-apollo.external-pr-review-apply.v1":
        raise ValueError("external PR review receipt has an unsupported schema")
    task_id = canonicalize_block_id(str(payload.get("task_id", "") or ""))
    if not task_id or not _looks_like_task_id(task_id):
        raise ValueError("external PR review receipt contains an invalid task id")
    if (
        payload.get("authority_eligible") is not True
        or payload.get("pr_mutated") is not False
        or str(payload.get("authority_scope", "") or "") != "kenneth_pr_exact_head_review"
    ):
        raise ValueError("external PR review receipt is not an eligible read-only exact-head apply")

    repo = str(payload.get("repo", "") or "")
    pr_number = int(payload.get("pr_number", 0) or 0)
    base_sha = str(payload.get("base_sha", "") or "")
    head_sha = str(payload.get("head_sha", "") or "")
    changed_files = [str(item) for item in payload.get("changed_files", [])]
    if not repo or pr_number <= 0 or not base_sha or not head_sha or not changed_files:
        raise ValueError("external PR review receipt lacks exact PR identity")

    raw_subject = payload.get("subject_bundle")
    if not isinstance(raw_subject, Mapping) or raw_subject.get("schema") != "toy-apollo.subject-bundle.v1":
        raise ValueError("external PR review receipt lacks a reconstructible subject bundle")
    if canonicalize_block_id(str(raw_subject.get("task_id", "") or "")) != task_id:
        raise ValueError("external PR subject task does not match the receipt")
    subject = SubjectBundle.from_manifest(
        task_id=task_id,
        files=raw_subject.get("files", []),
        primary_path=str(raw_subject.get("primary_path", "") or ""),
        source_repo=str(raw_subject.get("source_repo", "") or ""),
        source_commit=str(raw_subject.get("source_commit", "") or ""),
        layout=str(raw_subject.get("layout", "") or ""),
        subject_kind=str(raw_subject.get("subject_kind", "") or ""),
        created_at=str(payload.get("applied_at", "") or _file_time(path)),
    )
    for field, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
    ):
        expected = str(payload.get(field, "") or "")
        manifest_expected = str(raw_subject.get(field, "") or "")
        if actual != expected or actual != manifest_expected:
            raise ValueError(f"external PR subject {field} mismatch")
    if subject.source_commit != head_sha or subject.primary_path not in changed_files:
        raise ValueError("external PR subject is not bound to the recorded head and changed files")

    review_path, review = _receipt_artifact(
        path, payload.get("semantic_review"), label="semantic review"
    )
    _classification_path, classification = _receipt_artifact(
        path, payload.get("classification"), label="classification"
    )
    _builder_path, builder = _receipt_artifact(
        path, payload.get("builder_evidence"), label="builder evidence"
    )
    classification_ref = payload.get("classification")
    if not isinstance(classification_ref, Mapping):
        raise ValueError("external PR classification reference is missing")
    proof_class = str(classification_ref.get("proof_class", "") or "")
    completion_class = str(classification_ref.get("completion_class", "") or "")
    if not proof_class or not completion_class:
        raise ValueError("external PR receipt lacks canonical completion classes")

    from .state_pr_review import (
        PullRequestObservation,
        _matching_exact_binding,
        _validate_builder_evidence,
    )

    observation = PullRequestObservation(
        repo=repo,
        number=pr_number,
        state="open",
        draft=True,
        base_sha=base_sha,
        head_sha=head_sha,
        head_repo=str(payload.get("head_repo", "") or ""),
        head_ref=str(payload.get("head_ref", "") or ""),
        changed_files=tuple(changed_files),
        affected_files=tuple(path for path in changed_files if path == subject.primary_path),
        subject=subject,
        url=str(payload.get("url", "") or ""),
    )
    if str(review.get("schema_version", "") or "") != "toy-apollo.kenneth-pr-exact-semantic-review.v1":
        raise ValueError("external PR semantic review schema is unsupported")
    if (
        canonicalize_block_id(str(review.get("task_id", "") or "")) != task_id
        or str(review.get("verdict", "") or "").lower() != "pass"
        or str(review.get("candidate_hash", "") or "") != subject.primary_hash
        or str(review.get("subject_bundle_hash", "") or "") != subject.bundle_hash
        or not isinstance(review.get("exact_binding"), Mapping)
        or not _matching_exact_binding(review["exact_binding"], observation)
    ):
        raise ValueError("external PR semantic review does not match the receipt subject")
    basis = classification.get("basis_review")
    if (
        str(classification.get("schema_version", "") or "")
        != "toy-apollo.semantic-review-classification-supplement.v1"
        or canonicalize_block_id(str(classification.get("task_id", "") or "")) != task_id
        or str(classification.get("verdict", "") or "").lower() != "pass"
        or not isinstance(basis, Mapping)
        or str(basis.get("sha256", "") or "") != sha256_file(review_path)
        or str(classification.get("proof_class", "") or "") != proof_class
        or str(classification.get("completion_class", "") or "") != completion_class
        or not isinstance(classification.get("exact_binding"), Mapping)
        or not _matching_exact_binding(classification["exact_binding"], observation)
    ):
        raise ValueError("external PR classification does not match the reviewed subject")
    _validate_builder_evidence(builder, observation)

    independence = payload.get("reviewer_independence")
    if not isinstance(independence, Mapping) or independence.get("read_only") is not True:
        raise ValueError("external PR receipt lacks read-only reviewer independence")
    for field in (
        "modified_candidate",
        "modified_evidence",
        "created_or_deleted_files",
        "git_checkout_commit_push_performed",
        "build_rerun_by_reviewer",
    ):
        if independence.get(field) is not False:
            raise ValueError(f"external PR reviewer independence field {field} is not false")

    evidence_hash = sha256_file(path)
    reviewed_at = str(payload.get("applied_at", "") or _file_time(path))
    store.upsert_subject(subject)
    review_id = store.record_review(
        task_id=task_id,
        subject_id=subject.subject_id,
        verdict="pass",
        proof_class=proof_class,
        completion_class=completion_class,
        phase2_status="pass",
        evidence_path=path,
        evidence_hash=evidence_hash,
        reviewer_independence=json.dumps(dict(independence), ensure_ascii=False, sort_keys=True),
        authority_scope="kenneth_pr_exact_head_review",
        authority_eligible=True,
        reviewed_at=reviewed_at,
    )
    store.set_task_head(
        task_id=task_id,
        role="kenneth_pr_head",
        subject_id=subject.subject_id,
        observed_at=reviewed_at,
        detail={
            "repo": repo,
            "pr_number": pr_number,
            "head_sha": head_sha,
            "review_id": review_id,
            "imported_apply_receipt": str(path),
        },
    )
    store.mark_imported(
        source_path=path,
        source_kind="external_pr_review_apply_receipt",
        record_count=1,
    )
    report.reviews += 1
    report.external_pr_receipts += 1


def default_migration_roots(*, workspace_root: Path, runtime_root: Path) -> list[Path]:
    roots = [workspace_root / "toy-apollo-artifacts", runtime_root]
    return [path.resolve() for path in roots if path.exists()]


def _active_legacy_ledger(
    *,
    ledger_paths: Iterable[Path],
    workspace_root: Path,
    runtime_root: Path,
) -> Path | None:
    candidates = [
        (workspace_root / "toy-apollo-artifacts" / "project_ledger.json").resolve(),
        (runtime_root / "project_ledger.json").resolve(),
    ]
    available = {path.resolve(): path for path in ledger_paths}
    return next((available[path] for path in candidates if path in available), None)


def rebuild_workspace_database(
    *,
    state_path: Path,
    workspace_root: Path,
    runtime_root: Path,
    roots: Iterable[Path] | None = None,
    refresh_remote: bool = False,
) -> MigrationReport:
    target = WorkspaceStateStore(state_path)
    temp_store = WorkspaceStateStore.temporary_rebuild_store(target.path)
    report = MigrationReport(database=str(target.path))
    scan_roots = list(roots or default_migration_roots(workspace_root=workspace_root, runtime_root=runtime_root))
    try:
        ledger_paths = list(_ledger_files(scan_roots))
        applied_receipts = _applied_review_receipts(ledger_paths)
        receipt_paths = [
            Path(receipt["result_file"])
            for task_receipts in applied_receipts.values()
            for receipt in task_receipts
            if receipt.get("result_file")
        ]
        with temp_store.bulk_write():
            for path in ledger_paths:
                try:
                    import_legacy_ledger(temp_store, path, report)
                except Exception as exc:
                    report.warnings.append(f"ledger {path}: {exc}")
            active_legacy = _active_legacy_ledger(
                ledger_paths=ledger_paths,
                workspace_root=workspace_root,
                runtime_root=runtime_root,
            )
            if active_legacy is not None:
                active_payload = _read_json(active_legacy)
                if not isinstance(active_payload, Mapping):
                    raise RuntimeError(f"Active legacy ledger is malformed: {active_legacy}")
                temp_store.import_campaign_ledger(
                    campaign_id="workspace:active",
                    artifact_root=runtime_root,
                    ledger=active_payload,
                    legacy_ledger_path=active_legacy,
                    imported_from=str(active_legacy),
                )
            else:
                report.warnings.append("No explicit active legacy ledger was found; workspace:active will be initialized on first operation.")
            for path in _review_files(scan_roots, always_include=receipt_paths):
                try:
                    import_review_file(
                        temp_store,
                        path,
                        report,
                        applied_receipts=applied_receipts,
                    )
                except Exception as exc:
                    report.warnings.append(f"review {path}: {exc}")
            for path in _workspace_review_binding_files(scan_roots):
                try:
                    import_workspace_review_binding(temp_store, path, report)
                except Exception as exc:
                    report.warnings.append(f"review binding {path}: {exc}")
            for path in _external_pr_review_receipt_files(scan_roots):
                try:
                    import_external_pr_review_receipt(temp_store, path, report)
                except Exception as exc:
                    report.warnings.append(f"external PR review receipt {path}: {exc}")
            for path in _sidecar_state_files(scan_roots):
                try:
                    import_sidecar_state(temp_store, path, report)
                except Exception as exc:
                    report.warnings.append(f"sidecar {path}: {exc}")
        reconciliation = refresh_workspace_state(
            temp_store,
            workspace_root=workspace_root,
            runtime_root=runtime_root,
            chapters=(1, 2, 3, 4),
            refresh_remote=refresh_remote,
        )
        local = reconciliation.get("local") or {}
        report.local_subjects = int(local.get("mat_main", 0)) + int(local.get("mat_candidate", 0)) + int(local.get("toy_current", 0))
        report.warnings.extend(str(error) for error in local.get("errors", []))
        remote = reconciliation.get("remote") or {}
        report.remote_subjects = int(remote.get("subjects", 0) or 0)
        report.warnings.extend(str(error) for error in remote.get("errors", []))
        summary = temp_store.summary()
        if not any(summary[key] for key in ("campaign_ledgers", "subjects", "reviews", "runs", "integrations", "task_heads")):
            raise RuntimeError("State rebuild found no ledger, review evidence, repository subjects, or task heads.")
        temp_store.assert_integrity()
        backup = target.replace_from(temp_store.path, backup_label="rebuild")
        report.backup = str(backup or "")
        return report
    except Exception:
        temp_store.path.unlink(missing_ok=True)
        raise
