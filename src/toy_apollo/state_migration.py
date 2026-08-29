from __future__ import annotations

import json
import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Mapping

from src.block_id_naming import canonicalize_block_id, is_canonical_block_id

from .state_bundle_delta import compare_bundles
from .state_review_apply_recovery import (
    RECOVERY_AUTHORITY_SCOPE,
    RECOVERY_SCHEMA,
    validate_historical_review_apply_recovery,
)
from .state_invalidation_recovery import (
    RESOLVED_INVALIDATION_AUTHORITY_SCOPE,
    RESOLVED_INVALIDATION_SCHEMA,
    validate_resolved_invalidation_recovery,
)
from .state_boundary_delta_receipt import (
    BOUNDARY_DELTA_SCHEMA,
    TRANSFORMATION_KIND as BOUNDARY_DELTA_KIND,
    validate_verified_boundary_delta,
)
from .state_evidence_bridge import (
    AUTHORITY_KENNETH,
    AUTHORITY_MAT_SYNC,
    EVIDENCE_BRIDGE_SCHEMA,
    FINAL122_BATCH_RECEIPT_SCHEMA,
    TRANSFORMATION_KIND as EVIDENCE_BRIDGE_KIND,
    validate_evidence_bridge_receipt,
    load_validated_final122_bridge_batch_receipt,
)
from .state_exact_build_batch import (
    ExactBuildBatchError,
    catalog_owned_build_modules,
    validate_current_exact_build_receipt,
)
from .state_reconcile import refresh_workspace_state
from .review_versions import (
    profile_for_catalog,
    prompt_version_sql_predicate,
    rubric_version_sql_predicate,
    supported_prompt_versions,
    supported_rubric_version,
)
from .task_catalog import TaskCatalog, load_catalog, validate_catalog
from .state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    filesystem_path,
    sha256_file,
    sha256_json,
    stable_absolute_path,
    utc_now,
)


@dataclass
class MigrationReport:
    database: str
    backup: str = ""
    ledgers: int = 0
    ledger_tasks: int = 0
    reviews: int = 0
    rejected_reviews: int = 0
    review_bindings: int = 0
    external_pr_receipts: int = 0
    mat_review_receipts: int = 0
    rejected_mat_review_receipts: int = 0
    phase2_review_apply_receipts: int = 0
    rejected_phase2_review_apply_receipts: int = 0
    historical_apply_recovery_receipts: int = 0
    rejected_historical_apply_recovery_receipts: int = 0
    resolved_invalidation_recovery_receipts: int = 0
    rejected_resolved_invalidation_recovery_receipts: int = 0
    validated_transformation_receipts: int = 0
    rejected_transformation_receipts: int = 0
    boundary_delta_receipts: int = 0
    rejected_boundary_delta_receipts: int = 0
    evidence_bridge_receipts: int = 0
    rejected_evidence_bridge_receipts: int = 0
    evidence_bridge_batch_receipts: int = 0
    rejected_evidence_bridge_batch_receipts: int = 0
    process_events: int = 0
    duplicate_evidence_copies: int = 0
    evidence_roots: int = 0
    catalog_id: str = ""
    catalog_counts: dict[str, int] = field(default_factory=dict)
    invariants: dict[str, Any] = field(default_factory=dict)
    rebuilt_database: str = ""
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
            "rejected_reviews": self.rejected_reviews,
            "review_bindings": self.review_bindings,
            "external_pr_receipts": self.external_pr_receipts,
            "mat_review_receipts": self.mat_review_receipts,
            "rejected_mat_review_receipts": self.rejected_mat_review_receipts,
            "phase2_review_apply_receipts": self.phase2_review_apply_receipts,
            "rejected_phase2_review_apply_receipts": self.rejected_phase2_review_apply_receipts,
            "historical_apply_recovery_receipts": self.historical_apply_recovery_receipts,
            "rejected_historical_apply_recovery_receipts": self.rejected_historical_apply_recovery_receipts,
            "resolved_invalidation_recovery_receipts": self.resolved_invalidation_recovery_receipts,
            "rejected_resolved_invalidation_recovery_receipts": self.rejected_resolved_invalidation_recovery_receipts,
            "validated_transformation_receipts": self.validated_transformation_receipts,
            "rejected_transformation_receipts": self.rejected_transformation_receipts,
            "boundary_delta_receipts": self.boundary_delta_receipts,
            "rejected_boundary_delta_receipts": self.rejected_boundary_delta_receipts,
            "evidence_bridge_receipts": self.evidence_bridge_receipts,
            "rejected_evidence_bridge_receipts": self.rejected_evidence_bridge_receipts,
            "evidence_bridge_batch_receipts": self.evidence_bridge_batch_receipts,
            "rejected_evidence_bridge_batch_receipts": self.rejected_evidence_bridge_batch_receipts,
            "process_events": self.process_events,
            "duplicate_evidence_copies": self.duplicate_evidence_copies,
            "evidence_roots": self.evidence_roots,
            "catalog_id": self.catalog_id,
            "catalog_counts": dict(self.catalog_counts),
            "invariants": dict(self.invariants),
            "rebuilt_database": self.rebuilt_database,
            "sidecar_rows": self.sidecar_rows,
            "skipped": self.skipped,
            "local_subjects": self.local_subjects,
            "remote_subjects": self.remote_subjects,
            "warnings": list(self.warnings),
            "errors": list(self.errors),
        }


def _read_json(path: Path) -> Any:
    return json.loads(filesystem_path(path).read_text(encoding="utf-8"))


def _json_value(raw: Any) -> Any:
    if not isinstance(raw, str):
        return raw
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return raw


def _file_time(path: Path) -> str:
    return datetime.fromtimestamp(
        filesystem_path(path).stat().st_mtime, tz=timezone.utc
    ).isoformat()


def _looks_like_task_id(value: str, profile: str = "mat") -> bool:
    canonical = canonicalize_block_id(value, profile)
    return is_canonical_block_id(canonical, profile)


def _task_id(
    payload: Mapping[str, Any],
    fallback: str = "",
    *,
    profile: str = "mat",
) -> str:
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
        canonical = canonicalize_block_id(str(candidate or ""), profile)
        if canonical and _looks_like_task_id(canonical, profile):
            return canonical
    return ""


def _review_payloads(
    payload: Any,
    *,
    profile: str = "mat",
) -> Iterator[tuple[str, Mapping[str, Any], Mapping[str, Any]]]:
    if not isinstance(payload, Mapping):
        return
    direct_task = _task_id(payload, profile=profile)
    direct_verdict = str(payload.get("verdict", "") or "")
    if direct_task and direct_verdict:
        yield direct_task, payload, payload
        return
    for key, value in payload.items():
        if not isinstance(value, Mapping):
            continue
        task_id = _task_id(value, fallback=str(key), profile=profile)
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


def _applied_review_receipts(
    ledger_paths: Iterable[Path],
    *,
    profile: str = "mat",
) -> dict[str, list[dict[str, str]]]:
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
            task_id = canonicalize_block_id(str(raw_task_id), profile)
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


@dataclass(frozen=True)
class EvidenceInventory:
    ledgers: tuple[Path, ...]
    reviews: tuple[Path, ...]
    workspace_review_bindings: tuple[Path, ...]
    external_pr_receipts: tuple[Path, ...]
    mat_review_receipts: tuple[Path, ...]
    phase2_review_apply_receipts: tuple[Path, ...]
    historical_apply_recovery_receipts: tuple[Path, ...]
    resolved_invalidation_recovery_receipts: tuple[Path, ...]
    validated_transformation_receipts: tuple[Path, ...]
    boundary_delta_receipts: tuple[Path, ...]
    evidence_bridge_receipts: tuple[Path, ...]
    evidence_bridge_batch_receipts: tuple[Path, ...]
    sidecars: tuple[Path, ...]
    process_events: tuple[Path, ...]


def _json_paths(roots: Iterable[Path]) -> tuple[Path, ...]:
    """List JSON evidence once, preferring ripgrep's fast directory walker."""

    selected: set[Path] = set()
    exclusions = (
        "!.git/**",
        "!.lake/**",
        "!.venv/**",
        "!node_modules/**",
        "!__pycache__/**",
    )
    for raw_root in roots:
        root = raw_root.expanduser().resolve()
        if not root.exists():
            continue
        argv = ["rg", "--files", "--hidden", "--no-ignore", "-g", "*.json"]
        for pattern in exclusions:
            argv.extend(["-g", pattern])
        argv.extend(["--", str(root)])
        try:
            completed = subprocess.run(
                argv,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                timeout=120,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            completed = None
        if completed is not None and completed.returncode in {0, 1}:
            for raw in completed.stdout.decode("utf-8", errors="replace").splitlines():
                if raw.strip():
                    selected.add(Path(raw.strip()).resolve())
            continue
        for directory, names, files in os.walk(root):
            names[:] = [
                name
                for name in names
                if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}
            ]
            for filename in files:
                if filename.lower().endswith(".json"):
                    selected.add((Path(directory) / filename).resolve())
    return tuple(sorted(selected, key=lambda item: str(item).lower()))


def discover_evidence_inventory(roots: Iterable[Path]) -> EvidenceInventory:
    ledgers: list[Path] = []
    reviews: list[Path] = []
    bindings: list[Path] = []
    external: list[Path] = []
    mat_receipt_candidates: list[Path] = []
    phase2_receipt_candidates: list[Path] = []
    historical_apply_recovery_receipts: list[Path] = []
    resolved_invalidation_recovery_receipts: list[Path] = []
    transformation_receipts: list[Path] = []
    boundary_delta_receipts: list[Path] = []
    evidence_bridge_receipts: list[Path] = []
    evidence_bridge_batch_candidates: list[Path] = []
    sidecars: list[Path] = []
    process_events: list[Path] = []
    process_prefixes = (
        "build_result",
        "verify_result",
        "math_review_result",
        "basis_rebind",
        "review_apply_receipt",
        "external_pr_review_apply_receipt",
    )
    for path in _json_paths(roots):
        lowered = path.name.lower()
        if lowered == "project_ledger.json":
            ledgers.append(path)
        if (
            "template" not in lowered
            and (
                "semantic_review_result" in lowered
                or "_recheck_result" in lowered
                or "proof_debt_repair_result" in lowered
                or lowered.startswith("reviews_ch")
            )
        ):
            reviews.append(path)
        if lowered.startswith("workspace_review_binding_"):
            bindings.append(path)
        if lowered == "external_pr_review_apply_receipt.json":
            external.append(path)
        if lowered.startswith("review_apply_receipt"):
            mat_receipt_candidates.append(path)
            phase2_receipt_candidates.append(path)
        if lowered.startswith("historical_review_apply_recovery_receipt"):
            historical_apply_recovery_receipts.append(path)
        if lowered.startswith("resolved_invalidation_recovery_receipt"):
            resolved_invalidation_recovery_receipts.append(path)
        if lowered.startswith("validated_transformation_receipt"):
            transformation_receipts.append(path)
        if lowered.startswith("validated_boundary_delta_receipt"):
            boundary_delta_receipts.append(path)
        if lowered.startswith("validated_evidence_bridge_receipt"):
            evidence_bridge_receipts.append(path)
        if lowered.startswith(("validated_evidence_bridge_batch_receipt", "final122_evidence_bridge_batch_receipt")):
            evidence_bridge_batch_candidates.append(path)
        if lowered.startswith("state_ch"):
            sidecars.append(path)
        if lowered.startswith(process_prefixes):
            process_events.append(path)

    mat_receipts: list[Path] = []
    for path in mat_receipt_candidates:
        try:
            payload = _read_json(path)
        except Exception:
            continue
        if isinstance(payload, Mapping) and payload.get("schema") == "mat.rubric78.review-apply-receipt.v1":
            mat_receipts.append(path)
    phase2_receipts: list[Path] = []
    for path in phase2_receipt_candidates:
        try:
            payload = _read_json(path)
        except Exception:
            continue
        if (
            isinstance(payload, Mapping)
            and payload.get("schema_version")
            == "toy-apollo.phase2-review-apply-receipt.v1"
        ):
            phase2_receipts.append(path)
    process_events = [path for path in process_events if path not in phase2_receipts]
    evidence_bridge_batch_receipts: list[Path] = []
    for path in evidence_bridge_batch_candidates:
        try:
            payload = _read_json(path)
        except Exception:
            continue
        if isinstance(payload, Mapping) and payload.get("schema") == FINAL122_BATCH_RECEIPT_SCHEMA:
            evidence_bridge_batch_receipts.append(path)
    return EvidenceInventory(
        ledgers=tuple(ledgers),
        reviews=tuple(reviews),
        workspace_review_bindings=tuple(bindings),
        external_pr_receipts=tuple(external),
        mat_review_receipts=tuple(mat_receipts),
        phase2_review_apply_receipts=tuple(phase2_receipts),
        historical_apply_recovery_receipts=tuple(historical_apply_recovery_receipts),
        resolved_invalidation_recovery_receipts=tuple(resolved_invalidation_recovery_receipts),
        validated_transformation_receipts=tuple(transformation_receipts),
        boundary_delta_receipts=tuple(boundary_delta_receipts),
        evidence_bridge_receipts=tuple(evidence_bridge_receipts),
        evidence_bridge_batch_receipts=tuple(evidence_bridge_batch_receipts),
        sidecars=tuple(sidecars),
        process_events=tuple(process_events),
    )


def _safe_hash(path: Path) -> tuple[Path, str, str]:
    try:
        return path, sha256_file(path), ""
    except Exception as exc:
        return path, "", str(exc)


def _hash_paths(paths: Iterable[Path]) -> tuple[dict[Path, str], list[str]]:
    ordered = tuple(dict.fromkeys(paths))
    hashes: dict[Path, str] = {}
    errors: list[str] = []
    if not ordered:
        return hashes, errors
    workers = min(16, max(1, len(ordered)))
    with ThreadPoolExecutor(max_workers=workers) as executor:
        for path, digest, error in executor.map(_safe_hash, ordered):
            if error:
                errors.append(f"hash {path}: {error}")
            else:
                hashes[path] = digest
    return hashes, errors


def _read_json_safe(path: Path) -> tuple[Path, Any | None, str, str]:
    try:
        return path, _read_json(path), _file_time(path), ""
    except Exception as exc:
        return path, None, "", str(exc)


def _json_batches(
    paths: Iterable[Path],
    *,
    batch_size: int = 256,
) -> Iterator[list[tuple[Path, Any | None, str, str]]]:
    ordered = tuple(paths)
    if not ordered:
        return
    with ThreadPoolExecutor(max_workers=min(16, len(ordered))) as executor:
        for start in range(0, len(ordered), batch_size):
            batch = ordered[start : start + batch_size]
            yield list(executor.map(_read_json_safe, batch))


def _deduplicate_paths(
    paths: Iterable[Path],
    hashes: Mapping[Path, str],
) -> tuple[list[Path], list[tuple[Path, Path, str]]]:
    canonical_by_hash: dict[str, Path] = {}
    unique: list[Path] = []
    duplicates: list[tuple[Path, Path, str]] = []
    for path in paths:
        digest = hashes.get(path, "")
        if not digest:
            continue
        canonical = canonical_by_hash.get(digest)
        if canonical is None:
            canonical_by_hash[digest] = path
            unique.append(path)
        else:
            duplicates.append((path, canonical, digest))
    return unique, duplicates


def _emit_progress(
    callback: Callable[[str, Mapping[str, Any]], None] | None,
    phase: str,
    **detail: Any,
) -> None:
    if callback is not None:
        callback(phase, detail)


def import_legacy_ledger(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    profile: str = "mat",
) -> None:
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
    evidence_time = _file_time(path)
    evidence_hash = sha256_file(path)
    tasks = payload.get("tasks", {})
    if isinstance(tasks, Mapping):
        for raw_task_id, raw_record in tasks.items():
            if not isinstance(raw_record, Mapping):
                continue
            task_id = canonicalize_block_id(str(raw_task_id), profile)
            if not task_id:
                continue
            status = str(raw_record.get("status", "") or "unknown")
            artifact_path = str(
                raw_record.get("latest_operation_file", "")
                or raw_record.get("latest_semantic_review_result_file", "")
                or path
            )
            store.record_run(
                run_id=sha256_json({"ledger": evidence_hash, "task_id": task_id}),
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
                started_at=evidence_time,
                updated_at=evidence_time,
                completed_at=evidence_time if status in {"COMPLETED", "COMPLETED_WITH_PROOF_DEBT"} else "",
            )
            task_count += 1
    store.mark_imported(
        source_path=path,
        source_kind="legacy_ledger",
        record_count=task_count,
        source_hash=evidence_hash,
    )
    report.ledgers += 1
    report.ledger_tasks += task_count


def _int_or_none(value: Any) -> int | None:
    try:
        return int(value) if value not in (None, "") else None
    except (TypeError, ValueError):
        return None


def _artifact_path_from_reference(
    owner_path: Path,
    raw_path: Any,
    *,
    fallback_names: Iterable[str] = (),
) -> Path | None:
    raw = str(raw_path or "").strip()
    candidates: list[Path] = []
    if raw:
        candidate = Path(raw).expanduser()
        candidates.append(candidate if candidate.is_absolute() else owner_path.parent / candidate)
        candidates.append(owner_path.parent / Path(raw).name)
    candidates.extend(owner_path.parent / name for name in fallback_names)
    seen: set[Path] = set()
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except OSError:
            continue
        if resolved in seen:
            continue
        seen.add(resolved)
        if resolved.is_file():
            return resolved
    return None


def _review_input_for_result(
    path: Path,
    review: Mapping[str, Any],
) -> tuple[Path | None, Mapping[str, Any] | None, str]:
    version_match = re.search(r"_v(\d+)(?:_raw)?\.json$", path.name.lower())
    fallbacks: list[str] = []
    if version_match:
        fallbacks.append(f"semantic_review_input_v{version_match.group(1)}.json")
    fallbacks.append("semantic_review_input.json")
    input_path = _artifact_path_from_reference(
        path,
        review.get("review_input_file", ""),
        fallback_names=fallbacks,
    )
    if input_path is None:
        return None, None, ""
    try:
        payload = _read_json(input_path)
    except Exception:
        return input_path, None, ""
    if not isinstance(payload, Mapping):
        return input_path, None, ""
    return input_path, payload, sha256_json(payload)


def _exact_subject_from_review_input(
    *,
    task_id: str,
    input_payload: Mapping[str, Any] | None,
    created_at: str,
    profile: str = "mat",
) -> SubjectBundle | None:
    if input_payload is None:
        return None
    raw_subject = input_payload.get("subject_bundle")
    if not isinstance(raw_subject, Mapping):
        return None
    if canonicalize_block_id(
        str(raw_subject.get("task_id", "") or ""), profile
    ) != task_id:
        raise ValueError(f"{task_id}: review input subject task mismatch")
    subject = SubjectBundle.from_manifest(
        task_id=task_id,
        files=raw_subject.get("files", []),
        primary_path=str(raw_subject.get("primary_path", "") or ""),
        source_repo=str(raw_subject.get("source_repo", "") or ""),
        source_commit=str(raw_subject.get("source_commit", "") or ""),
        layout=str(raw_subject.get("layout", "") or ""),
        subject_kind=str(raw_subject.get("subject_kind", "") or "review_input_bundle"),
        parent_subject_id=str(raw_subject.get("parent_subject_id", "") or ""),
        created_at=created_at,
    )
    for key, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
    ):
        expected = str(raw_subject.get(key, "") or "")
        if expected and expected != actual:
            raise ValueError(f"{task_id}: review input subject {key} mismatch")
    return subject


def _reviewed_at(
    path: Path,
    review: Mapping[str, Any],
    input_payload: Mapping[str, Any] | None,
) -> str:
    for payload in (review, input_payload or {}):
        for key in ("reviewed_at", "completed_at", "created_at", "generated_at"):
            value = str(payload.get(key, "") or "")
            if value:
                return value
    return _file_time(path)


def import_review_file(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    applied_receipts: Mapping[str, list[dict[str, str]]],
    payload: Any | None = None,
    evidence_hash: str = "",
    profile: str = "mat",
) -> None:
    resolved_hash = evidence_hash or sha256_file(path)
    if store.import_is_current(path, source_hash=resolved_hash):
        report.skipped += 1
        return
    payload = _read_json(path) if payload is None else payload
    evidence_hash = resolved_hash
    scope = _authority_scope(path)
    count = 0
    for task_id, review, wrapper in _review_payloads(payload, profile=profile):
        verdict = str(review.get("verdict", "") or "").strip().lower()
        if not verdict:
            continue
        input_path, input_payload, computed_input_hash = _review_input_for_result(path, review)
        declared_input_hash = str(review.get("review_input_hash", "") or "")
        if declared_input_hash and computed_input_hash and declared_input_hash != computed_input_hash:
            raise ValueError(f"{task_id}: semantic review input hash mismatch")
        reviewed_at = _reviewed_at(path, review, input_payload)
        subject = _exact_subject_from_review_input(
            task_id=task_id,
            input_payload=input_payload,
            created_at=reviewed_at,
            profile=profile,
        )
        candidate_hash = _candidate_hash(review, wrapper)
        candidate_path = _candidate_path(review, wrapper)
        if subject is None:
            subject = SubjectBundle.from_legacy_hash(
                task_id=task_id,
                candidate_hash=candidate_hash,
                evidence_hash=evidence_hash,
                source_repo=_source_repo(path),
                primary_path=candidate_path,
                authority_scope=scope,
                created_at=reviewed_at,
            )
        elif candidate_hash and candidate_hash != subject.primary_hash:
            raise ValueError(f"{task_id}: review candidate hash does not match exact subject")
        else:
            candidate_hash = subject.primary_hash
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
            reviewed_at=reviewed_at,
            prompt_version=_int_or_none(
                review.get("prompt_version", "")
                or (input_payload or {}).get("prompt_version", "")
            ),
            rubric_version=_int_or_none(
                review.get("rubric_version", "")
                or (input_payload or {}).get("rubric_version", "")
            ),
            review_input_path=input_path or "",
            review_input_hash=declared_input_hash or computed_input_hash,
            reviewer_backend_id=str(
                review.get("reviewer_backend_id", "")
                or (input_payload or {}).get("reviewer_backend_id", "")
            ),
            provenance={
                "import_kind": "historical_semantic_review",
                "result_schema": review.get("schema_version", review.get("schema", "")),
                "exact_subject_reconstructed": input_payload is not None
                and isinstance((input_payload or {}).get("subject_bundle"), Mapping),
                "source_root": str(path.parent),
            },
        )
        count += 1
    store.mark_imported(
        source_path=path,
        source_kind=scope,
        record_count=count,
        source_hash=evidence_hash,
    )
    report.reviews += count


def import_duplicate_review_copy(
    store: WorkspaceStateStore,
    *,
    path: Path,
    evidence_hash: str,
    canonical_path: Path,
    report: MigrationReport,
) -> None:
    store.mark_imported(
        source_path=path,
        source_kind=f"duplicate_semantic_review_copy:{canonical_path.name}",
        record_count=0,
        source_hash=evidence_hash,
    )
    report.duplicate_evidence_copies += 1


def import_rejected_review_artifact(
    store: WorkspaceStateStore,
    *,
    path: Path,
    evidence_hash: str,
    error: str,
    report: MigrationReport,
    payload: Any | None = None,
    occurred_at: str = "",
    profile: str = "mat",
) -> None:
    task_id = (
        _task_id(payload, fallback=path.parent.name, profile=profile)
        if isinstance(payload, Mapping)
        else ""
    )
    summary = {
        "validation_error": error,
        "verdict": payload.get("verdict", "") if isinstance(payload, Mapping) else "",
        "prompt_version": payload.get("prompt_version") if isinstance(payload, Mapping) else None,
        "rubric_version": payload.get("rubric_version") if isinstance(payload, Mapping) else None,
    }
    store.record_event(
        event_type="semantic_review_artifact_rejected",
        task_id=task_id,
        evidence_path=path,
        evidence_hash=evidence_hash,
        occurred_at=occurred_at or _file_time(path),
        payload=summary,
    )
    store.mark_imported(
        source_path=path,
        source_kind="rejected_semantic_review_artifact",
        record_count=1,
        source_hash=evidence_hash,
    )
    report.rejected_reviews += 1


def import_sidecar_state(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    profile: str = "mat",
) -> None:
    if store.import_is_current(path):
        report.skipped += 1
        return
    payload = _read_json(path)
    count = 0
    evidence_time = _file_time(path)
    evidence_hash = sha256_file(path)
    if isinstance(payload, Mapping):
        for raw_task_id, raw_record in payload.items():
            if not isinstance(raw_record, Mapping):
                continue
            task_id = canonicalize_block_id(str(raw_task_id), profile)
            if not task_id:
                continue
            store.record_run(
                run_id=sha256_json({"sidecar": evidence_hash, "task_id": task_id}),
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
                started_at=evidence_time,
                updated_at=evidence_time,
                completed_at=evidence_time,
            )
            count += 1
    store.mark_imported(
        source_path=path,
        source_kind="historical_sidecar_state",
        record_count=count,
        source_hash=evidence_hash,
    )
    report.sidecar_rows += count


def import_workspace_review_binding(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    profile: str = "mat",
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
        task_id = canonicalize_block_id(str(raw.get("task_id", "") or ""), profile)
        if not task_id or not _looks_like_task_id(task_id, profile):
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
                prompt_version=_int_or_none(basis_review.get("prompt_version")),
                rubric_version=_int_or_none(basis_review.get("rubric_version")),
                review_input_path=str(basis_review.get("review_input_path", "") or ""),
                review_input_hash=str(basis_review.get("review_input_hash", "") or ""),
                reviewer_backend_id=str(basis_review.get("reviewer_backend_id", "") or ""),
                provenance={
                    "binding_evidence": str(path),
                    "basis_review_id": str(basis_review.get("review_id", "") or ""),
                    "basis_provenance": _json_value(
                        basis_review.get("provenance_json", "{}")
                    ),
                },
            )
            count += 1
    store.mark_imported(
        source_path=path,
        source_kind="workspace_review_binding",
        record_count=count,
    )
    report.reviews += count
    report.review_bindings += count


def _validated_receipt_subject(
    raw: Any,
    *,
    task_id: str,
    label: str,
    created_at: str,
    allow_legacy_source_provenance: bool = False,
) -> SubjectBundle:
    if not isinstance(raw, Mapping):
        raise ValueError(f"{task_id}: {label} subject is missing")
    if canonicalize_block_id(str(raw.get("task_id", "") or "")) != task_id:
        raise ValueError(f"{task_id}: {label} subject task mismatch")
    required_strings = (
        "subject_id",
        "subject_kind",
        "bundle_hash",
        "primary_hash",
        "primary_path",
    )
    for key in required_strings:
        if not str(raw.get(key, "") or ""):
            raise ValueError(f"{task_id}: {label} subject lacks {key}")
    if not allow_legacy_source_provenance:
        for key in ("source_repo", "source_commit", "layout"):
            if not str(raw.get(key, "") or ""):
                raise ValueError(f"{task_id}: {label} subject lacks {key}")
    files = raw.get("files")
    if not isinstance(files, list) or not files:
        raise ValueError(f"{task_id}: {label} subject lacks a manifest")
    for item in files:
        if not isinstance(item, Mapping):
            raise ValueError(f"{task_id}: {label} manifest entry is not an object")
        content_hash = str(item.get("content_sha256", "") or "")
        git_hash = str(item.get("git_blob_sha", "") or "")
        if not re.fullmatch(r"[0-9a-f]{64}", content_hash):
            raise ValueError(f"{task_id}: {label} manifest has an invalid content hash")
        if not re.fullmatch(r"[0-9a-f]{40}", git_hash):
            raise ValueError(f"{task_id}: {label} manifest has an invalid git blob hash")
        if not str(item.get("path", "") or "") or int(item.get("size", -1)) < 0:
            raise ValueError(f"{task_id}: {label} manifest entry is incomplete")
    subject = SubjectBundle.from_manifest(
        task_id=task_id,
        files=files,
        primary_path=str(raw["primary_path"]),
        source_repo=str(raw["source_repo"]),
        source_commit=str(raw["source_commit"]),
        layout=str(raw["layout"]),
        subject_kind=str(raw["subject_kind"]),
        parent_subject_id=str(raw.get("parent_subject_id", "") or ""),
        created_at=created_at,
    )
    for key, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
    ):
        if str(raw.get(key, "") or "") != actual:
            raise ValueError(f"{task_id}: {label} subject {key} mismatch")
    return subject


def _subject_matches_row(subject: SubjectBundle, row: Mapping[str, Any], *, label: str) -> None:
    manifest = _json_value(row.get("manifest_json", "[]"))
    expected = {
        "subject_id": subject.subject_id,
        "task_id": subject.task_id,
        "subject_kind": subject.subject_kind,
        "source_repo": subject.source_repo,
        "source_commit": subject.source_commit,
        "layout": subject.layout,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path,
        "manifest_hash": sha256_json(subject.manifest()),
    }
    actual = {
        key: str(row.get(key, "") or "")
        for key in expected
        if key != "manifest_hash"
    }
    actual["manifest_hash"] = sha256_json(manifest)
    for key, value in expected.items():
        if actual[key] != value:
            raise ValueError(f"{subject.task_id}: {label} database {key} mismatch")


def _subject_from_row(row: Mapping[str, Any], *, label: str) -> SubjectBundle:
    """Rebuild and verify a database subject from its canonical manifest."""

    manifest = _json_value(row.get("manifest_json", "[]"))
    if not isinstance(manifest, list) or not manifest:
        raise ValueError(f"{label}: database subject manifest is missing")
    task_id = canonicalize_block_id(str(row.get("task_id", "") or ""))
    if not task_id:
        raise ValueError(f"{label}: database subject task id is missing")
    subject = SubjectBundle.from_manifest(
        task_id=task_id,
        files=manifest,
        primary_path=str(row.get("primary_path", "") or ""),
        source_repo=str(row.get("source_repo", "") or ""),
        source_commit=str(row.get("source_commit", "") or ""),
        layout=str(row.get("layout", "") or ""),
        subject_kind=str(row.get("subject_kind", "") or ""),
    )
    _subject_matches_row(subject, row, label=label)
    return subject


def _active_exact_content_target(
    receipt_target: SubjectBundle,
    row: Mapping[str, Any],
    *,
    target_repo: Path | None,
    label: str,
) -> tuple[SubjectBundle, bool]:
    """Resolve an immutable historical target to the active exact-content head.

    Commit-forward is intentionally narrower than review rebinding: the old
    MAT commit must be an ancestor of the active catalog commit and the entire
    canonical task bundle (paths, blobs, content hashes and sizes) must be
    identical.  A changed bundle therefore cannot enter this channel.
    """

    current = _subject_from_row(row, label=f"{label} active target")
    active_commit = str(row.get("mat_commit", "") or "")
    if (
        current.source_repo.lower() != "mat"
        or current.source_commit != active_commit
        or receipt_target.source_repo.lower() != "mat"
        or receipt_target.task_id != current.task_id
    ):
        raise ValueError(f"{receipt_target.task_id}: {label} is not a MAT catalog target")
    if receipt_target.subject_id == current.subject_id:
        return current, False
    if not re.fullmatch(r"[0-9a-f]{40}", receipt_target.source_commit):
        raise ValueError(f"{receipt_target.task_id}: {label} historical commit is invalid")
    if target_repo is None:
        raise ValueError(
            f"{receipt_target.task_id}: {label} commit-forward requires a MAT repository"
        )
    target_repo = target_repo.resolve()
    ancestry = subprocess.run(
        [
            "git", "merge-base", "--is-ancestor",
            receipt_target.source_commit, active_commit,
        ],
        cwd=target_repo,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if ancestry.returncode != 0:
        raise ValueError(
            f"{receipt_target.task_id}: {label} historical target is not an active ancestor"
        )
    exact_fields = (
        receipt_target.subject_kind == current.subject_kind,
        receipt_target.layout == current.layout,
        receipt_target.bundle_hash == current.bundle_hash,
        receipt_target.primary_hash == current.primary_hash,
        receipt_target.primary_path == current.primary_path,
        receipt_target.manifest() == current.manifest(),
    )
    if not all(exact_fields):
        raise ValueError(
            f"{receipt_target.task_id}: {label} bundle changed after the receipt commit"
        )
    return current, True


def _require_current_build_for_changed_consumers(
    store: WorkspaceStateStore,
    *,
    receipt_path: Path,
    consumer_refs: Iterable[Mapping[str, Any]],
    target_repo: Path,
) -> None:
    """Close commit-forward dependency evidence for changed direct consumers."""

    target_repo = target_repo.resolve()
    runtime_root = Path(__file__).resolve().parents[2]
    catalog: TaskCatalog | None = None
    module_context: tuple[Mapping[str, str], Mapping[str, tuple[str, ...]]] | None = None
    for ref in consumer_refs:
        raw_path = Path(str(ref.get("path", "") or ""))
        old_path = raw_path if raw_path.is_absolute() else receipt_path.parent / raw_path
        old_path = old_path.resolve()
        expected_hash = str(ref.get("sha256", "") or "")
        if (
            not old_path.is_file()
            or not re.fullmatch(r"[0-9a-f]{64}", expected_hash)
            or sha256_file(old_path) != expected_hash
        ):
            raise ValueError("commit-forward consumer build reference is invalid")
        old_build = _read_json(old_path)
        if not isinstance(old_build, Mapping):
            raise ValueError("commit-forward consumer build is malformed")
        task_id = canonicalize_block_id(str(old_build.get("task_id", "") or ""))
        if not task_id:
            raise ValueError("commit-forward consumer build task is missing")
        with store._connection(write=store._bulk_connection is not None) as connection:
            row = connection.execute(
                """
                SELECT s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                       s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                       s.primary_path, s.manifest_json, cv.mat_commit
                FROM task_heads h
                JOIN subjects s ON s.subject_id = h.subject_id
                JOIN meta active ON active.key = 'active_catalog_id'
                JOIN catalog_versions cv ON cv.catalog_id = active.value
                WHERE h.task_id = ? AND h.role = 'mat_main'
                  AND h.freshness IN ('fresh', 'local')
                """,
                (task_id,),
            ).fetchone()
        if row is None:
            raise ValueError(f"{task_id}: active direct-consumer subject is missing")
        current = _subject_from_row(dict(row), label=f"{task_id} direct consumer")
        old_manifest = old_build.get("subject_files")
        unchanged = (
            old_build.get("bundle_hash") == current.bundle_hash
            and old_build.get("primary_hash") == current.primary_hash
            and isinstance(old_manifest, list)
            and old_manifest == current.manifest()
        )
        if unchanged:
            continue

        if catalog is None:
            catalog = load_catalog(
                workspace_root=runtime_root.parent,
                runtime_root=runtime_root,
                mat_root=target_repo,
            )
            module_context = catalog_owned_build_modules(catalog, catalog.task_ids())
        assert module_context is not None
        primary_modules, owned_modules = module_context
        exact_root = runtime_root.parent / "toy-apollo-artifacts" / "exact_current_builds"
        candidates: list[Path] = []
        if exact_root.is_dir():
            for commit_root in sorted(exact_root.iterdir(), key=lambda item: item.name):
                candidate = commit_root / task_id / "exact_mat_build_receipt_v1.json"
                if not candidate.is_file():
                    continue
                try:
                    candidate_payload = _read_json(candidate)
                except (OSError, ValueError, json.JSONDecodeError):
                    continue
                if (
                    isinstance(candidate_payload, Mapping)
                    and candidate_payload.get("task_id") == task_id
                    and candidate_payload.get("commit") == current.source_commit
                ):
                    candidates.append(candidate.resolve())
        if len(candidates) != 1:
            raise ValueError(
                f"{task_id}: changed direct consumer has {len(candidates)} current exact-build receipts"
            )
        current_path = candidates[0]
        current_payload = _read_json(current_path)
        focused = current_payload.get("focused_build") if isinstance(current_payload, Mapping) else None
        checkout = Path(str((focused or {}).get("cwd", "") or ""))
        try:
            validate_current_exact_build_receipt(
                current_path,
                subject=current,
                primary_module=str(primary_modules[task_id]),
                task_modules=owned_modules[task_id],
                commit=current.source_commit,
                checkout=checkout,
            )
        except (ExactBuildBatchError, KeyError) as exc:
            raise ValueError(
                f"{task_id}: changed direct-consumer current build is invalid: {exc}"
            ) from exc


def _transformation_check_artifact(
    receipt_path: Path,
    raw: Any,
    *,
    label: str,
    task_id: str,
    target: SubjectBundle,
) -> tuple[Path, str]:
    if not isinstance(raw, Mapping) or str(raw.get("status", "") or "").lower() != "pass":
        raise ValueError(f"{task_id}: {label} check must explicitly pass")
    reference = raw.get("artifact")
    if not isinstance(reference, Mapping):
        raise ValueError(f"{task_id}: {label} evidence reference is missing")
    artifact_path = Path(str(reference.get("path", "") or "")).expanduser()
    if not artifact_path.is_absolute():
        artifact_path = receipt_path.parent / artifact_path
    artifact_path = artifact_path.resolve()
    expected_hash = str(reference.get("sha256", "") or "")
    if not artifact_path.is_file() or not re.fullmatch(r"[0-9a-f]{64}", expected_hash):
        raise ValueError(f"{task_id}: {label} evidence is missing")
    if sha256_file(artifact_path) != expected_hash:
        raise ValueError(f"{task_id}: {label} evidence hash mismatch")
    payload = _read_json(artifact_path)
    if not isinstance(payload, Mapping):
        raise ValueError(f"{task_id}: {label} evidence is not an object")
    expected_identity = {
        "task_id": task_id,
        "subject_id": target.subject_id,
        "bundle_hash": target.bundle_hash,
        "primary_hash": target.primary_hash,
        "commit": target.source_commit,
    }
    for key, value in expected_identity.items():
        if str(payload.get(key, "") or "") != value:
            raise ValueError(f"{task_id}: {label} evidence {key} mismatch")
    if str(payload.get("status", "") or "").lower() != "pass":
        raise ValueError(f"{task_id}: {label} evidence did not pass")
    if label == "build":
        if payload.get("success") is not True or payload.get("exit_code") != 0:
            raise ValueError(f"{task_id}: build evidence is not a successful exit")
    elif label == "forbidden scan":
        if payload.get("matches") != []:
            raise ValueError(f"{task_id}: forbidden scan found matches")
    return artifact_path, expected_hash


def import_validated_transformation_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    target_repo: Path | None = None,
) -> None:
    """Restore one path-only transformation without creating or upgrading a review."""

    if store.import_is_current(path):
        report.skipped += 1
        return
    receipt = _read_json(path)
    if (
        not isinstance(receipt, Mapping)
        or receipt.get("schema") != "toy-apollo.validated-transformation-receipt.v1"
    ):
        raise ValueError("validated transformation receipt has an unsupported schema")
    task_id = canonicalize_block_id(str(receipt.get("task_id", "") or ""))
    if not task_id or not _looks_like_task_id(task_id):
        raise ValueError("validated transformation receipt contains an invalid task id")
    if str(receipt.get("transformation_kind", "") or "") != "path_relocation":
        raise ValueError(f"{task_id}: only path_relocation transformations are supported")
    if str(receipt.get("mechanical_status", "") or "").lower() != "pass":
        raise ValueError(f"{task_id}: transformation must explicitly be mechanical pass")
    created_at = str(receipt.get("created_at", "") or "")
    if not created_at:
        raise ValueError(f"{task_id}: transformation receipt lacks created_at")
    source = _validated_receipt_subject(
        receipt.get("source_subject"),
        task_id=task_id,
        label="source",
        created_at=created_at,
        allow_legacy_source_provenance=True,
    )
    target = _validated_receipt_subject(
        receipt.get("target_subject"),
        task_id=task_id,
        label="target",
        created_at=created_at,
    )
    raw_review = receipt.get("source_review")
    if not isinstance(raw_review, Mapping):
        raise ValueError(f"{task_id}: source review identity is missing")
    review_id = str(raw_review.get("review_id", "") or "")
    if not re.fullmatch(r"[0-9a-f]{64}", review_id):
        raise ValueError(f"{task_id}: source review id is invalid")
    if not re.fullmatch(r"[0-9a-f]{64}", str(raw_review.get("evidence_hash", "") or "")):
        raise ValueError(f"{task_id}: source review evidence hash is invalid")
    with store._connection(write=True) as connection:
        source_row = connection.execute(
            """
            SELECT r.review_id, r.task_id, r.subject_id, r.verdict,
                   r.phase2_status, r.evidence_hash, r.authority_eligible,
                   r.authority_scope, m.prompt_version, m.rubric_version,
                   s.subject_kind, s.source_repo, s.source_commit, s.layout,
                   s.bundle_hash, s.primary_hash, s.primary_path, s.manifest_json
            FROM reviews r
            JOIN review_metadata m ON m.review_id = r.review_id
            JOIN subjects s ON s.subject_id = r.subject_id
            WHERE r.review_id = ? AND r.task_id = ? AND r.subject_id = ?
            """,
            (review_id, task_id, source.subject_id),
        ).fetchone()
        target_row = connection.execute(
            """
            SELECT s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                   s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                   s.primary_path, s.manifest_json, cv.mat_commit
            FROM task_heads h
            JOIN subjects s ON s.subject_id = h.subject_id
            JOIN meta active ON active.key = 'active_catalog_id'
            JOIN catalog_versions cv ON cv.catalog_id = active.value
            WHERE h.task_id = ? AND h.role = 'mat_main' AND h.freshness = 'fresh'
            """,
            (task_id,),
        ).fetchone()
    if source_row is None:
        raise ValueError(f"{task_id}: source review is not present")
    source_values = dict(source_row)
    if (
        str(source_values["verdict"]).lower() != "pass"
        or str(source_values["phase2_status"]).lower() != "pass"
        or int(source_values["authority_eligible"]) != 1
        or int(source_values["prompt_version"] or 0) not in {9, 10, 11}
        or int(source_values["rubric_version"] or 0) != 9
    ):
        raise ValueError(f"{task_id}: source is not an eligible modern applied PASS")
    for key, actual in (
        ("evidence_hash", source_values["evidence_hash"]),
        ("prompt_version", source_values["prompt_version"]),
        ("rubric_version", source_values["rubric_version"]),
    ):
        if str(raw_review.get(key, "") or "") != str(actual):
            raise ValueError(f"{task_id}: source review {key} mismatch")
    _subject_matches_row(source, source_values, label="source")
    if target_row is None:
        raise ValueError(f"{task_id}: current pinned MAT main subject is missing")
    target_values = dict(target_row)
    historical_target = target
    active_target, commit_forwarded = _active_exact_content_target(
        historical_target,
        target_values,
        target_repo=target_repo,
        label="path-relocation target",
    )

    comparison = compare_bundles(
        {
            "bundle_hash": source.bundle_hash,
            "primary_hash": source.primary_hash,
            "manifest_json": source.manifest(),
        },
        {
            "bundle_hash": historical_target.bundle_hash,
            "primary_hash": historical_target.primary_hash,
            "manifest_json": historical_target.manifest(),
        },
    )
    if comparison.classification != "path_only_relocation":
        raise ValueError(
            f"{task_id}: transformation is {comparison.classification}, not path-only relocation"
        )
    declared = receipt.get("comparison")
    if (
        not isinstance(declared, Mapping)
        or declared.get("classification") != "path_only_relocation"
        or declared.get("primary_equal") is not True
        or declared.get("content_multiset_equal") is not True
    ):
        raise ValueError(f"{task_id}: receipt does not declare the validated path-only comparison")
    checks = receipt.get("checks")
    if not isinstance(checks, Mapping):
        raise ValueError(f"{task_id}: transformation checks are missing")
    _transformation_check_artifact(
        path,
        checks.get("build"),
        label="build",
        task_id=task_id,
        target=historical_target,
    )
    _transformation_check_artifact(
        path,
        checks.get("forbidden_scan"),
        label="forbidden scan",
        task_id=task_id,
        target=historical_target,
    )

    evidence_hash = sha256_file(path)
    transformation_id = store.record_transformation(
        task_id=task_id,
        source_subject_id=source.subject_id,
        target_subject_id=active_target.subject_id,
        transformation_kind="path_relocation",
        mechanical_status="pass",
        build_status="pass",
        evidence_path=path,
        evidence_hash=evidence_hash,
    )
    store.record_event(
        event_type="validated_transformation_receipt_imported",
        task_id=task_id,
        subject_id=active_target.subject_id,
        evidence_path=path,
        evidence_hash=evidence_hash,
        occurred_at=created_at,
        payload={
            "transformation_id": transformation_id,
            "source_review_id": review_id,
            "source_subject_id": source.subject_id,
            "target_subject_id": active_target.subject_id,
            "receipt_target_subject_id": historical_target.subject_id,
            "receipt_mat_commit": historical_target.source_commit,
            "pinned_mat_commit": active_target.source_commit,
            "commit_forwarded_exact_bundle": commit_forwarded,
        },
    )
    store.mark_imported(
        source_path=path,
        source_kind="validated_path_relocation_receipt",
        record_count=1,
        source_hash=evidence_hash,
    )
    report.validated_transformation_receipts += 1


def import_verified_boundary_delta_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    source_repos: Iterable[Path],
    target_repo: Path,
    kenneth_repo: Path,
) -> None:
    """Import a validated boundary-only transformation after current heads exist.

    The semantic authority remains the already-imported source review.  This
    function records only the mechanically verified source→target edge; it
    does not create a review or change the source prompt/rubric metadata.
    """

    if store.import_is_current(path):
        report.skipped += 1
        return
    receipt, source, target = validate_verified_boundary_delta(
        path,
        source_repos=tuple(source_repos),
        target_repo=target_repo,
        kenneth_repo=kenneth_repo,
    )
    if (
        receipt.get("schema") != BOUNDARY_DELTA_SCHEMA
        or receipt.get("transformation_kind") != BOUNDARY_DELTA_KIND
        or receipt.get("semantic_upgrade") is not False
    ):
        raise ValueError("verified boundary-delta receipt exceeds its mechanical scope")
    task_id = str(receipt["task_id"])
    source_authority = receipt.get("source_authority")
    artifacts = receipt.get("artifacts")
    checks = receipt.get("checks")
    if not isinstance(source_authority, Mapping) or not isinstance(artifacts, Mapping) or not isinstance(checks, Mapping):
        raise ValueError(f"{task_id}: boundary-delta authority/checks are incomplete")
    required_checks = {
        "source_applied_modern_r9_pass", "source_complete_bundle",
        "target_complete_bundle_at_pinned_commit", "per_file_diff_classified",
        "lean_payload_token_invariant", "public_declaration_signatures_unchanged",
        "import_boundary_exactly_declared", "target_build_and_forbidden_scan",
        "direct_consumers_built_and_scanned", "kenneth_provenance_or_author_decision",
        "no_semantic_or_rubric_upgrade",
    }
    if any(checks.get(key) != "pass" for key in required_checks):
        raise ValueError(f"{task_id}: boundary-delta checks are not all PASS")
    scope_ref = artifacts.get("source_scope")
    if not isinstance(scope_ref, Mapping):
        raise ValueError(f"{task_id}: source scope reference is missing")
    scope_hash = str(scope_ref.get("sha256", "") or "")
    scope_schema = str(scope_ref.get("schema", "") or "")
    recovery_review_id = str(source_authority.get("review_id", "") or "")
    recovery_result_hash = str(source_authority.get("result_evidence_hash", "") or "")
    if scope_schema == RECOVERY_SCHEMA:
        source_predicate = (
            "r.review_id = ? AND r.task_id = ? AND r.subject_id = ? AND r.evidence_hash = ?"
        )
        source_parameters = (
            recovery_review_id, task_id, source.subject_id, recovery_result_hash,
        )
    elif scope_schema == "toy-apollo.workspace-review-binding.v1":
        source_predicate = "r.task_id = ? AND r.subject_id = ? AND r.evidence_hash = ?"
        source_parameters = (task_id, source.subject_id, scope_hash)
    else:
        raise ValueError(f"{task_id}: unsupported imported full-bundle scope schema {scope_schema!r}")
    # Rebuilds run inside one bulk transaction.  Use that same connection so
    # the source authority and freshly reconciled MAT head are visible before
    # the transaction commits; a separate read-only connection sees neither.
    with store._connection(write=store._bulk_connection is not None) as connection:
        source_row = connection.execute(
            f"""
            SELECT r.review_id, r.verdict, r.phase2_status, r.authority_eligible,
                   r.authority_scope, m.provenance_json,
                   m.prompt_version, m.rubric_version,
                   s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                   s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                   s.primary_path, s.manifest_json
            FROM reviews r
            JOIN review_metadata m ON m.review_id = r.review_id
            JOIN subjects s ON s.subject_id = r.subject_id
            WHERE {source_predicate}
            """,
            source_parameters,
        ).fetchone()
        target_row = connection.execute(
            """
            SELECT s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                   s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                   s.primary_path, s.manifest_json, cv.mat_commit
            FROM task_heads h
            JOIN subjects s ON s.subject_id = h.subject_id
            JOIN meta active ON active.key = 'active_catalog_id'
            JOIN catalog_versions cv ON cv.catalog_id = active.value
            WHERE h.task_id = ? AND h.role = 'mat_main' AND h.freshness = 'fresh'
            """,
            (task_id,),
        ).fetchone()
    if source_row is None:
        raise ValueError(f"{task_id}: validated complete source bundle review is not present")
    source_values = dict(source_row)
    provenance = _json_value(source_values.get("provenance_json", "{}"))
    scope_authority_bound = (
        str(source_values["review_id"]) == recovery_review_id
        if scope_schema == RECOVERY_SCHEMA
        else isinstance(provenance, Mapping)
        and str(provenance.get("basis_review_id", "") or "") == recovery_review_id
    )
    if (
        str(source_values["verdict"]).lower() != "pass"
        or str(source_values["phase2_status"]).lower() != "pass"
        or int(source_values["authority_eligible"]) != 1
        or int(source_values["prompt_version"] or 0) not in {9, 10, 11}
        or int(source_values["rubric_version"] or 0) != 9
        or not scope_authority_bound
    ):
        raise ValueError(f"{task_id}: source bundle is not bound to the recovered modern r9 PASS")
    if int(source_authority.get("prompt_version", 0) or 0) != int(source_values["prompt_version"] or 0) or int(source_authority.get("rubric_version", 0) or 0) != int(source_values["rubric_version"] or 0):
        raise ValueError(f"{task_id}: source authority prompt/rubric mismatch")
    _subject_matches_row(source, source_values, label="source")
    if target_row is None:
        raise ValueError(f"{task_id}: current pinned MAT main subject is missing")
    target_values = dict(target_row)
    historical_target = target
    active_target, commit_forwarded = _active_exact_content_target(
        historical_target,
        target_values,
        target_repo=target_repo,
        label="boundary-delta target",
    )
    if commit_forwarded:
        consumer_refs = artifacts.get("consumer_builds")
        if not isinstance(consumer_refs, list) or any(
            not isinstance(item, Mapping) for item in consumer_refs
        ):
            raise ValueError(f"{task_id}: boundary consumer build references are malformed")
        _require_current_build_for_changed_consumers(
            store,
            receipt_path=path,
            consumer_refs=consumer_refs,
            target_repo=target_repo,
        )

    evidence_hash = sha256_file(path)
    transformation_id = store.record_transformation(
        task_id=task_id,
        source_subject_id=source.subject_id,
        target_subject_id=active_target.subject_id,
        transformation_kind=BOUNDARY_DELTA_KIND,
        mechanical_status="pass",
        build_status="pass",
        evidence_path=path,
        evidence_hash=evidence_hash,
    )
    store.record_event(
        event_type="verified_boundary_delta_receipt_imported",
        task_id=task_id,
        subject_id=active_target.subject_id,
        evidence_path=path,
        evidence_hash=evidence_hash,
        occurred_at=str(receipt.get("created_at", "") or ""),
        payload={
            "transformation_id": transformation_id,
            "source_review_id": str(source_values["review_id"]),
            "source_authority_review_id": recovery_review_id,
            "source_subject_id": source.subject_id,
            "target_subject_id": active_target.subject_id,
            "receipt_target_subject_id": historical_target.subject_id,
            "receipt_mat_commit": historical_target.source_commit,
            "pinned_mat_commit": active_target.source_commit,
            "commit_forwarded_exact_bundle": commit_forwarded,
            "semantic_upgrade": False,
        },
    )
    store.mark_imported(
        source_path=path,
        source_kind="verified_boundary_delta_receipt",
        record_count=1,
        source_hash=evidence_hash,
    )
    report.boundary_delta_receipts += 1


def import_validated_evidence_bridge_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    source_repos: Iterable[Path],
    target_repo: Path,
    kenneth_repo: Path,
) -> None:
    """Import a typed A/B authority edge without creating a target review.

    Validation, including rejection of the unrepresentable C category, occurs
    before the first state mutation.  The store then writes subjects,
    transformation, typed binding, import marker and event in one transaction.
    """

    evidence_hash = sha256_file(path)
    if store.import_is_current(path, source_hash=evidence_hash):
        report.skipped += 1
        return
    receipt, source, target = validate_evidence_bridge_receipt(
        path,
        source_repos=tuple(source_repos),
        target_repo=target_repo,
        kenneth_repo=kenneth_repo,
    )
    if (
        receipt.get("schema") != EVIDENCE_BRIDGE_SCHEMA
        or receipt.get("transformation_kind") != EVIDENCE_BRIDGE_KIND
        or receipt.get("mechanical_status") != "pass"
        or receipt.get("semantic_upgrade") is not False
        or receipt.get("rubric_upgrade") is not False
        or receipt.get("creates_review") is not False
    ):
        raise ValueError("evidence bridge exceeds its mechanical non-review scope")
    task_id = str(receipt["task_id"])
    authority = receipt.get("source_authority")
    if not isinstance(authority, Mapping):
        raise ValueError(f"{task_id}: evidence bridge source authority is missing")
    authority_type = str(authority.get("type", "") or "")
    capability = str(authority.get("capability", "") or "")
    decision_ref = authority.get("decision")
    if not isinstance(decision_ref, Mapping):
        raise ValueError(f"{task_id}: evidence bridge decision reference is missing")

    # Read current state only after the receipt has fully replayed.  A rejected
    # C/unknown/partial manifest therefore has exactly zero state writes.
    with store._connection(write=store._bulk_connection is not None) as connection:
        target_row = connection.execute(
            """
            SELECT s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                   s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                   s.primary_path, s.manifest_json,
                   cv.mat_commit
            FROM task_heads h
            JOIN subjects s ON s.subject_id = h.subject_id
            JOIN meta active ON active.key = 'active_catalog_id'
            JOIN catalog_versions cv ON cv.catalog_id = active.value
            WHERE h.task_id = ? AND h.role = 'mat_main'
              AND h.freshness IN ('fresh', 'local')
            """,
            (task_id,),
        ).fetchone()
        source_review = None
        if authority_type not in {AUTHORITY_KENNETH, AUTHORITY_MAT_SYNC}:
            source_review = connection.execute(
                """
                SELECT r.review_id, r.verdict, r.phase2_status,
                       r.authority_eligible, m.prompt_version, m.rubric_version,
                       s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                       s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                       s.primary_path, s.manifest_json
                FROM reviews r
                JOIN review_metadata m ON m.review_id = r.review_id
                JOIN subjects s ON s.subject_id = r.subject_id
                WHERE r.task_id = ? AND r.subject_id = ?
                  AND r.review_id = ? AND r.evidence_hash = ?
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND m.prompt_version IN (9, 10, 11) AND m.rubric_version = 9
                ORDER BY r.reviewed_at DESC LIMIT 1
                """,
                (
                    task_id, source.subject_id,
                    str(authority.get("review_id", "") or ""),
                    str(authority.get("source_evidence_hash", "") or ""),
                ),
            ).fetchone()
    if target_row is None:
        raise ValueError(f"{task_id}: active catalog-pinned MAT target is missing")
    target_values = dict(target_row)
    historical_target = target
    target, commit_forwarded = _active_exact_content_target(
        historical_target,
        target_values,
        target_repo=target_repo,
        label="evidence-bridge target",
    )
    if commit_forwarded:
        artifacts = receipt.get("artifacts")
        consumer_refs = artifacts.get("consumer_builds") if isinstance(artifacts, Mapping) else None
        if not isinstance(consumer_refs, list) or any(
            not isinstance(ref, Mapping) for ref in consumer_refs
        ):
            raise ValueError(f"{task_id}: evidence-bridge consumer builds are malformed")
        _require_current_build_for_changed_consumers(
            store,
            receipt_path=path,
            consumer_refs=consumer_refs,
            target_repo=target_repo,
        )
    if authority_type not in {AUTHORITY_KENNETH, AUTHORITY_MAT_SYNC}:
        if source_review is None:
            raise ValueError(f"{task_id}: reviewed B source is not present in state")
        _subject_matches_row(source, dict(source_review), label="source")
    else:
        # A and explicit sync-B attach an immutable decision to the exact
        # current content; their historical source/target IDs differ only by
        # the commit anchor after a validated commit-forward.
        source = target

    binding_id, transformation_id = store.record_evidence_bridge_binding(
        source=source,
        target=target,
        bridge_route=str(receipt["bridge_route"]),
        authority_type=authority_type,
        capability=capability,
        decision_path=Path(str(decision_ref.get("path", "") or "")),
        decision_hash=str(decision_ref.get("sha256", "") or ""),
        evidence_path=path,
        evidence_hash=evidence_hash,
        created_at=str(receipt.get("created_at", "") or ""),
    )
    if not binding_id or not transformation_id:
        raise ValueError(f"{task_id}: evidence bridge state identity was not recorded")
    report.evidence_bridge_receipts += 1


def import_validated_evidence_bridge_batch_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    target_repo: Path,
    kenneth_repo: Path,
) -> None:
    """Replay and atomically import one closed final122 A/B batch."""

    path = path.resolve()
    payload, evidence_hash = load_validated_final122_bridge_batch_receipt(
        path, target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    items = payload.get("items")
    if (
        payload.get("schema") != FINAL122_BATCH_RECEIPT_SCHEMA
        or not isinstance(items, list) or not items
        or payload.get("count") != len(items)
        or len({_task_id(item) for item in items if isinstance(item, Mapping)}) != len(items)
    ):
        raise ValueError("evidence bridge batch identity/count is invalid")

    prepared: list[tuple[Mapping[str, Any], SubjectBundle, Mapping[str, Any]]] = []
    with store._connection(write=store._bulk_connection is not None) as connection:
        for item in items:
            if not isinstance(item, Mapping):
                raise ValueError("evidence bridge batch item is malformed")
            task_id = _task_id(item)
            target_raw = item.get("target_subject")
            if not task_id or not isinstance(target_raw, Mapping):
                raise ValueError("evidence bridge batch item target is missing")
            historical_target = SubjectBundle.from_manifest(
                task_id=task_id,
                files=target_raw.get("files", []),
                primary_path=str(target_raw.get("primary_path", "") or ""),
                source_repo=str(target_raw.get("source_repo", "") or ""),
                source_commit=str(target_raw.get("source_commit", "") or ""),
                layout=str(target_raw.get("layout", "") or ""),
                subject_kind=str(target_raw.get("subject_kind", "") or ""),
            )
            if any(
                str(target_raw.get(key, "") or "") != value
                for key, value in (
                    ("subject_id", historical_target.subject_id),
                    ("bundle_hash", historical_target.bundle_hash),
                    ("primary_hash", historical_target.primary_hash),
                )
            ):
                raise ValueError(f"{task_id}: batch target subject identity mismatch")
            row = connection.execute(
                """
                SELECT s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                       s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                       s.primary_path, s.manifest_json, cv.mat_commit
                FROM task_heads h
                JOIN subjects s ON s.subject_id = h.subject_id
                JOIN meta active ON active.key = 'active_catalog_id'
                JOIN catalog_versions cv ON cv.catalog_id = active.value
                WHERE h.task_id = ? AND h.role = 'mat_main'
                  AND h.freshness IN ('fresh', 'local')
                """,
                (task_id,),
            ).fetchone()
            if row is None:
                raise ValueError(f"{task_id}: active catalog-pinned MAT target is missing")
            values = dict(row)
            target, commit_forwarded = _active_exact_content_target(
                historical_target,
                values,
                target_repo=target_repo,
                label="evidence-bridge batch target",
            )
            if commit_forwarded:
                artifacts = item.get("artifacts")
                consumer_refs = artifacts.get("consumer_builds") if isinstance(artifacts, Mapping) else None
                if not isinstance(consumer_refs, list) or any(
                    not isinstance(ref, Mapping) for ref in consumer_refs
                ):
                    raise ValueError(f"{task_id}: batch consumer build references are malformed")
                _require_current_build_for_changed_consumers(
                    store,
                    receipt_path=path,
                    consumer_refs=consumer_refs,
                    target_repo=target_repo,
                )
            authority = item.get("source_authority")
            if not isinstance(authority, Mapping) or not isinstance(authority.get("decision"), Mapping):
                raise ValueError(f"{task_id}: batch typed authority is missing")
            prepared.append((item, target, authority))

    # Full replay and every active-target check above precede the first write.
    with store.atomic_write("evidence_bridge_batch") as connection:
        source_path = stable_absolute_path(path)
        existing_import = connection.execute(
            "SELECT source_hash, source_kind, record_count FROM imports WHERE source_path = ?",
            (source_path,),
        ).fetchone()
        if existing_import is not None:
            expected_binding_ids: set[str] = set()
            for item, target, authority in prepared:
                decision = authority["decision"]
                transformation_id = sha256_json({
                    "schema": "toy-apollo.transformation.v1",
                    "source": target.subject_id,
                    "target": target.subject_id,
                    "kind": "verified_evidence_bridge",
                })
                binding_id = sha256_json({
                    "schema": "toy-apollo.typed-authority-binding.v1",
                    "task_id": target.task_id,
                    "source_subject_id": target.subject_id,
                    "target_subject_id": target.subject_id,
                    "bridge_route": str(item["bridge_route"]),
                    "authority_type": str(authority.get("type", "") or ""),
                    "capability": str(authority.get("capability", "") or ""),
                    "decision_hash": str(decision.get("sha256", "") or ""),
                    "evidence_hash": evidence_hash,
                })
                expected_binding_ids.add(binding_id)
                binding = connection.execute(
                    """
                    SELECT b.*, v.binding_id AS valid_binding_id,
                           t.evidence_path AS transformation_evidence_path,
                           t.evidence_hash AS transformation_evidence_hash
                    FROM authority_bindings b
                    LEFT JOIN valid_authority_bindings v ON v.binding_id = b.binding_id
                    JOIN transformations t ON t.transformation_id = b.transformation_id
                    WHERE b.binding_id = ?
                    """,
                    (binding_id,),
                ).fetchone()
                expected = {
                    "task_id": target.task_id,
                    "source_subject_id": target.subject_id,
                    "target_subject_id": target.subject_id,
                    "transformation_id": transformation_id,
                    "bridge_route": str(item["bridge_route"]),
                    "authority_type": str(authority.get("type", "") or ""),
                    "capability": str(authority.get("capability", "") or ""),
                    "decision_path": stable_absolute_path(str(decision.get("path", "") or "")),
                    "decision_hash": str(decision.get("sha256", "") or ""),
                    "evidence_path": source_path,
                    "evidence_hash": evidence_hash,
                    "created_at": str(item.get("created_at", "") or ""),
                    "valid_binding_id": binding_id,
                    "transformation_evidence_path": source_path,
                    "transformation_evidence_hash": evidence_hash,
                }
                if binding is None or any(
                    str(binding[key]) != str(value) for key, value in expected.items()
                ):
                    raise ValueError(
                        f"{target.task_id}: evidence bridge batch idempotent binding mismatch"
                    )
            actual_binding_ids = {
                str(row["binding_id"])
                for row in connection.execute(
                    """
                    SELECT binding_id FROM authority_bindings
                    WHERE evidence_path = ? AND evidence_hash = ?
                    """,
                    (source_path, evidence_hash),
                ).fetchall()
            }
            valid_binding_ids = {
                str(row["binding_id"])
                for row in connection.execute(
                    """
                    SELECT binding_id FROM valid_authority_bindings
                    WHERE evidence_path = ? AND evidence_hash = ?
                    """,
                    (source_path, evidence_hash),
                ).fetchall()
            }
            if (
                str(existing_import["source_hash"]) != evidence_hash
                or str(existing_import["source_kind"])
                != "validated_evidence_bridge_batch_receipt"
                or int(existing_import["record_count"]) != len(prepared)
                or actual_binding_ids != expected_binding_ids
                or valid_binding_ids != expected_binding_ids
            ):
                raise ValueError("evidence bridge batch idempotent state mismatch")
            report.skipped += 1
            return
        for item, target, authority in prepared:
            decision = authority["decision"]
            store.record_evidence_bridge_binding(
                source=target,
                target=target,
                bridge_route=str(item["bridge_route"]),
                authority_type=str(authority.get("type", "") or ""),
                capability=str(authority.get("capability", "") or ""),
                decision_path=Path(str(decision.get("path", "") or "")),
                decision_hash=str(decision.get("sha256", "") or ""),
                evidence_path=path,
                evidence_hash=evidence_hash,
                created_at=str(item.get("created_at", "") or ""),
                record_import=False,
            )
        store.mark_imported(
            source_path=path,
            source_kind="validated_evidence_bridge_batch_receipt",
            record_count=len(prepared),
            source_hash=evidence_hash,
        )
    report.evidence_bridge_receipts += len(prepared)
    report.evidence_bridge_batch_receipts += 1


def import_historical_review_apply_recovery_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
) -> None:
    """Recover an old canonical apply on its original exact subject only."""

    if store.import_is_current(path):
        report.skipped += 1
        return
    receipt, subject = validate_historical_review_apply_recovery(path)
    if (
        receipt.get("schema") != RECOVERY_SCHEMA
        or receipt.get("authority_scope") != RECOVERY_AUTHORITY_SCOPE
        or receipt.get("semantic_upgrade") is not False
        or receipt.get("current_target_binding") is not False
    ):
        raise ValueError("historical review-apply recovery exceeds its source-subject scope")
    task_id = str(receipt["task_id"])
    source_review = receipt.get("source_review")
    artifacts = receipt.get("artifacts")
    if not isinstance(source_review, Mapping) or not isinstance(artifacts, Mapping):
        raise ValueError(f"{task_id}: historical review-apply recovery is incomplete")
    result_ref = artifacts.get("result")
    input_ref = artifacts.get("input")
    if not isinstance(result_ref, Mapping) or not isinstance(input_ref, Mapping):
        raise ValueError(f"{task_id}: historical review-apply recovery lacks review artifacts")
    result_path = (path.parent / str(result_ref.get("path", "") or "")).resolve()
    input_path = (path.parent / str(input_ref.get("path", "") or "")).resolve()
    result_hash = str(result_ref.get("sha256", "") or "")
    independence = source_review.get("reviewer_independence")
    if not isinstance(independence, Mapping):
        raise ValueError(f"{task_id}: recovered review independence is missing")

    store.upsert_subject(subject)
    expected_review_id = str(source_review.get("review_id", "") or "")
    # Recovery subjects and earlier receipt rows may have been inserted in the
    # same bulk rebuild transaction.  Query through that transaction so a
    # conflicting identity cannot be hidden until commit.
    with store._connection(write=store._bulk_connection is not None) as connection:
        existing = connection.execute(
            "SELECT review_id, authority_eligible FROM reviews "
            "WHERE subject_id = ? AND evidence_hash = ?",
            (subject.subject_id, result_hash),
        ).fetchone()
    if existing is not None and str(existing["review_id"]) != expected_review_id:
        raise ValueError(
            f"{task_id}: an older non-recovery review identity already occupies this evidence; "
            "run a clean canonical rebuild"
        )
    review_id = store.record_review(
        task_id=task_id,
        subject_id=subject.subject_id,
        verdict="pass",
        proof_class=str(source_review.get("proof_class", "") or ""),
        completion_class=str(source_review.get("completion_class", "") or ""),
        phase2_status="pass",
        evidence_path=result_path,
        evidence_hash=result_hash,
        reviewer_independence=json.dumps(dict(independence), ensure_ascii=False, sort_keys=True),
        authority_scope=RECOVERY_AUTHORITY_SCOPE,
        authority_eligible=True,
        reviewed_at=str(source_review.get("applied_at", "") or receipt.get("created_at", "") or ""),
        prompt_version=int(source_review.get("prompt_version", 0) or 0),
        rubric_version=int(source_review.get("rubric_version", 0) or 0),
        review_input_path=input_path,
        review_input_hash=str(input_ref.get("canonical_sha256", "") or ""),
        reviewer_backend_id=str(source_review.get("reviewer_backend_id", "") or ""),
        provenance={
            "import_kind": "historical_canonical_review_apply_recovery",
            "recovery_receipt_path": str(path),
            "recovery_receipt_hash": sha256_file(path),
            "source_subject_only": True,
            "semantic_upgrade": False,
            "current_target_binding": False,
        },
    )
    if review_id != expected_review_id:
        raise ValueError(f"{task_id}: recovered review identity mismatch")
    receipt_hash = sha256_file(path)
    store.record_event(
        event_type="historical_review_apply_recovered",
        task_id=task_id,
        subject_id=subject.subject_id,
        evidence_path=path,
        evidence_hash=receipt_hash,
        occurred_at=str(receipt.get("created_at", "") or ""),
        payload={
            "review_id": review_id,
            "authority_scope": RECOVERY_AUTHORITY_SCOPE,
            "source_subject_only": True,
            "semantic_upgrade": False,
            "current_target_binding": False,
        },
    )
    store.mark_imported(
        source_path=path,
        source_kind="historical_review_apply_recovery_receipt",
        record_count=1,
        source_hash=receipt_hash,
    )
    report.reviews += 1
    report.historical_apply_recovery_receipts += 1


def import_resolved_invalidation_recovery_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    target_repo: Path | None = None,
) -> None:
    """Promote a current exact subject only through a validated invalidation fix.

    The old apply receipt remains immutable and rejected.  This imports a new
    authority record whose provenance names the old semantic result and the
    fresh build evidence; it does not alter either artifact or invent a verdict.
    """

    if store.import_is_current(path):
        report.skipped += 1
        return
    receipt, target, result_path, input_path = validate_resolved_invalidation_recovery(path)
    if (
        receipt.get("schema") != RESOLVED_INVALIDATION_SCHEMA
        or receipt.get("authority_scope") != RESOLVED_INVALIDATION_AUTHORITY_SCOPE
        or receipt.get("semantic_upgrade") is not False
    ):
        raise ValueError("resolved-invalidation recovery exceeds its narrow authority scope")
    task_id = str(receipt["task_id"])
    source_review = receipt.get("source_review")
    if not isinstance(source_review, Mapping):
        raise ValueError(f"{task_id}: recovery lacks source review identity")
    # The current MAT head was inserted earlier in the same bulk rebuild
    # transaction.  A separate read-only connection cannot see that
    # uncommitted row and would falsely reject every valid recovery receipt.
    with store._connection(write=store._bulk_connection is not None) as connection:
        target_row = connection.execute(
            """
            SELECT s.subject_id, s.task_id, s.subject_kind, s.source_repo,
                   s.source_commit, s.layout, s.bundle_hash, s.primary_hash,
                   s.primary_path, s.manifest_json, cv.mat_commit
            FROM task_heads h
            JOIN subjects s ON s.subject_id = h.subject_id
            JOIN meta active ON active.key = 'active_catalog_id'
            JOIN catalog_versions cv ON cv.catalog_id = active.value
            WHERE h.task_id = ? AND h.role = 'mat_main' AND h.freshness = 'fresh'
            """,
            (task_id,),
        ).fetchone()
    if target_row is None:
        raise ValueError(f"{task_id}: current pinned MAT main subject is missing")
    values = dict(target_row)
    historical_target = target
    target, commit_forwarded = _active_exact_content_target(
        historical_target,
        values,
        target_repo=target_repo,
        label="resolved-invalidation target",
    )
    if commit_forwarded:
        resolution = receipt.get("resolution")
        dependency_refs: list[Mapping[str, Any]] = []
        if isinstance(resolution, Mapping):
            for key in ("consumer_builds", "invalidator_builds"):
                raw_refs = resolution.get(key)
                if not isinstance(raw_refs, list) or any(
                    not isinstance(ref, Mapping) for ref in raw_refs
                ):
                    raise ValueError(f"{task_id}: recovery {key} references are malformed")
                dependency_refs.extend(raw_refs)
        else:
            raise ValueError(f"{task_id}: recovery dependency resolution is missing")
        assert target_repo is not None
        _require_current_build_for_changed_consumers(
            store,
            receipt_path=path,
            consumer_refs=dependency_refs,
            target_repo=target_repo,
        )
    result_hash = str(source_review.get("result_hash", "") or "")
    if sha256_file(result_path) != result_hash:
        raise ValueError(f"{task_id}: recovered semantic result hash mismatch")
    independence = source_review.get("reviewer_independence")
    if not isinstance(independence, Mapping):
        raise ValueError(f"{task_id}: recovered reviewer independence is missing")
    store.upsert_subject(target)
    review_id = store.record_review(
        task_id=task_id,
        subject_id=target.subject_id,
        verdict="pass",
        proof_class=str(source_review.get("proof_class", "") or ""),
        completion_class=str(source_review.get("completion_class", "") or ""),
        phase2_status="pass",
        evidence_path=result_path,
        evidence_hash=result_hash,
        reviewer_independence=json.dumps(dict(independence), ensure_ascii=False, sort_keys=True),
        authority_scope=RESOLVED_INVALIDATION_AUTHORITY_SCOPE,
        authority_eligible=True,
        reviewed_at=str(receipt.get("created_at", "") or ""),
        prompt_version=int(source_review.get("prompt_version", 0) or 0),
        rubric_version=int(source_review.get("rubric_version", 0) or 0),
        review_input_path=input_path,
        review_input_hash=str(source_review.get("review_input_hash", "") or ""),
        reviewer_backend_id=str(source_review.get("reviewer_backend_id", "") or ""),
        provenance={
            "import_kind": "resolved_dependency_invalidation_current_exact_recovery",
            "recovery_receipt_path": str(path),
            "recovery_receipt_hash": sha256_file(path),
            "semantic_upgrade": False,
            "stale_receipt_preserved": True,
            "invalidated_by": str((receipt.get("resolution") or {}).get("invalidated_by", "") or ""),
            "receipt_target_subject_id": historical_target.subject_id,
            "receipt_mat_commit": historical_target.source_commit,
            "active_mat_commit": target.source_commit,
            "commit_forwarded_exact_bundle": commit_forwarded,
        },
    )
    receipt_hash = sha256_file(path)
    store.record_event(
        event_type="resolved_invalidation_recovery_imported",
        task_id=task_id,
        subject_id=target.subject_id,
        evidence_path=path,
        evidence_hash=receipt_hash,
        occurred_at=str(receipt.get("created_at", "") or ""),
        payload={"review_id": review_id, "authority_scope": RESOLVED_INVALIDATION_AUTHORITY_SCOPE},
    )
    store.mark_imported(
        source_path=path,
        source_kind="resolved_invalidation_current_exact_recovery_receipt",
        record_count=1,
        source_hash=receipt_hash,
    )
    report.reviews += 1
    report.resolved_invalidation_recovery_receipts += 1


def import_mat_review_apply_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
) -> None:
    """Restore one exact MAT bundle PASS from its immutable apply receipt."""

    if store.import_is_current(path):
        report.skipped += 1
        return
    receipt = _read_json(path)
    if not isinstance(receipt, Mapping) or receipt.get("schema") != "mat.rubric78.review-apply-receipt.v1":
        raise ValueError("MAT review apply receipt has an unsupported schema")
    task_id = canonicalize_block_id(str(receipt.get("task_id", "") or ""))
    if not task_id or not _looks_like_task_id(task_id):
        raise ValueError("MAT review apply receipt contains an invalid task id")
    if (
        receipt.get("authority_eligible") is not True
        or receipt.get("clean_pass") is not True
        or receipt.get("exact_bundle_covered") is not True
        or str(receipt.get("verdict", "") or "").lower() != "pass"
        or str(receipt.get("phase2_status", "") or "").lower() != "pass"
        or str(receipt.get("invalidated_by", "") or "")
    ):
        raise ValueError(f"{task_id}: MAT review receipt is not an active exact clean PASS")

    result_path = _artifact_path_from_reference(
        path,
        receipt.get("review_result_file", ""),
        fallback_names=(Path(str(receipt.get("review_result_file", "") or "")).name,),
    )
    if result_path is None:
        raise ValueError(f"{task_id}: MAT receipt review result is missing")
    result_hash = sha256_file(result_path)
    if result_hash != str(receipt.get("review_result_hash", "") or ""):
        raise ValueError(f"{task_id}: MAT receipt review result hash mismatch")
    result = _read_json(result_path)
    if not isinstance(result, Mapping):
        raise ValueError(f"{task_id}: MAT review result is not an object")
    if (
        canonicalize_block_id(str(result.get("task_id", "") or "")) != task_id
        or str(result.get("verdict", "") or "").lower() != "pass"
        or str(result.get("phase2_status", "") or "").lower() != "pass"
    ):
        raise ValueError(f"{task_id}: MAT review result does not match the PASS receipt")
    prompt_version = _int_or_none(result.get("prompt_version", ""))
    rubric_version = _int_or_none(result.get("rubric_version", ""))
    if prompt_version not in {9, 10, 11} or rubric_version != 9:
        raise ValueError(
            f"{task_id}: MAT receipt does not use a current-compatible prompt/rubric "
            f"({prompt_version}/{rubric_version})"
        )

    input_path, input_payload, computed_input_hash = _review_input_for_result(result_path, result)
    if input_path is None or input_payload is None:
        raise ValueError(f"{task_id}: MAT review input is missing")
    expected_input_hash = str(receipt.get("review_input_hash", "") or "")
    if not expected_input_hash or expected_input_hash != computed_input_hash:
        raise ValueError(f"{task_id}: MAT receipt review input hash mismatch")
    if str(result.get("review_input_hash", "") or "") != expected_input_hash:
        raise ValueError(f"{task_id}: MAT result and receipt input hashes differ")
    reviewed_at = str(receipt.get("applied_at", "") or _reviewed_at(result_path, result, input_payload))
    subject = _exact_subject_from_review_input(
        task_id=task_id,
        input_payload=input_payload,
        created_at=reviewed_at,
    )
    if subject is None:
        raise ValueError(f"{task_id}: MAT receipt lacks an exact subject bundle")
    for key, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
        ("commit", subject.source_commit),
    ):
        if str(receipt.get(key, "") or "") != actual:
            raise ValueError(f"{task_id}: MAT receipt {key} mismatch")
    if str(result.get("candidate_hash", "") or "") != subject.primary_hash:
        raise ValueError(f"{task_id}: MAT result candidate hash mismatch")
    independence = result.get("reviewer_independence")
    if not isinstance(independence, Mapping) or independence.get("read_only") is not True:
        raise ValueError(f"{task_id}: MAT review lacks read-only reviewer independence")
    if independence.get("did_edit_candidate") is not False:
        raise ValueError(f"{task_id}: MAT reviewer independence is invalid")

    store.upsert_subject(subject)
    review_id = store.record_review(
        task_id=task_id,
        subject_id=subject.subject_id,
        verdict="pass",
        proof_class=str(receipt.get("proof_class", "") or result.get("proof_class", "") or ""),
        completion_class=str(
            receipt.get("completion_class", "") or result.get("completion_class", "") or ""
        ),
        phase2_status="pass",
        evidence_path=result_path,
        evidence_hash=result_hash,
        reviewer_independence=json.dumps(dict(independence), ensure_ascii=False, sort_keys=True),
        authority_scope="mat_final_exact_bundle_review",
        authority_eligible=True,
        reviewed_at=reviewed_at,
        prompt_version=prompt_version,
        rubric_version=rubric_version,
        review_input_path=input_path,
        review_input_hash=expected_input_hash,
        reviewer_backend_id=str(result.get("reviewer_backend_id", "") or ""),
        provenance={
            "import_kind": "mat_exact_review_apply_receipt",
            "receipt_path": str(path),
            "receipt_hash": sha256_file(path),
            "campaign_id": receipt.get("campaign_id", ""),
            "attempt": receipt.get("attempt", result.get("attempt", "")),
        },
    )
    if str(receipt.get("review_id", "") or "") != review_id:
        raise ValueError(f"{task_id}: MAT receipt review identity mismatch")
    evidence_hash = sha256_file(path)
    store.record_event(
        event_type="review_applied",
        task_id=task_id,
        subject_id=subject.subject_id,
        evidence_path=path,
        evidence_hash=evidence_hash,
        occurred_at=reviewed_at,
        payload={
            "review_id": review_id,
            "authority_scope": "mat_final_exact_bundle_review",
            "prompt_version": prompt_version,
            "rubric_version": rubric_version,
            "campaign_id": receipt.get("campaign_id", ""),
        },
    )
    store.mark_imported(
        source_path=path,
        source_kind="mat_exact_review_apply_receipt",
        record_count=1,
    )
    report.reviews += 1
    report.mat_review_receipts += 1


def _phase2_receipt_subject(
    raw: Any,
    *,
    task_id: str,
    label: str,
    created_at: str,
    profile: str,
) -> SubjectBundle:
    if not isinstance(raw, Mapping):
        raise ValueError(f"{task_id}: {label} is missing")
    if canonicalize_block_id(str(raw.get("task_id", "") or ""), profile) != task_id:
        raise ValueError(f"{task_id}: {label} task mismatch")
    subject = SubjectBundle.from_manifest(
        task_id=task_id,
        files=raw.get("files", []),
        primary_path=str(raw.get("primary_path", "") or ""),
        source_repo=str(raw.get("source_repo", "") or ""),
        source_commit=str(raw.get("source_commit", "") or ""),
        layout=str(raw.get("layout", "") or ""),
        subject_kind=str(raw.get("subject_kind", "") or "review_bundle"),
        parent_subject_id=str(raw.get("parent_subject_id", "") or ""),
        created_at=created_at,
    )
    for key, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
    ):
        if str(raw.get(key, "") or "") != actual:
            raise ValueError(f"{task_id}: {label} {key} mismatch")
    return subject


def _phase2_receipt_artifact(receipt_path: Path, raw: Any, *, label: str) -> Path:
    path = Path(str(raw or "")).expanduser()
    if not path.is_absolute():
        path = receipt_path.parent / path
    path = path.resolve()
    if not path.is_file():
        raise ValueError(f"Phase2 review-apply receipt {label} is missing: {path}")
    return path


def _phase2_receipt_bundles_equivalent(
    source: SubjectBundle,
    target: SubjectBundle,
) -> bool:
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


def import_phase2_review_apply_receipt(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    profile: str,
) -> None:
    """Restore one authority-eligible review and its exact output relocation."""

    if store.import_is_current(path):
        report.skipped += 1
        return
    receipt = _read_json(path)
    if (
        not isinstance(receipt, Mapping)
        or receipt.get("schema_version")
        != "toy-apollo.phase2-review-apply-receipt.v1"
    ):
        raise ValueError("Unsupported Phase2 review-apply receipt schema")
    receipt_profile = str(receipt.get("profile", "") or "").strip().lower()
    if receipt_profile != profile:
        raise ValueError(
            f"Phase2 review-apply receipt profile mismatch: {receipt_profile!r} != {profile!r}"
        )
    task_id = canonicalize_block_id(str(receipt.get("task_id", "") or ""), profile)
    if not task_id or not _looks_like_task_id(task_id, profile):
        raise ValueError("Phase2 review-apply receipt contains an invalid task id")
    if receipt.get("success") is not True:
        raise ValueError(f"{task_id}: Phase2 review-apply receipt is not successful")
    review = receipt.get("review")
    if not isinstance(review, Mapping):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt lacks review metadata")
    if (
        str(review.get("verdict", "") or "").lower() != "pass"
        or str(review.get("phase2_status", "") or "").lower() != "pass"
    ):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt is not a clean pass")
    prompt_version = _int_or_none(review.get("prompt_version"))
    rubric_version = _int_or_none(review.get("rubric_version"))
    if (
        prompt_version not in supported_prompt_versions(profile)
        or rubric_version != supported_rubric_version(profile)
    ):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt uses obsolete review versions")
    applied_at = str(receipt.get("applied_at", "") or _file_time(path))
    review_subject = _phase2_receipt_subject(
        receipt.get("review_subject"),
        task_id=task_id,
        label="review_subject",
        created_at=applied_at,
        profile=profile,
    )
    projected_subject = _phase2_receipt_subject(
        receipt.get("projected_subject"),
        task_id=task_id,
        label="projected_subject",
        created_at=applied_at,
        profile=profile,
    )
    if not _phase2_receipt_bundles_equivalent(review_subject, projected_subject):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt changed reviewed content")
    transformation = receipt.get("transformation")
    if (
        not isinstance(transformation, Mapping)
        or transformation.get("kind") != "review_apply_output_relocation"
        or transformation.get("mechanical_status") != "pass"
        or transformation.get("build_status") not in {"pass", "not_required"}
    ):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt transformation is invalid")
    expected_role = f"{profile}_reviewed" if profile != "mat" else "toy_reviewed"
    if str(receipt.get("reviewed_head_role", "") or "") != expected_role:
        raise ValueError(f"{task_id}: Phase2 review-apply receipt reviewed role mismatch")

    result_path = _phase2_receipt_artifact(
        path,
        receipt.get("review_result_file"),
        label="review result",
    )
    result_hash = sha256_file(result_path)
    if result_hash != str(receipt.get("review_result_hash", "") or ""):
        raise ValueError(f"{task_id}: Phase2 review result hash mismatch")
    result = _read_json(result_path)
    if not isinstance(result, Mapping):
        raise ValueError(f"{task_id}: Phase2 review result is not an object")
    if canonicalize_block_id(str(result.get("task_id", "") or ""), profile) != task_id:
        raise ValueError(f"{task_id}: Phase2 review result task mismatch")
    if (
        str(result.get("verdict", "") or "").lower() != "pass"
        or str(result.get("phase2_status", "") or "").lower() not in {"", "pass"}
        or str(result.get("candidate_hash", "") or "") != review_subject.primary_hash
    ):
        raise ValueError(f"{task_id}: Phase2 review result does not match the receipt")
    input_path = _phase2_receipt_artifact(
        path,
        receipt.get("review_input_file"),
        label="review input",
    )
    input_payload = _read_json(input_path)
    input_hash = sha256_json(input_payload)
    if (
        input_hash != str(receipt.get("review_input_hash", "") or "")
        or input_hash != str(result.get("review_input_hash", "") or "")
    ):
        raise ValueError(f"{task_id}: Phase2 review input hash mismatch")

    identity = {
        key: receipt.get(key)
        for key in (
            "schema_version",
            "profile",
            "task_id",
            "attempt",
            "review_id",
            "transformation_id",
            "review_result_file",
            "review_result_hash",
            "review_input_hash",
            "review_subject_id",
            "projected_subject_id",
            "disposition",
        )
    }
    if sha256_json(identity) != str(receipt.get("receipt_id", "") or ""):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt identity mismatch")
    if (
        receipt.get("review_subject_id") != review_subject.subject_id
        or receipt.get("projected_subject_id") != projected_subject.subject_id
    ):
        raise ValueError(f"{task_id}: Phase2 review-apply receipt subject identity mismatch")

    store.upsert_subject(review_subject)
    store.upsert_subject(projected_subject)
    reviewer_independence = review.get("reviewer_independence", "")
    if isinstance(reviewer_independence, Mapping):
        reviewer_independence = json.dumps(
            reviewer_independence,
            ensure_ascii=False,
            sort_keys=True,
        )
    review_id = store.record_review(
        task_id=task_id,
        subject_id=review_subject.subject_id,
        verdict="pass",
        proof_class=str(review.get("proof_class", "") or ""),
        completion_class=str(review.get("completion_class", "") or ""),
        phase2_status="pass",
        evidence_path=result_path,
        evidence_hash=result_hash,
        reviewer_independence=str(reviewer_independence),
        authority_scope="phase2_review_apply",
        authority_eligible=True,
        reviewed_at=applied_at,
        prompt_version=prompt_version,
        rubric_version=rubric_version,
        review_input_path=input_path,
        review_input_hash=input_hash,
        reviewer_backend_id=str(review.get("reviewer_backend_id", "") or ""),
        provenance={
            "projection": "immutable_phase2_review_apply_receipt",
            "receipt": str(path.resolve()),
        },
    )
    if review_id != str(receipt.get("review_id", "") or ""):
        raise ValueError(f"{task_id}: Phase2 review id mismatch")
    transformation_id = store.record_transformation(
        task_id=task_id,
        source_subject_id=review_subject.subject_id,
        target_subject_id=projected_subject.subject_id,
        transformation_kind="review_apply_output_relocation",
        mechanical_status="pass",
        build_status=str(transformation.get("build_status")),
        evidence_path=result_path,
        evidence_hash=result_hash,
        created_at=applied_at,
    )
    if transformation_id != str(receipt.get("transformation_id", "") or ""):
        raise ValueError(f"{task_id}: Phase2 transformation id mismatch")
    store.set_task_head(
        task_id=task_id,
        role="reviewed_subject",
        subject_id=review_subject.subject_id,
        observed_at=applied_at,
        detail={"receipt": str(path.resolve()), "review_id": review_id},
    )
    store.set_task_head(
        task_id=task_id,
        role=expected_role,
        subject_id=projected_subject.subject_id,
        observed_at=applied_at,
        detail={"receipt": str(path.resolve()), "review_id": review_id},
    )
    receipt_hash = sha256_file(path)
    store.record_event(
        event_type="phase2_review_apply_receipt_imported",
        task_id=task_id,
        subject_id=projected_subject.subject_id,
        evidence_path=path,
        evidence_hash=receipt_hash,
        occurred_at=applied_at,
        payload={
            "receipt_id": receipt.get("receipt_id", ""),
            "review_id": review_id,
            "transformation_id": transformation_id,
            "profile": profile,
        },
    )
    store.mark_imported(
        source_path=path,
        source_kind="phase2_review_apply_receipt",
        record_count=1,
        source_hash=receipt_hash,
    )
    report.phase2_review_apply_receipts += 1
    report.reviews += 1


def import_process_event_file(
    store: WorkspaceStateStore,
    path: Path,
    report: MigrationReport,
    *,
    payload: Any | None = None,
    evidence_hash: str = "",
    fallback_occurred_at: str = "",
    profile: str = "mat",
) -> None:
    resolved_hash = evidence_hash or sha256_file(path)
    if store.import_is_current(path, source_hash=resolved_hash):
        report.skipped += 1
        return
    payload = _read_json(path) if payload is None else payload
    if not isinstance(payload, Mapping):
        raise ValueError("process event artifact is not an object")
    lowered = path.name.lower()
    if lowered.startswith("build_result"):
        event_type = "build_finished"
    elif lowered.startswith("verify_result"):
        event_type = "verification_finished"
    elif lowered.startswith("math_review_result"):
        event_type = "math_review_finished"
    elif lowered.startswith("basis_rebind"):
        event_type = "review_basis_rebound"
    elif "review_apply_receipt" in lowered:
        event_type = "review_apply_receipt_observed"
    else:
        event_type = "process_artifact_observed"
    task_id = _task_id(payload, fallback=path.parent.name, profile=profile)
    occurred_at = next(
        (
            str(payload.get(key, "") or "")
            for key in ("completed_at", "applied_at", "created_at", "generated_at", "started_at")
            if str(payload.get(key, "") or "")
        ),
        fallback_occurred_at or _file_time(path),
    )
    subject_id = str(payload.get("subject_id", "") or "")
    # Event history may predate reconstructible subjects.  Preserve the
    # reference in payload without violating the subject foreign key.
    bound_subject_id = ""
    if subject_id:
        try:
            with store._connection(write=False) as connection:
                present = connection.execute(
                    "SELECT 1 FROM subjects WHERE subject_id = ?", (subject_id,)
                ).fetchone()
            if present is not None:
                bound_subject_id = subject_id
        except Exception:
            bound_subject_id = ""
    summary = {
        "schema": payload.get("schema", payload.get("schema_version", "")),
        "status": payload.get("status", ""),
        "success": payload.get("success"),
        "verdict": payload.get("verdict", ""),
        "phase2_status": payload.get("phase2_status", ""),
        "attempt": payload.get("attempt", ""),
        "command": payload.get("command", ""),
        "exit_code": payload.get("exit_code"),
        "candidate_hash": payload.get("candidate_hash", payload.get("primary_hash", "")),
        "bundle_hash": payload.get("bundle_hash", ""),
        "referenced_subject_id": subject_id,
    }
    store.record_event(
        event_type=event_type,
        task_id=task_id,
        subject_id=bound_subject_id,
        evidence_path=path,
        evidence_hash=resolved_hash,
        occurred_at=occurred_at,
        payload=summary,
    )
    store.mark_imported(
        source_path=path,
        source_kind=event_type,
        record_count=1,
        source_hash=resolved_hash,
    )
    report.process_events += 1


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
    roots = [
        workspace_root / "toy-apollo-artifacts",
        runtime_root,
        workspace_root / "toy-apollo-archive-20260508",
        workspace_root / "phase2_prompt_packs",
        workspace_root / "research materials",
        workspace_root / "_archive",
        workspace_root / "_migration",
    ]
    selected: list[Path] = []
    seen: set[Path] = set()
    for path in roots:
        resolved = path.resolve()
        if resolved.exists() and resolved not in seen:
            selected.append(resolved)
            seen.add(resolved)
    return selected


def _required_rebuild_invariants(
    *,
    profile: str,
    catalog_valid: bool,
    catalog_counts: Mapping[str, int],
    current_head_count: int,
    compatible_pass_count: int,
    exact_current_count: int,
) -> dict[str, bool]:
    catalog_task_count = int(catalog_counts.get("tasks", 0))
    if profile != "mat":
        return {
            "catalog_valid": catalog_valid,
            "catalog_nonempty": catalog_task_count > 0,
            "all_catalog_modern_compatible_pass": compatible_pass_count == catalog_task_count,
            "all_catalog_exact_current_bundle_coverage": exact_current_count == catalog_task_count,
        }
    return {
        "catalog_valid": catalog_valid,
        "catalog_task_count_452": catalog_task_count == 452,
        "catalog_family_count_445": catalog_counts.get("families") == 445,
        "catalog_module_count_584": catalog_counts.get("modules") == 584,
        "mat_main_bundle_count_452": current_head_count == 452,
        "all_catalog_modern_compatible_pass": compatible_pass_count == catalog_task_count,
    }


def rebuild_invariants(store: WorkspaceStateStore, catalog: TaskCatalog) -> dict[str, Any]:
    catalog_check = validate_catalog(catalog)
    # Per-profile supported review versions: MAT keeps prompt 9/10/11 + rubric 9;
    # Cordis (catalog carries task_module_paths) uses prompt 1 + rubric 1.
    catalog_profile = profile_for_catalog(catalog)
    current_head_role = "mat_main" if catalog_profile == "mat" else f"{catalog_profile}_reviewed"
    prompt_pred = prompt_version_sql_predicate(catalog_profile)
    rubric_pred = rubric_version_sql_predicate(catalog_profile)
    cohort_id = next(iter(catalog.cohorts))
    with store._connection(write=False) as connection:
        current_head_count = int(
            connection.execute(
                """
                SELECT COUNT(*) FROM task_heads h
                JOIN catalog_tasks c ON c.task_id = h.task_id
                WHERE c.catalog_id = ? AND h.role = ? AND h.freshness IN ('fresh', 'local')
                """,
                (catalog.catalog_id, current_head_role),
            ).fetchone()[0]
        )
        compatible_rows = connection.execute(
            f"""
            SELECT r.task_id, MAX(m.prompt_version) AS prompt_version
            FROM reviews r
            JOIN review_metadata m ON m.review_id = r.review_id
            JOIN catalog_tasks c ON c.task_id = r.task_id AND c.catalog_id = ?
            WHERE lower(r.verdict) = 'pass'
              AND lower(COALESCE(r.phase2_status, '')) IN ('', 'pass')
              AND {rubric_pred}
              AND {prompt_pred}
            GROUP BY r.task_id
            """,
            (catalog.catalog_id,),
        ).fetchall()
        compatible_by_task = {str(row["task_id"]): int(row["prompt_version"]) for row in compatible_rows}
        cohort_members = set(catalog.task_ids(cohort_id=cohort_id))
        compatible_cohort = cohort_members & set(compatible_by_task)
        distribution = {
            prompt: sum(value == prompt for value in compatible_by_task.values())
            for prompt in supported_prompt_versions(catalog_profile)
        }
        exact_current_count = int(
            connection.execute(
                f"""
                SELECT COUNT(DISTINCT h.task_id)
                FROM task_heads h
                JOIN subjects current ON current.subject_id = h.subject_id
                JOIN catalog_tasks c ON c.task_id = h.task_id AND c.catalog_id = ?
                WHERE h.role = ? AND h.freshness IN ('fresh', 'local')
                  AND (
                    EXISTS (
                        SELECT 1
                        FROM reviews r
                        JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
                        JOIN review_metadata m ON m.review_id = r.review_id
                        WHERE r.task_id = h.task_id
                          AND reviewed.bundle_hash = current.bundle_hash
                          AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                          AND r.authority_eligible = 1
                          AND {prompt_pred}
                          AND {rubric_pred}
                    )
                    OR EXISTS (
                        SELECT 1
                        FROM transformations t
                        JOIN reviews r ON r.subject_id = t.source_subject_id
                        JOIN review_metadata m ON m.review_id = r.review_id
                        JOIN subjects transformed ON transformed.subject_id = t.target_subject_id
                        WHERE transformed.task_id = h.task_id
                          AND transformed.bundle_hash = current.bundle_hash
                          AND t.mechanical_status = 'pass'
                          AND t.build_status IN ('pass', 'not_required')
                          AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                          AND r.authority_eligible = 1
                          AND {prompt_pred}
                          AND {rubric_pred}
                    )
                    OR EXISTS (
                        SELECT 1
                        FROM valid_authority_bindings b
                        JOIN transformations t
                          ON t.transformation_id = b.transformation_id
                        JOIN subjects bridged
                          ON bridged.subject_id = b.target_subject_id
                        WHERE b.target_subject_id = current.subject_id
                          AND bridged.task_id = h.task_id
                          AND bridged.bundle_hash = current.bundle_hash
                          AND t.transformation_kind = 'verified_evidence_bridge'
                          AND t.mechanical_status = 'pass'
                          AND t.build_status = 'pass'
                    )
                  )
                """,
                (catalog.catalog_id, current_head_role),
            ).fetchone()[0]
        )
        authority_pass_tasks = int(
            connection.execute(
                """
                SELECT COUNT(DISTINCT r.task_id)
                FROM reviews r
                JOIN catalog_tasks c ON c.task_id = r.task_id AND c.catalog_id = ?
                WHERE r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                """,
                (catalog.catalog_id,),
            ).fetchone()[0]
        )
        exact_bridge_count = int(
            connection.execute(
                """
                SELECT COUNT(DISTINCT h.task_id)
                FROM task_heads h
                JOIN subjects current ON current.subject_id = h.subject_id
                JOIN catalog_tasks c ON c.task_id = h.task_id AND c.catalog_id = ?
                JOIN valid_authority_bindings b ON b.target_subject_id = current.subject_id
                JOIN transformations t ON t.transformation_id = b.transformation_id
                WHERE h.role = ? AND h.freshness IN ('fresh', 'local')
                  AND t.transformation_kind = 'verified_evidence_bridge'
                  AND t.mechanical_status = 'pass' AND t.build_status = 'pass'
                """,
                (catalog.catalog_id, current_head_role),
            ).fetchone()[0]
        )
    catalog_task_ids = set(catalog.task_ids())
    compatible_task_ids = set(compatible_by_task)
    catalog_counts = catalog.counts()
    required = _required_rebuild_invariants(
        profile=catalog_profile,
        catalog_valid=bool(catalog_check.get("valid")),
        catalog_counts=catalog_counts,
        current_head_count=current_head_count,
        compatible_pass_count=len(compatible_task_ids),
        exact_current_count=exact_current_count,
    )
    bridge_integrity = store.validate_authority_bindings()
    required["typed_authority_bindings_well_formed"] = bool(bridge_integrity["valid"])
    result = {
        "profile": catalog_profile,
        "required": required,
        "all_required_pass": all(required.values()),
        "catalog": catalog_check,
        "current_catalog_head_role": current_head_role,
        "current_catalog_head_count": current_head_count,
        "compatible_pass": {
            "all_catalog_found": len(compatible_task_ids),
            "all_catalog_expected": len(catalog_task_ids),
            "all_catalog_missing": sorted(catalog_task_ids - compatible_task_ids),
            "highest_prompt_distribution_all_catalog_tasks": distribution,
        },
        "historical_metrics": {
            "legacy_review_root_compatible_pass": {
                "cohort_id": cohort_id,
                "found": len(compatible_cohort),
                "expected": len(cohort_members),
                "missing": sorted(cohort_members - compatible_cohort),
                "applicable": catalog_profile == "mat",
                "reproducibility_target_met": (
                    len(compatible_cohort) == len(cohort_members) == 344
                    if catalog_profile == "mat"
                    else None
                ),
            }
        },
        "authority_eligible_pass_tasks": authority_pass_tasks,
        "typed_authority_bindings": bridge_integrity,
        "exact_current_catalog_typed_authority_coverage": exact_bridge_count,
        "exact_current_catalog_bundle_coverage": exact_current_count,
    }
    if catalog_profile == "mat":
        # Stable MAT compatibility aliases; non-MAT profiles stay terminology-neutral.
        result["mat_main_bundle_count"] = current_head_count
        result["exact_current_mat_typed_authority_coverage"] = exact_bridge_count
        result["exact_current_mat_bundle_coverage"] = exact_current_count
    return result


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
    catalog: TaskCatalog | None = None,
    replace_target: bool = True,
    progress: Callable[[str, Mapping[str, Any]], None] | None = None,
) -> MigrationReport:
    target = WorkspaceStateStore(state_path)
    temp_store = WorkspaceStateStore.temporary_rebuild_store(target.path)
    report = MigrationReport(database=str(target.path))
    scan_roots = list(roots or default_migration_roots(workspace_root=workspace_root, runtime_root=runtime_root))
    policy_path = runtime_root / "data" / "task_catalog" / "catalog_policy_v1.json"
    if catalog is None and policy_path.is_file():
        catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    review_profile = profile_for_catalog(catalog) if catalog is not None else "mat"
    try:
        _emit_progress(progress, "inventory_started", roots=len(scan_roots))
        inventory = discover_evidence_inventory(scan_roots)
        ledger_paths = list(inventory.ledgers)
        applied_receipts = _applied_review_receipts(
            ledger_paths,
            profile=review_profile,
        )
        receipt_paths = [
            Path(receipt["result_file"]).resolve()
            for task_receipts in applied_receipts.values()
            for receipt in task_receipts
            if receipt.get("result_file") and Path(receipt["result_file"]).is_file()
        ]
        receipt_path_set = set(receipt_paths)
        review_paths = sorted(
            set(inventory.reviews) | receipt_path_set,
            key=lambda item: (0 if item in receipt_path_set else 1, str(item).lower()),
        )
        process_paths = list(inventory.process_events)
        _emit_progress(
            progress,
            "inventory_finished",
            ledgers=len(ledger_paths),
            reviews=len(review_paths),
            bindings=len(inventory.workspace_review_bindings),
            mat_receipts=len(inventory.mat_review_receipts),
            phase2_review_apply_receipts=len(
                inventory.phase2_review_apply_receipts
            ),
            historical_apply_recovery_receipts=len(
                inventory.historical_apply_recovery_receipts
            ),
            transformation_receipts=len(inventory.validated_transformation_receipts),
            boundary_delta_receipts=len(inventory.boundary_delta_receipts),
            evidence_bridge_receipts=len(inventory.evidence_bridge_receipts),
            evidence_bridge_batch_receipts=len(inventory.evidence_bridge_batch_receipts),
            process_events=len(process_paths),
        )
        evidence_hashes, hash_errors = _hash_paths([*review_paths, *process_paths])
        report.warnings.extend(hash_errors)
        unique_reviews, duplicate_reviews = _deduplicate_paths(review_paths, evidence_hashes)
        unique_process, duplicate_process = _deduplicate_paths(process_paths, evidence_hashes)
        _emit_progress(
            progress,
            "evidence_hashed",
            review_unique=len(unique_reviews),
            review_duplicates=len(duplicate_reviews),
            process_unique=len(unique_process),
            process_duplicates=len(duplicate_process),
            hash_errors=len(hash_errors),
        )
        with temp_store.bulk_write():
            if catalog is not None:
                temp_store.persist_catalog(catalog)
                report.catalog_id = catalog.catalog_id
                report.catalog_counts = catalog.counts()
            for root in scan_roots:
                temp_store.register_evidence_root(
                    root_path=root,
                    root_kind="workspace_history" if root != runtime_root else "active_runtime",
                    detail={"rebuild_scan_root": True},
                )
                report.evidence_roots += 1
            for path in ledger_paths:
                try:
                    import_legacy_ledger(
                        temp_store,
                        path,
                        report,
                        profile=review_profile,
                    )
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
            # Exact apply receipts establish the canonical review identity.
            # Import them before generic result aliases so the UNIQUE
            # (evidence_hash, subject_id) row cannot be claimed first by a
            # weaker historical scope.
            for path in inventory.external_pr_receipts:
                try:
                    import_external_pr_review_receipt(temp_store, path, report)
                except Exception as exc:
                    report.warnings.append(f"external PR review receipt {path}: {exc}")
            _emit_progress(
                progress,
                "external_receipts_imported",
                external_pr_receipts=report.external_pr_receipts,
            )
            for path in inventory.historical_apply_recovery_receipts:
                try:
                    import_historical_review_apply_recovery_receipt(temp_store, path, report)
                except Exception as exc:
                    try:
                        payload = _read_json(path)
                    except Exception:
                        payload = {}
                    task_id = _task_id(payload, fallback=path.parent.name) if isinstance(payload, Mapping) else ""
                    evidence_hash = sha256_file(path)
                    temp_store.record_event(
                        event_type="historical_review_apply_recovery_receipt_rejected",
                        task_id=task_id,
                        evidence_path=path,
                        evidence_hash=evidence_hash,
                        occurred_at=_file_time(path),
                        payload={"validation_error": str(exc)},
                    )
                    temp_store.mark_imported(
                        source_path=path,
                        source_kind="rejected_historical_review_apply_recovery_receipt",
                        record_count=1,
                        source_hash=evidence_hash,
                    )
                    report.rejected_historical_apply_recovery_receipts += 1
                    report.warnings.append(
                        f"historical review-apply recovery receipt {path}: {exc}"
                    )
            _emit_progress(
                progress,
                "historical_apply_recovery_receipts_imported",
                validated=report.historical_apply_recovery_receipts,
                rejected=report.rejected_historical_apply_recovery_receipts,
            )
            for path in inventory.mat_review_receipts:
                try:
                    import_mat_review_apply_receipt(temp_store, path, report)
                except Exception as exc:
                    payload = _read_json(path)
                    task_id = _task_id(payload, fallback=path.parent.name)
                    evidence_hash = evidence_hashes.get(path, "") or sha256_file(path)
                    occurred_at = next(
                        (
                            str(payload.get(key, "") or "")
                            for key in ("applied_at", "created_at", "completed_at")
                            if isinstance(payload, Mapping) and str(payload.get(key, "") or "")
                        ),
                        _file_time(path),
                    )
                    temp_store.record_event(
                        event_type="review_apply_receipt_rejected",
                        task_id=task_id,
                        evidence_path=path,
                        evidence_hash=evidence_hash,
                        occurred_at=occurred_at,
                        payload={"validation_error": str(exc)},
                    )
                    temp_store.mark_imported(
                        source_path=path,
                        source_kind="rejected_mat_review_apply_receipt",
                        record_count=1,
                        source_hash=evidence_hash,
                    )
                    report.rejected_mat_review_receipts += 1
            _emit_progress(
                progress,
                "mat_receipts_imported",
                mat_review_receipts=report.mat_review_receipts,
                rejected_mat_review_receipts=report.rejected_mat_review_receipts,
            )
            for path in inventory.phase2_review_apply_receipts:
                try:
                    import_phase2_review_apply_receipt(
                        temp_store,
                        path,
                        report,
                        profile=review_profile,
                    )
                except Exception as exc:
                    report.rejected_phase2_review_apply_receipts += 1
                    report.warnings.append(
                        f"phase2 review-apply receipt {path}: {exc}"
                    )
            _emit_progress(
                progress,
                "phase2_review_apply_receipts_imported",
                validated=report.phase2_review_apply_receipts,
                rejected=report.rejected_phase2_review_apply_receipts,
            )
            temp_store.mark_imported_many(
                (
                    path,
                    evidence_hash,
                    f"duplicate_semantic_review_copy:{canonical_copy.name}",
                    0,
                )
                for path, canonical_copy, evidence_hash in duplicate_reviews
            )
            report.duplicate_evidence_copies += len(duplicate_reviews)
            for batch in _json_batches(unique_reviews):
                for path, payload, file_timestamp, error in batch:
                    if error:
                        import_rejected_review_artifact(
                            temp_store,
                            path=path,
                            evidence_hash=evidence_hashes[path],
                            error=error,
                            report=report,
                            occurred_at=file_timestamp,
                            profile=review_profile,
                        )
                        continue
                    try:
                        import_review_file(
                            temp_store,
                            path,
                            report,
                            applied_receipts=applied_receipts,
                            payload=payload,
                            evidence_hash=evidence_hashes[path],
                            profile=review_profile,
                        )
                    except Exception as exc:
                        import_rejected_review_artifact(
                            temp_store,
                            path=path,
                            evidence_hash=evidence_hashes[path],
                            error=str(exc),
                            report=report,
                            payload=payload,
                            occurred_at=file_timestamp,
                            profile=review_profile,
                        )
            _emit_progress(
                progress,
                "reviews_imported",
                review_rows=report.reviews,
                rejected_reviews=report.rejected_reviews,
                duplicate_copies=report.duplicate_evidence_copies,
            )
            for path in inventory.workspace_review_bindings:
                try:
                    import_workspace_review_binding(
                        temp_store,
                        path,
                        report,
                        profile=review_profile,
                    )
                except Exception as exc:
                    report.warnings.append(f"review binding {path}: {exc}")
            _emit_progress(
                progress,
                "review_bindings_imported",
                review_bindings=report.review_bindings,
            )
            for path in inventory.sidecars:
                try:
                    import_sidecar_state(
                        temp_store,
                        path,
                        report,
                        profile=review_profile,
                    )
                except Exception as exc:
                    report.warnings.append(f"sidecar {path}: {exc}")
            _emit_progress(progress, "sidecars_imported", sidecar_rows=report.sidecar_rows)
            temp_store.mark_imported_many(
                (
                    path,
                    evidence_hash,
                    f"duplicate_process_artifact:{canonical_copy.name}",
                    0,
                )
                for path, canonical_copy, evidence_hash in duplicate_process
            )
            report.duplicate_evidence_copies += len(duplicate_process)
            processed_paths = 0
            for batch in _json_batches(unique_process):
                for path, payload, file_timestamp, error in batch:
                    processed_paths += 1
                    if error:
                        report.warnings.append(f"process event {path}: {error}")
                        continue
                    try:
                        import_process_event_file(
                            temp_store,
                            path,
                            report,
                            payload=payload,
                            evidence_hash=evidence_hashes[path],
                            fallback_occurred_at=file_timestamp,
                            profile=review_profile,
                        )
                    except Exception as exc:
                        report.warnings.append(f"process event {path}: {exc}")
                if processed_paths % 1024 == 0 or processed_paths == len(unique_process):
                    _emit_progress(
                        progress,
                        "process_history_batch",
                        processed=processed_paths,
                        total=len(unique_process),
                    )
            _emit_progress(
                progress,
                "process_history_imported",
                process_events=report.process_events,
                duplicate_copies=report.duplicate_evidence_copies,
                warnings=len(report.warnings),
            )
            reconciliation = refresh_workspace_state(
                temp_store,
                workspace_root=workspace_root,
                runtime_root=runtime_root,
                chapters=tuple(range(1, 15)) if catalog is not None else (1, 2, 3, 4),
                refresh_remote=refresh_remote,
                catalog=catalog,
            )
            _emit_progress(progress, "repository_state_refreshed", **(reconciliation.get("local") or {}))
            # This recovery must run after current MAT heads are refreshed: its
            # only authority is a receipt proving the stale result's content is
            # identical to the now-pinned main subject and the invalidator plus
            # direct consumers were rebuilt on that same commit.
            for path in inventory.resolved_invalidation_recovery_receipts:
                try:
                    import_resolved_invalidation_recovery_receipt(
                        temp_store,
                        path,
                        report,
                        target_repo=workspace_root / "MAT3280-formalization-output",
                    )
                except Exception as exc:
                    try:
                        payload = _read_json(path)
                    except Exception:
                        payload = {}
                    task_id = _task_id(payload, fallback=path.parent.name) if isinstance(payload, Mapping) else ""
                    evidence_hash = sha256_file(path)
                    temp_store.record_event(
                        event_type="resolved_invalidation_recovery_receipt_rejected",
                        task_id=task_id,
                        evidence_path=path,
                        evidence_hash=evidence_hash,
                        occurred_at=_file_time(path),
                        payload={"validation_error": str(exc)},
                    )
                    temp_store.mark_imported(
                        source_path=path,
                        source_kind="rejected_resolved_invalidation_recovery_receipt",
                        record_count=1,
                        source_hash=evidence_hash,
                    )
                    report.rejected_resolved_invalidation_recovery_receipts += 1
                    report.warnings.append(f"resolved-invalidation recovery receipt {path}: {exc}")
            _emit_progress(
                progress,
                "resolved_invalidation_recovery_receipts_imported",
                validated=report.resolved_invalidation_recovery_receipts,
                rejected=report.rejected_resolved_invalidation_recovery_receipts,
            )
            for path in inventory.validated_transformation_receipts:
                try:
                    import_validated_transformation_receipt(
                        temp_store,
                        path,
                        report,
                        target_repo=workspace_root / "MAT3280-formalization-output",
                    )
                except Exception as exc:
                    try:
                        payload = _read_json(path)
                    except Exception:
                        payload = {}
                    task_id = _task_id(payload, fallback=path.parent.name) if isinstance(payload, Mapping) else ""
                    evidence_hash = sha256_file(path)
                    temp_store.record_event(
                        event_type="validated_transformation_receipt_rejected",
                        task_id=task_id,
                        evidence_path=path,
                        evidence_hash=evidence_hash,
                        occurred_at=_file_time(path),
                        payload={"validation_error": str(exc)},
                    )
                    temp_store.mark_imported(
                        source_path=path,
                        source_kind="rejected_validated_transformation_receipt",
                        record_count=1,
                        source_hash=evidence_hash,
                    )
                    report.rejected_transformation_receipts += 1
                    report.warnings.append(f"validated transformation receipt {path}: {exc}")
            _emit_progress(
                progress,
                "transformation_receipts_imported",
                validated=report.validated_transformation_receipts,
                rejected=report.rejected_transformation_receipts,
            )
            # Boundary-delta receipts depend on both the source recovery/scope
            # reviews above and the refreshed active MAT head.  Keep this last
            # so one clean rebuild establishes the whole chain exactly once.
            kenneth_repo = workspace_root / "_external_refs" / "kenneth_probabilitytheory_readonly"
            for path in inventory.boundary_delta_receipts:
                try:
                    import_verified_boundary_delta_receipt(
                        temp_store,
                        path,
                        report,
                        source_repos=(runtime_root, workspace_root / "MAT3280-formalization-output"),
                        target_repo=workspace_root / "MAT3280-formalization-output",
                        kenneth_repo=kenneth_repo,
                    )
                except Exception as exc:
                    try:
                        payload = _read_json(path)
                    except Exception:
                        payload = {}
                    task_id = _task_id(payload, fallback=path.parent.name) if isinstance(payload, Mapping) else ""
                    evidence_hash = sha256_file(path)
                    temp_store.record_event(
                        event_type="verified_boundary_delta_receipt_rejected",
                        task_id=task_id,
                        evidence_path=path,
                        evidence_hash=evidence_hash,
                        occurred_at=_file_time(path),
                        payload={"validation_error": str(exc)},
                    )
                    temp_store.mark_imported(
                        source_path=path,
                        source_kind="rejected_verified_boundary_delta_receipt",
                        record_count=1,
                        source_hash=evidence_hash,
                    )
                    report.rejected_boundary_delta_receipts += 1
                    report.warnings.append(f"verified boundary-delta receipt {path}: {exc}")
            _emit_progress(
                progress,
                "boundary_delta_receipts_imported",
                validated=report.boundary_delta_receipts,
                rejected=report.rejected_boundary_delta_receipts,
            )
            # Evidence bridges are the final authority projection: source
            # reviews/sync decisions and current MAT heads must already exist.
            # Rejections intentionally create no event/import row so an
            # unrepresentable C item has zero state writes.
            for path in inventory.evidence_bridge_receipts:
                try:
                    import_validated_evidence_bridge_receipt(
                        temp_store,
                        path,
                        report,
                        source_repos=(
                            runtime_root,
                            workspace_root / "MAT3280-formalization-output",
                            kenneth_repo,
                        ),
                        target_repo=workspace_root / "MAT3280-formalization-output",
                        kenneth_repo=kenneth_repo,
                    )
                except Exception as exc:
                    report.rejected_evidence_bridge_receipts += 1
                    report.warnings.append(f"validated evidence bridge receipt {path}: {exc}")
            for path in inventory.evidence_bridge_batch_receipts:
                try:
                    import_validated_evidence_bridge_batch_receipt(
                        temp_store,
                        path,
                        report,
                        target_repo=workspace_root / "MAT3280-formalization-output",
                        kenneth_repo=kenneth_repo,
                    )
                except Exception as exc:
                    report.rejected_evidence_bridge_batch_receipts += 1
                    report.warnings.append(f"validated evidence bridge batch receipt {path}: {exc}")
            _emit_progress(
                progress,
                "evidence_bridge_receipts_imported",
                validated=report.evidence_bridge_receipts,
                rejected=report.rejected_evidence_bridge_receipts,
                validated_batches=report.evidence_bridge_batch_receipts,
                rejected_batches=report.rejected_evidence_bridge_batch_receipts,
            )
        local = reconciliation.get("local") or {}
        report.local_subjects = sum(
            int(value or 0)
            for key, value in local.items()
            if key != "errors" and not isinstance(value, (list, dict))
        )
        report.warnings.extend(str(error) for error in local.get("errors", []))
        remote = reconciliation.get("remote") or {}
        report.remote_subjects = int(remote.get("subjects", 0) or 0)
        report.warnings.extend(str(error) for error in remote.get("errors", []))
        summary = temp_store.summary()
        if not any(summary[key] for key in ("campaign_ledgers", "subjects", "reviews", "runs", "integrations", "task_heads")):
            raise RuntimeError("State rebuild found no ledger, review evidence, repository subjects, or task heads.")
        if catalog is not None:
            report.invariants = rebuild_invariants(temp_store, catalog)
            _emit_progress(
                progress,
                "invariants_checked",
                required=report.invariants.get("required", {}),
                compatible_pass=report.invariants.get("compatible_pass", {}),
                authority_eligible_pass_tasks=report.invariants.get(
                    "authority_eligible_pass_tasks", 0
                ),
                exact_current_mat_bundle_coverage=report.invariants.get(
                    "exact_current_mat_bundle_coverage", 0
                ),
            )
            if not report.invariants.get("all_required_pass"):
                raise RuntimeError(
                    "State rebuild failed catalog/coverage invariants: "
                    + json.dumps(report.invariants.get("required", {}), sort_keys=True)
                )
        temp_store.assert_integrity()
        if replace_target:
            backup = target.replace_from(temp_store.path, backup_label="rebuild")
            report.backup = str(backup or "")
            report.rebuilt_database = str(target.path)
        else:
            report.rebuilt_database = str(temp_store.path)
        return report
    except Exception:
        temp_store.path.unlink(missing_ok=True)
        raise
