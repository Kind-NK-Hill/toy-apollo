from __future__ import annotations

import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from formalization_engine.block_id_naming import canonicalize_block_id

from .state_bundle_delta import compare_bundles
from .state_reconcile import discover_catalog_git_subjects, git_file_at_ref
from .state_store import SubjectBundle, WorkspaceStateStore, filesystem_path
from .task_catalog import TaskCatalog, load_catalog


RECEIPT_SCHEMA = "toy-apollo.validated-transformation-receipt.v1"
BUILD_SCHEMA = "toy-apollo.mechanical-build-evidence.v1"
FORBIDDEN_SCHEMA = "toy-apollo.forbidden-scan-evidence.v1"
FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*(?:private\s+)?axiom\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
}


class TransformationReceiptError(RuntimeError):
    """Raised when a mechanical receipt cannot be proved fail-closed."""


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _run(repo: Path, *argv: str, timeout: int = 120) -> subprocess.CompletedProcess[bytes]:
    try:
        completed = subprocess.run(
            list(argv),
            cwd=str(repo),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise TransformationReceiptError(f"Command failed to run in {repo}: {' '.join(argv)}: {exc}") from exc
    return completed


def _command_text(repo: Path, *argv: str) -> str:
    completed = _run(repo, *argv)
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise TransformationReceiptError(f"Command failed in {repo}: {' '.join(argv)}: {detail}")
    return completed.stdout.decode("utf-8", errors="replace").strip()


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


def _subject_from_row(row: Mapping[str, Any]) -> SubjectBundle:
    manifest = row.get("manifest_json", "[]")
    if isinstance(manifest, str):
        try:
            manifest = json.loads(manifest)
        except json.JSONDecodeError as exc:
            raise TransformationReceiptError("Source review subject manifest is malformed") from exc
    subject = SubjectBundle.from_manifest(
        task_id=str(row["task_id"]),
        files=manifest,
        primary_path=str(row["primary_path"]),
        source_repo=str(row["source_repo"]),
        source_commit=str(row["source_commit"]),
        layout=str(row["layout"]),
        subject_kind=str(row["subject_kind"]),
    )
    if subject.subject_id != str(row["subject_id"]):
        raise TransformationReceiptError("Source review subject identity does not reconstruct")
    return subject


def _eligible_sources(
    store: WorkspaceStateStore,
    *,
    task_id: str,
    review_id: str = "",
) -> list[dict[str, Any]]:
    predicate = " AND r.review_id = ?" if review_id else ""
    parameters: tuple[Any, ...] = (task_id, review_id) if review_id else (task_id,)
    with store._connection(write=False) as connection:
        rows = connection.execute(
            """
            SELECT r.review_id, r.task_id, r.subject_id, r.evidence_hash,
                   r.evidence_path, r.reviewed_at, r.verdict, r.phase2_status,
                   r.authority_eligible, m.prompt_version, m.rubric_version,
                   s.subject_kind, s.source_repo, s.source_commit, s.layout,
                   s.bundle_hash, s.primary_hash, s.primary_path, s.manifest_json
            FROM reviews r
            JOIN review_metadata m ON m.review_id = r.review_id
            JOIN subjects s ON s.subject_id = r.subject_id
            WHERE r.task_id = ?
              AND lower(r.verdict) = 'pass'
              AND lower(r.phase2_status) = 'pass'
              AND r.authority_eligible = 1
              AND m.prompt_version IN (9, 10, 11)
              AND m.rubric_version = 9
            """
            + predicate
            + " ORDER BY r.reviewed_at DESC, r.review_id DESC",
            parameters,
        ).fetchall()
    return [dict(row) for row in rows]


def _primary_module(catalog: TaskCatalog, task_id: str) -> str:
    matches = [
        item.module_name
        for item in catalog.modules
        if item.owner_task_id == task_id and item.module_role == "primary"
    ]
    if len(matches) != 1:
        raise TransformationReceiptError(
            f"{task_id}: catalog must provide exactly one primary MAT module, found {len(matches)}"
        )
    return matches[0]


def _inspect_validated_transformations(
    *,
    store: WorkspaceStateStore,
    workspace_root: Path,
    runtime_root: Path,
    task_ids: list[str],
    source_review_ids: Mapping[str, str] | None = None,
    checkout: Path | None = None,
    require_clean_checkout: bool = True,
) -> list[dict[str, Any]]:
    """Inspect many path-only candidates with one catalog and MAT inventory pass."""

    canonical_tasks = sorted({canonicalize_block_id(task_id) for task_id in task_ids})
    if not canonical_tasks or any(not task_id for task_id in canonical_tasks):
        raise TransformationReceiptError("At least one valid canonical task id is required")
    store.assert_integrity()
    catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    missing = sorted(set(canonical_tasks) - set(catalog.task_ids()))
    if missing:
        raise TransformationReceiptError(f"Tasks are absent from the active catalog: {missing}")
    mat_repo = workspace_root / "MAT3280-formalization-output"
    if not (mat_repo / ".git").exists():
        raise TransformationReceiptError(f"MAT repository is missing: {mat_repo}")
    origin_main = _command_text(mat_repo, "git", "rev-parse", "origin/main")
    if origin_main != catalog.mat_commit:
        raise TransformationReceiptError(
            f"MAT origin/main {origin_main} does not match catalog pin {catalog.mat_commit}"
        )
    build_checkout = (checkout or mat_repo).expanduser().resolve()
    if not (build_checkout / ".git").exists():
        raise TransformationReceiptError(f"Exact MAT build checkout is missing: {build_checkout}")
    head = _command_text(build_checkout, "git", "rev-parse", "HEAD")
    if head != catalog.mat_commit:
        raise TransformationReceiptError(
            f"MAT build checkout HEAD {head} does not match catalog-pinned origin/main {catalog.mat_commit}"
        )
    dirty = _command_text(
        build_checkout, "git", "status", "--porcelain", "--untracked-files=all"
    )
    if dirty and require_clean_checkout:
        raise TransformationReceiptError("MAT worktree is not clean; exact pinned build cannot be certified")
    targets = discover_catalog_git_subjects(
        mat_repo,
        ref=catalog.mat_commit,
        catalog=catalog,
        source_repo="mat",
        layout="mat",
        task_ids=canonical_tasks,
    )
    inspections: list[dict[str, Any]] = []
    for canonical_task in canonical_tasks:
        target = targets.get(canonical_task)
        if target is None:
            raise TransformationReceiptError(f"{canonical_task}: catalog-pinned MAT bundle is missing")
        source_review_id = str((source_review_ids or {}).get(canonical_task, "") or "")
        candidates: list[tuple[dict[str, Any], SubjectBundle, dict[str, Any]]] = []
        for row in _eligible_sources(store, task_id=canonical_task, review_id=source_review_id):
            try:
                source = _subject_from_row(row)
            except TransformationReceiptError:
                if source_review_id:
                    raise
                continue
            comparison = compare_bundles(
                {
                    "bundle_hash": source.bundle_hash,
                    "primary_hash": source.primary_hash,
                    "manifest_json": source.manifest(),
                },
                {
                    "bundle_hash": target.bundle_hash,
                    "primary_hash": target.primary_hash,
                    "manifest_json": target.manifest(),
                },
            ).as_dict()
            if comparison["classification"] == "path_only_relocation":
                candidates.append((row, source, comparison))
        if not candidates:
            suffix = f" for requested review {source_review_id}" if source_review_id else ""
            raise TransformationReceiptError(
                f"{canonical_task}: no eligible modern authority source is path-only relative to current MAT{suffix}"
            )
        row, source, comparison = candidates[0]
        inspections.append(
            {
                "schema": "toy-apollo.validated-transformation-inspection.v1",
                "status": "eligible",
                "task_id": canonical_task,
                "catalog_id": catalog.catalog_id,
                "catalog_mat_commit": catalog.mat_commit,
                "mat_origin_main": origin_main,
                "mat_head": head,
                "mat_repo": str(mat_repo.resolve()),
                "build_checkout": str(build_checkout),
                "build_checkout_dirty": bool(dirty),
                "source_review": {
                    "review_id": row["review_id"],
                    "evidence_hash": row["evidence_hash"],
                    "prompt_version": row["prompt_version"],
                    "rubric_version": row["rubric_version"],
                    "reviewed_at": row["reviewed_at"],
                },
                "source_subject": _subject_payload(source),
                "target_subject": _subject_payload(target),
                "comparison": comparison,
                "focused_build": {
                    "command": ["lake", "build", _primary_module(catalog, canonical_task)]
                },
                "forbidden_tokens": sorted(FORBIDDEN_PATTERNS),
            }
        )
    return inspections


def inspect_validated_transformation(
    *,
    store: WorkspaceStateStore,
    workspace_root: Path,
    runtime_root: Path,
    task_id: str,
    source_review_id: str = "",
    checkout: Path | None = None,
) -> dict[str, Any]:
    """Inspect one exact path-only candidate without changing repositories or SQLite."""

    return _inspect_validated_transformations(
        store=store,
        workspace_root=workspace_root,
        runtime_root=runtime_root,
        task_ids=[task_id],
        source_review_ids={canonicalize_block_id(task_id): source_review_id},
        checkout=checkout,
        require_clean_checkout=True,
    )[0]


def _forbidden_findings(mat_repo: Path, target: Mapping[str, Any]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    commit = str(target["source_commit"])
    for item in target["files"]:
        path = str(item["path"])
        text = git_file_at_ref(mat_repo, commit, path).decode("utf-8", errors="replace")
        for token, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                findings.append(
                    {
                        "path": path,
                        "token": token,
                        "line": text.count("\n", 0, match.start()) + 1,
                    }
                )
    return findings


def _revalidate_emit_heads(inspection: Mapping[str, Any]) -> None:
    mat_repo = Path(str(inspection["mat_repo"]))
    build_checkout = Path(str(inspection["build_checkout"]))
    expected = str(inspection["catalog_mat_commit"])
    if _command_text(mat_repo, "git", "rev-parse", "origin/main") != expected:
        raise TransformationReceiptError("MAT origin/main changed during transformation validation")
    if _command_text(build_checkout, "git", "rev-parse", "HEAD") != expected:
        raise TransformationReceiptError("MAT build checkout HEAD changed during transformation validation")
    if _command_text(
        build_checkout, "git", "status", "--porcelain", "--untracked-files=all"
    ):
        raise TransformationReceiptError("MAT build checkout became dirty during transformation validation")


def _json_bytes(payload: Mapping[str, Any]) -> bytes:
    return (json.dumps(dict(payload), ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _write_new(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("xb") as handle:
            handle.write(payload)
    except FileExistsError as exc:
        raise TransformationReceiptError(f"Refusing to overwrite immutable evidence: {path}") from exc


def _evidence_paths(output: Path, task_id: str) -> tuple[Path, Path, Path]:
    return (
        output / f"validated_transformation_build_{task_id}.json",
        output / f"validated_transformation_forbidden_scan_{task_id}.json",
        output / f"validated_transformation_receipt_{task_id}.json",
    )


def _validate_existing_evidence(
    inspection: Mapping[str, Any],
    paths: tuple[Path, Path, Path],
) -> dict[str, Any]:
    task_id = str(inspection["task_id"])
    if not all(path.is_file() for path in paths):
        raise TransformationReceiptError(
            f"{task_id}: immutable evidence is partial; refusing overwrite"
        )
    try:
        build = json.loads(filesystem_path(paths[0]).read_text(encoding="utf-8"))
        forbidden = json.loads(filesystem_path(paths[1]).read_text(encoding="utf-8"))
        receipt = json.loads(filesystem_path(paths[2]).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise TransformationReceiptError(f"{task_id}: existing evidence is unreadable: {exc}") from exc
    target = inspection["target_subject"]
    source = inspection["source_subject"]
    review = inspection["source_review"]
    module = str(inspection["focused_build"]["command"][-1])
    if (
        not isinstance(receipt, Mapping)
        or receipt.get("schema") != RECEIPT_SCHEMA
        or receipt.get("task_id") != task_id
        or receipt.get("catalog_id") != inspection["catalog_id"]
        or receipt.get("source_subject") != source
        or receipt.get("target_subject") != target
        or not isinstance(receipt.get("source_review"), Mapping)
        or receipt["source_review"].get("review_id") != review["review_id"]
        or receipt["source_review"].get("evidence_hash") != review["evidence_hash"]
    ):
        raise TransformationReceiptError(f"{task_id}: existing receipt does not bind current inspection")
    expected_identity = {
        "task_id": task_id,
        "subject_id": target["subject_id"],
        "bundle_hash": target["bundle_hash"],
        "primary_hash": target["primary_hash"],
        "commit": target["source_commit"],
    }
    for label, payload in (("build", build), ("forbidden scan", forbidden)):
        if not isinstance(payload, Mapping) or any(
            payload.get(key) != value for key, value in expected_identity.items()
        ):
            raise TransformationReceiptError(f"{task_id}: existing {label} identity mismatch")
        if payload.get("status") != "pass":
            raise TransformationReceiptError(f"{task_id}: existing {label} did not pass")
    command = build.get("command")
    if (
        build.get("success") is not True
        or build.get("exit_code") != 0
        or not isinstance(command, list)
        or command[:2] != ["lake", "build"]
        or module not in command[2:]
    ):
        raise TransformationReceiptError(f"{task_id}: existing build did not include its focused module")
    if forbidden.get("matches") != []:
        raise TransformationReceiptError(f"{task_id}: existing forbidden scan has findings")
    checks = receipt.get("checks")
    if not isinstance(checks, Mapping):
        raise TransformationReceiptError(f"{task_id}: existing receipt checks are missing")
    for key, path in (("build", paths[0]), ("forbidden_scan", paths[1])):
        raw = checks.get(key)
        artifact = raw.get("artifact") if isinstance(raw, Mapping) else None
        digest = _sha256_bytes(filesystem_path(path).read_bytes())
        if (
            not isinstance(artifact, Mapping)
            or artifact.get("path") != path.name
            or artifact.get("sha256") != digest
        ):
            raise TransformationReceiptError(f"{task_id}: existing {key} hash binding mismatch")
    return {
        "task_id": task_id,
        "status": "skipped_existing",
        "receipt": str(paths[2]),
        "receipt_sha256": _sha256_bytes(filesystem_path(paths[2]).read_bytes()),
    }


def _task_evidence_payloads(
    inspection: Mapping[str, Any],
    *,
    command: list[str],
    completed: subprocess.CompletedProcess[bytes],
    findings: list[dict[str, Any]],
    created_at: str,
    names: tuple[str, str, str],
) -> tuple[bytes, bytes, bytes]:
    target = dict(inspection["target_subject"])
    task_id = str(inspection["task_id"])
    task_module = str(inspection["focused_build"]["command"][-1])
    if task_module not in command[2:]:
        raise TransformationReceiptError(f"{task_id}: batch build omitted the task module")
    build = {
        "schema": BUILD_SCHEMA,
        "task_id": task_id,
        "subject_id": target["subject_id"],
        "bundle_hash": target["bundle_hash"],
        "primary_hash": target["primary_hash"],
        "commit": target["source_commit"],
        "status": "pass",
        "success": True,
        "exit_code": 0,
        "command": command,
        "task_module": task_module,
        "cwd": str(inspection["build_checkout"]),
        "stdout": completed.stdout.decode("utf-8", errors="replace"),
        "stderr": completed.stderr.decode("utf-8", errors="replace"),
        "completed_at": created_at,
    }
    forbidden = {
        "schema": FORBIDDEN_SCHEMA,
        "task_id": task_id,
        "subject_id": target["subject_id"],
        "bundle_hash": target["bundle_hash"],
        "primary_hash": target["primary_hash"],
        "commit": target["source_commit"],
        "status": "pass" if not findings else "fail",
        "tokens": sorted(FORBIDDEN_PATTERNS),
        "matches": findings,
        "completed_at": created_at,
    }
    if findings:
        raise TransformationReceiptError(
            f"{task_id}: forbidden-token scan found {len(findings)} match(es)"
        )
    build_bytes = _json_bytes(build)
    forbidden_bytes = _json_bytes(forbidden)
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "task_id": task_id,
        "created_at": created_at,
        "catalog_id": inspection["catalog_id"],
        "transformation_kind": "path_relocation",
        "mechanical_status": "pass",
        "source_review": inspection["source_review"],
        "source_subject": inspection["source_subject"],
        "target_subject": target,
        "comparison": {
            "classification": "path_only_relocation",
            "primary_equal": True,
            "content_multiset_equal": True,
        },
        "checks": {
            "build": {
                "status": "pass",
                "artifact": {"path": names[0], "sha256": _sha256_bytes(build_bytes)},
            },
            "forbidden_scan": {
                "status": "pass",
                "artifact": {"path": names[1], "sha256": _sha256_bytes(forbidden_bytes)},
            },
        },
    }
    return build_bytes, forbidden_bytes, _json_bytes(receipt)


def emit_validated_transformation(
    *,
    store: WorkspaceStateStore,
    workspace_root: Path,
    runtime_root: Path,
    task_id: str,
    output_dir: Path,
    source_review_id: str = "",
    checkout: Path | None = None,
    timeout: int = 1800,
) -> dict[str, Any]:
    """Build, scan, and emit immutable evidence; never update SQLite."""

    if timeout <= 0:
        raise TransformationReceiptError("Build timeout must be positive")
    inspection = inspect_validated_transformation(
        store=store,
        workspace_root=workspace_root,
        runtime_root=runtime_root,
        task_id=task_id,
        source_review_id=source_review_id,
        checkout=checkout,
    )
    mat_repo = Path(str(inspection["mat_repo"]))
    build_checkout = Path(str(inspection["build_checkout"]))
    command = [str(item) for item in inspection["focused_build"]["command"]]
    completed = _run(build_checkout, *command, timeout=timeout)
    if completed.returncode != 0:
        raise TransformationReceiptError(
            f"{inspection['task_id']}: focused build failed with exit code {completed.returncode}"
        )
    created_at = _utc_now()
    target = dict(inspection["target_subject"])
    build = {
        "schema": BUILD_SCHEMA,
        "task_id": inspection["task_id"],
        "subject_id": target["subject_id"],
        "bundle_hash": target["bundle_hash"],
        "primary_hash": target["primary_hash"],
        "commit": target["source_commit"],
        "status": "pass" if completed.returncode == 0 else "fail",
        "success": completed.returncode == 0,
        "exit_code": completed.returncode,
        "command": command,
        "cwd": str(build_checkout),
        "stdout": completed.stdout.decode("utf-8", errors="replace"),
        "stderr": completed.stderr.decode("utf-8", errors="replace"),
        "completed_at": created_at,
    }
    findings = _forbidden_findings(mat_repo, target)
    forbidden = {
        "schema": FORBIDDEN_SCHEMA,
        "task_id": inspection["task_id"],
        "subject_id": target["subject_id"],
        "bundle_hash": target["bundle_hash"],
        "primary_hash": target["primary_hash"],
        "commit": target["source_commit"],
        "status": "pass" if not findings else "fail",
        "tokens": sorted(FORBIDDEN_PATTERNS),
        "matches": findings,
        "completed_at": created_at,
    }
    if findings:
        raise TransformationReceiptError(
            f"{inspection['task_id']}: forbidden-token scan found {len(findings)} match(es)"
        )
    _revalidate_emit_heads(inspection)

    output = output_dir.expanduser().resolve()
    stem = str(inspection["task_id"])
    build_name = f"validated_transformation_build_{stem}.json"
    forbidden_name = f"validated_transformation_forbidden_scan_{stem}.json"
    receipt_name = f"validated_transformation_receipt_{stem}.json"
    build_bytes = _json_bytes(build)
    forbidden_bytes = _json_bytes(forbidden)
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "task_id": inspection["task_id"],
        "created_at": created_at,
        "catalog_id": inspection["catalog_id"],
        "transformation_kind": "path_relocation",
        "mechanical_status": "pass",
        "source_review": inspection["source_review"],
        "source_subject": inspection["source_subject"],
        "target_subject": target,
        "comparison": {
            "classification": "path_only_relocation",
            "primary_equal": True,
            "content_multiset_equal": True,
        },
        "checks": {
            "build": {
                "status": "pass",
                "artifact": {"path": build_name, "sha256": _sha256_bytes(build_bytes)},
            },
            "forbidden_scan": {
                "status": "pass",
                "artifact": {"path": forbidden_name, "sha256": _sha256_bytes(forbidden_bytes)},
            },
        },
    }
    receipt_bytes = _json_bytes(receipt)
    paths = [output / build_name, output / forbidden_name, output / receipt_name]
    existing = [str(path) for path in paths if path.exists()]
    if existing:
        raise TransformationReceiptError(
            "Refusing to overwrite immutable evidence: " + ", ".join(existing)
        )
    _write_new(paths[0], build_bytes)
    _write_new(paths[1], forbidden_bytes)
    _write_new(paths[2], receipt_bytes)
    return {
        "status": "emitted",
        "task_id": inspection["task_id"],
        "catalog_mat_commit": inspection["catalog_mat_commit"],
        "source_review_id": inspection["source_review"]["review_id"],
        "target_subject_id": target["subject_id"],
        "build_evidence": str(paths[0]),
        "forbidden_scan_evidence": str(paths[1]),
        "receipt": str(paths[2]),
        "receipt_sha256": _sha256_bytes(receipt_bytes),
    }


def emit_validated_transformations_batch(
    *,
    store: WorkspaceStateStore,
    workspace_root: Path,
    runtime_root: Path,
    task_ids: list[str],
    output_dir: Path,
    checkout: Path | None = None,
    timeout: int = 1800,
    skip_existing: bool = True,
) -> dict[str, Any]:
    """Emit task-bound receipts after one catalog scan and one combined Lake build."""

    if timeout <= 0:
        raise TransformationReceiptError("Build timeout must be positive")
    inspections = _inspect_validated_transformations(
        store=store,
        workspace_root=workspace_root,
        runtime_root=runtime_root,
        task_ids=task_ids,
        checkout=checkout,
        require_clean_checkout=False,
    )
    output = output_dir.expanduser().resolve()
    pending: list[tuple[dict[str, Any], tuple[Path, Path, Path]]] = []
    skipped: list[dict[str, Any]] = []
    for inspection in inspections:
        task_id = str(inspection["task_id"])
        paths = _evidence_paths(output / task_id, task_id)
        if any(path.exists() for path in paths):
            if not skip_existing:
                raise TransformationReceiptError(
                    f"{inspection['task_id']}: immutable evidence already exists"
                )
            skipped.append(_validate_existing_evidence(inspection, paths))
        else:
            pending.append((inspection, paths))
    if not pending:
        return {
            "status": "all_existing",
            "catalog_mat_commit": inspections[0]["catalog_mat_commit"],
            "requested": len(inspections),
            "emitted": 0,
            "skipped_existing": len(skipped),
            "tasks": skipped,
        }

    if pending[0][0].get("build_checkout_dirty"):
        raise TransformationReceiptError(
            "MAT build checkout is not clean; pending batch tasks cannot be certified"
        )

    modules = sorted(
        {str(inspection["focused_build"]["command"][-1]) for inspection, _paths in pending}
    )
    command = ["lake", "build", *modules]
    build_checkout = Path(str(pending[0][0]["build_checkout"]))
    completed = _run(build_checkout, *command, timeout=timeout)
    if completed.returncode != 0:
        raise TransformationReceiptError(
            f"Batch focused build failed with exit code {completed.returncode}"
        )
    created_at = _utc_now()
    prepared: list[
        tuple[dict[str, Any], tuple[Path, Path, Path], tuple[bytes, bytes, bytes]]
    ] = []
    for inspection, paths in pending:
        findings = _forbidden_findings(
            Path(str(inspection["mat_repo"])), inspection["target_subject"]
        )
        payloads = _task_evidence_payloads(
            inspection,
            command=command,
            completed=completed,
            findings=findings,
            created_at=created_at,
            names=tuple(path.name for path in paths),
        )
        prepared.append((inspection, paths, payloads))
    _revalidate_emit_heads(pending[0][0])
    raced = [str(path) for _inspection, paths, _payloads in prepared for path in paths if path.exists()]
    if raced:
        raise TransformationReceiptError(
            "Immutable evidence appeared during batch validation; refusing overwrite: "
            + ", ".join(raced)
        )

    emitted: list[dict[str, Any]] = []
    for inspection, paths, payloads in prepared:
        for path, payload in zip(paths, payloads, strict=True):
            _write_new(path, payload)
        emitted.append(
            {
                "task_id": inspection["task_id"],
                "status": "emitted",
                "source_review_id": inspection["source_review"]["review_id"],
                "target_subject_id": inspection["target_subject"]["subject_id"],
                "receipt": str(paths[2]),
                "receipt_sha256": _sha256_bytes(payloads[2]),
            }
        )
    tasks = sorted([*skipped, *emitted], key=lambda item: str(item["task_id"]))
    return {
        "status": "emitted",
        "catalog_mat_commit": inspections[0]["catalog_mat_commit"],
        "requested": len(inspections),
        "emitted": len(emitted),
        "skipped_existing": len(skipped),
        "build_command": command,
        "tasks": tasks,
    }
