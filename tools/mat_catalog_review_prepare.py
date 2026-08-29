#!/usr/bin/env python3
"""Prepare a canonical p11/r9 review pack for one current MAT catalog task.

Preparation is read-only with respect to Lean sources and SQLite.  It derives
the exact task-owned bundle from the catalog-pinned MAT commit, proves that the
clean build checkout has the same complete Lean tree, runs a focused build and
forbidden-token scan, then delegates artifact rendering to the tracked Phase 2
handoff writer.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.core import get_settings, open_runtime_ledger
from src.toy_apollo.phase2_pack_generation import _write_codex_handoff_review_artifacts
from src.toy_apollo.state_reconcile import git_file_at_ref
from src.toy_apollo.state_exact_build_batch import (
    ExactBuildBatchError,
    catalog_owned_build_modules,
    validate_current_exact_build_receipt,
)
from src.toy_apollo.state_store import (
    SubjectBundle,
    canonical_subject_bytes,
    sha256_bytes,
    sha256_file,
    sha256_json,
    utc_now,
)
from src.toy_apollo.task_catalog import TaskCatalog, load_catalog


CAMPAIGN_ID = "modern_catalog_gap_closure_20260807"
REVIEW_SUPPLEMENT_SPEC_SCHEMA = "mat.catalog.review-supplement-spec.v1"
REVIEW_SUPPLEMENT_EVIDENCE_SCHEMA = "mat.catalog.review-supplement-evidence.v1"
FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*(?:private\s+)?axiom\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
}


class PrepareError(RuntimeError):
    pass


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(
        json.dumps(dict(payload), indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _write_immutable_json(path: Path, payload: Mapping[str, Any]) -> None:
    """Write a generated evidence object once, allowing only an identical replay."""
    if path.exists():
        try:
            existing = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise PrepareError(f"Existing review supplement is unreadable: {path}: {exc}") from exc
        if existing != dict(payload):
            raise PrepareError(f"Refusing to overwrite different review supplement evidence: {path}")
        return
    _write_json(path, payload)


def _write_immutable_bytes(path: Path, payload: bytes) -> None:
    """Create a pack-local artifact once, allowing only byte-identical replay."""
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        if not path.is_file() or path.read_bytes() != payload:
            raise PrepareError(f"Refusing to overwrite different build receipt: {path}")
        return
    try:
        with path.open("xb") as handle:
            handle.write(payload)
    except FileExistsError as exc:
        raise PrepareError(f"Build receipt appeared concurrently: {path}") from exc


def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    completed = subprocess.run(
        ["git", "-C", str(repo), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise PrepareError(f"Git command failed: git {' '.join(args)}: {detail}")
    return completed


def _git_text(repo: Path, *args: str) -> str:
    return _git(repo, *args).stdout.decode("utf-8", errors="replace").strip()


def _validate_exact_checkout_freshness(
    mat_repo: Path, build_root: Path, commit: str
) -> None:
    if _git_text(mat_repo, "rev-parse", "origin/main") != commit:
        raise PrepareError("MAT origin/main changed during exact-build preparation")
    head = _git_text(build_root, "rev-parse", "HEAD")
    if head != commit:
        raise PrepareError("Build checkout HEAD changed during exact-build preparation")
    if _git_text(build_root, "status", "--porcelain", "--untracked-files=all"):
        raise PrepareError("Build checkout became dirty during exact-build preparation")
    lean_delta = _git(
        mat_repo, "diff", "--name-only", head, commit, "--", "*.lean"
    ).stdout.decode("utf-8", errors="replace").splitlines()
    if lean_delta:
        raise PrepareError(
            f"Build checkout Lean tree drifted during preparation: {lean_delta[:10]}"
        )


def _require_object(value: Any, *, label: str) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise PrepareError(f"Review supplement {label} must be an object")
    return dict(value)


def _require_list(value: Any, *, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise PrepareError(f"Review supplement {label} must be a list")
    return value


def _require_text(value: Any, *, label: str) -> str:
    text = str(value or "").strip()
    if not text:
        raise PrepareError(f"Review supplement {label} must be non-empty")
    return text


def _spec_path(spec_path: Path, raw: Any, *, label: str) -> Path:
    path = Path(_require_text(raw, label=label)).expanduser()
    if not path.is_absolute():
        path = spec_path.parent / path
    path = path.resolve()
    if not path.is_file():
        raise PrepareError(f"Review supplement {label} is missing: {path}")
    return path


def _git_commit(repo: Path, ref: str, *, label: str) -> str:
    if not repo.is_dir():
        raise PrepareError(f"Review supplement {label} repository is missing: {repo}")
    return _git_text(repo, "rev-parse", f"{ref}^{{commit}}")


def _git_blob(repo: Path, commit: str, path: str, *, label: str) -> tuple[str, bytes]:
    blob = _git_text(repo, "rev-parse", f"{commit}:{path}")
    if not blob:
        raise PrepareError(f"Review supplement {label} has no Git blob: {commit}:{path}")
    return blob, git_file_at_ref(repo, commit, path)


def _read_utf8_evidence(path: Path, *, label: str) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise PrepareError(f"Review supplement {label} must be readable UTF-8 text: {path}: {exc}") from exc


def _build_review_supplement(
    *,
    spec_path: Path,
    task_id: str,
    target_commit: str,
    subject: SubjectBundle,
    mat_repo: Path,
) -> dict[str, Any]:
    """Validate and fully embed reviewer context without expanding task ownership."""
    try:
        spec = json.loads(spec_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PrepareError(f"Invalid review supplement spec {spec_path}: {exc}") from exc
    spec = _require_object(spec, label="spec")
    if spec.get("schema") != REVIEW_SUPPLEMENT_SPEC_SCHEMA:
        raise PrepareError("Unsupported review supplement spec schema")
    if str(spec.get("task_id", "") or "") != task_id:
        raise PrepareError("Review supplement task_id does not match the prepared task")
    if str(spec.get("target_commit", "") or "") != target_commit:
        raise PrepareError("Review supplement target_commit does not match pinned MAT")

    upstream_spec = _require_object(spec.get("kenneth_upstream"), label="kenneth_upstream")
    upstream_status = str(upstream_spec.get("status", "") or "")
    if upstream_status == "absent":
        upstream = {
            "status": "absent",
            "reason": _require_text(upstream_spec.get("reason"), label="kenneth_upstream.reason"),
        }
    elif upstream_status == "present":
        repo_raw = _require_text(upstream_spec.get("repo"), label="kenneth_upstream.repo")
        upstream_repo = Path(repo_raw).expanduser()
        if not upstream_repo.is_absolute():
            upstream_repo = spec_path.parent / upstream_repo
        upstream_repo = upstream_repo.resolve()
        upstream_ref = _require_text(upstream_spec.get("ref"), label="kenneth_upstream.ref")
        upstream_commit = _require_text(
            upstream_spec.get("commit"), label="kenneth_upstream.commit"
        )
        if _git_commit(upstream_repo, upstream_ref, label="kenneth_upstream") != upstream_commit:
            raise PrepareError("Kenneth upstream ref does not resolve to the declared commit")
        upstream_files: list[dict[str, Any]] = []
        for index, raw_file in enumerate(
            _require_list(upstream_spec.get("files"), label="kenneth_upstream.files")
        ):
            item = _require_object(raw_file, label=f"kenneth_upstream.files[{index}]")
            path = _require_text(item.get("path"), label=f"kenneth_upstream.files[{index}].path")
            expected_blob = _require_text(
                item.get("blob"), label=f"kenneth_upstream.files[{index}].blob"
            )
            target_path = _require_text(
                item.get("target_path"),
                label=f"kenneth_upstream.files[{index}].target_path",
            )
            relationship = _require_text(
                item.get("relationship"),
                label=f"kenneth_upstream.files[{index}].relationship",
            )
            if relationship != "byte_identical":
                raise PrepareError(
                    f"Kenneth upstream files[{index}].relationship must be byte_identical"
                )
            actual_blob, raw = _git_blob(
                upstream_repo, upstream_commit, path, label="Kenneth upstream"
            )
            if actual_blob != expected_blob:
                raise PrepareError(f"Kenneth upstream blob mismatch: {path}")
            target_blob, target_raw = _git_blob(
                mat_repo, target_commit, target_path, label="MAT Kenneth target"
            )
            if raw != target_raw:
                raise PrepareError(
                    f"Kenneth upstream byte-identical target mismatch: {path} != {target_path}"
                )
            try:
                content = raw.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise PrepareError(f"Kenneth upstream file is not UTF-8: {path}") from exc
            upstream_files.append(
                {
                    "path": path,
                    "git_blob_sha": actual_blob,
                    "content_sha256": sha256_bytes(raw),
                    "target_path": target_path,
                    "target_git_blob_sha": target_blob,
                    "target_content_sha256": sha256_bytes(target_raw),
                    "relationship": relationship,
                    "content": content,
                }
            )
        if not upstream_files:
            raise PrepareError("Kenneth upstream present status requires at least one file")
        upstream = {
            "status": "present",
            "repo": str(upstream_repo),
            "ref": upstream_ref,
            "commit": upstream_commit,
            "files": upstream_files,
        }
    else:
        raise PrepareError("Kenneth upstream status must be present or absent")

    historical: list[dict[str, Any]] = []
    for index, raw_evidence in enumerate(
        _require_list(spec.get("historical_evidence", []), label="historical_evidence")
    ):
        item = _require_object(raw_evidence, label=f"historical_evidence[{index}]")
        path = _spec_path(
            spec_path, item.get("path"), label=f"historical_evidence[{index}].path"
        )
        expected_hash = _require_text(
            item.get("sha256"), label=f"historical_evidence[{index}].sha256"
        )
        actual_hash = sha256_file(path)
        if actual_hash != expected_hash:
            raise PrepareError(f"Historical evidence hash mismatch: {path}")
        historical.append(
            {
                "path": str(path),
                "sha256": actual_hash,
                "purpose": _require_text(
                    item.get("purpose"), label=f"historical_evidence[{index}].purpose"
                ),
                "content": _read_utf8_evidence(path, label="historical evidence"),
            }
        )

    proof_closure: list[dict[str, Any]] = []
    for index, raw_closure in enumerate(
        _require_list(spec.get("proof_closure", []), label="proof_closure")
    ):
        item = _require_object(raw_closure, label=f"proof_closure[{index}]")
        path = _require_text(item.get("path"), label=f"proof_closure[{index}].path")
        expected_blob = _require_text(item.get("blob"), label=f"proof_closure[{index}].blob")
        actual_blob, raw = _git_blob(mat_repo, target_commit, path, label="MAT proof closure")
        if actual_blob != expected_blob:
            raise PrepareError(f"MAT proof-closure blob mismatch: {path}")
        try:
            content = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise PrepareError(f"MAT proof-closure file is not UTF-8: {path}") from exc
        proof_closure.append(
            {
                "path": path,
                "target_commit": target_commit,
                "git_blob_sha": actual_blob,
                "content_sha256": sha256_bytes(raw),
                "purpose": _require_text(
                    item.get("purpose"), label=f"proof_closure[{index}].purpose"
                ),
                "content": content,
            }
        )

    resolutions: list[dict[str, str]] = []
    for index, raw_resolution in enumerate(
        _require_list(spec.get("risk_resolutions", []), label="risk_resolutions")
    ):
        item = _require_object(raw_resolution, label=f"risk_resolutions[{index}]")
        status = str(item.get("status", "") or "")
        if status not in {"resolved", "superseded"}:
            raise PrepareError(
                f"Review supplement risk_resolutions[{index}].status must be resolved or superseded"
            )
        resolutions.append(
            {
                "risk": _require_text(item.get("risk"), label=f"risk_resolutions[{index}].risk"),
                "status": status,
                "rationale": _require_text(
                    item.get("rationale"), label=f"risk_resolutions[{index}].rationale"
                ),
            }
        )

    return {
        "schema": REVIEW_SUPPLEMENT_EVIDENCE_SCHEMA,
        "task_id": task_id,
        "target_commit": target_commit,
        "subject_id": subject.subject_id,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path,
        "authority": "review_context_only; no verdict or task ownership change",
        "kenneth_upstream": upstream,
        "historical_evidence": historical,
        "proof_closure": proof_closure,
        "risk_resolutions": resolutions,
        "reviewer_instruction": _require_text(
            spec.get("reviewer_instruction"), label="reviewer_instruction"
        ),
        "source_spec": {
            "path": str(spec_path.resolve()),
            "sha256": sha256_file(spec_path),
        },
    }


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


def _catalog_subject(catalog: TaskCatalog, *, task_id: str, mat_repo: Path) -> SubjectBundle:
    task = next((item for item in catalog.tasks if item.task_id == task_id), None)
    if task is None:
        raise PrepareError(f"Task is not in the pinned catalog: {task_id}")
    paths = catalog.owned_paths(task_id)
    if not paths or task.primary_path not in paths:
        raise PrepareError(f"Catalog task-owned bundle is incomplete: {task_id}")
    files = {path: git_file_at_ref(mat_repo, catalog.mat_commit, path) for path in paths}
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
        raise PrepareError(f"Task is not in the pinned catalog: {task_id}")
    paths = catalog.owned_paths(task_id)
    if not paths or task.primary_path not in paths:
        raise PrepareError(f"Catalog task-owned bundle is incomplete: {task_id}")
    files: dict[str, bytes] = {}
    for path in paths:
        candidate_path = candidate_root / Path(path)
        if not candidate_path.is_file():
            raise PrepareError(f"Candidate task-owned file is missing: {candidate_path}")
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


def _pinned_task(catalog: TaskCatalog, *, task_id: str, runtime_root: Path) -> dict[str, Any]:
    entry = next((item for item in catalog.tasks if item.task_id == task_id), None)
    if entry is None:
        raise PrepareError(f"Unknown catalog task: {task_id}")
    raw = _git(runtime_root, "show", f"{catalog.toy_commit}:{entry.source_plan_path}").stdout
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PrepareError(f"Pinned task plan is invalid: {entry.source_plan_path}: {exc}") from exc
    matches = [
        item
        for item in payload
        if isinstance(item, dict) and str(item.get("block_id", "") or "") == task_id
    ] if isinstance(payload, list) else []
    if len(matches) != 1:
        raise PrepareError(f"Pinned plan does not contain one unique task: {task_id}")
    return dict(matches[0])


def _strip_comments(text: str) -> str:
    without_blocks = re.sub(r"/\*.*?\*/", " ", text, flags=re.DOTALL)
    return re.sub(r"(?m)--.*$", " ", without_blocks)


def _forbidden_findings(
    subject: SubjectBundle,
    mat_repo: Path,
    *,
    content_root: Path | None = None,
) -> dict[str, list[str]]:
    findings: dict[str, list[str]] = {}
    for item in subject.files:
        if content_root is None:
            raw = git_file_at_ref(mat_repo, subject.source_commit, item.path)
        else:
            raw = (content_root / Path(item.path)).read_bytes()
        text = raw.decode("utf-8", errors="replace")
        clean = _strip_comments(text)
        matched = [name for name, pattern in FORBIDDEN_PATTERNS.items() if pattern.search(clean)]
        if matched:
            findings[item.path] = matched
    return findings


def _direct_consumers(
    catalog: TaskCatalog,
    *,
    task_id: str,
    mat_repo: Path,
) -> list[dict[str, str]]:
    owned_modules = [item for item in catalog.modules if item.owner_task_id == task_id]
    module_names = {item.module_name for item in owned_modules}
    consumers: dict[tuple[str, str], dict[str, str]] = {}
    for module_name in sorted(module_names):
        completed = _git(
            mat_repo,
            "grep",
            "-l",
            f"^import {module_name}$",
            catalog.mat_commit,
            "--",
            "*.lean",
            check=False,
        )
        if completed.returncode not in {0, 1}:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise PrepareError(f"Unable to scan MAT direct consumers: {detail}")
        for line in completed.stdout.decode("utf-8", errors="replace").splitlines():
            raw_path = line.split(":", 1)[-1].strip()
            owner = catalog.task_for_path(raw_path)
            key = (owner or "", raw_path)
            consumers[key] = {
                "task_id": owner or "",
                "path": raw_path,
                "relation": "exact_current_direct_import",
            }
    return [consumers[key] for key in sorted(consumers)]


def _focused_build(build_root: Path, module_names: Iterable[str]) -> dict[str, Any]:
    command = ["lake", "build", *module_names]
    started = time.perf_counter()
    completed = subprocess.run(
        command,
        cwd=str(build_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    return {
        "command": command,
        "cwd": str(build_root),
        "exit_code": completed.returncode,
        "duration_seconds": round(time.perf_counter() - started, 3),
        "stdout": completed.stdout.decode("utf-8", errors="replace"),
        "stderr": completed.stderr.decode("utf-8", errors="replace"),
    }


def prepare_review(
    *,
    task_id: str,
    attempt: int,
    pack_dir: Path,
    workspace_root: Path,
    runtime_root: Path,
    build_root: Path,
    candidate_root: Path | None = None,
    review_supplement_spec: Path | None = None,
    prebuilt_exact_build_receipt: Path | None = None,
    campaign_id: str = CAMPAIGN_ID,
) -> dict[str, Any]:
    campaign_id = campaign_id.strip()
    if not campaign_id:
        raise PrepareError("Campaign id must be non-empty")
    if (
        prebuilt_exact_build_receipt is not None
        and not prebuilt_exact_build_receipt.expanduser().is_absolute()
    ):
        raise PrepareError("Prebuilt exact-build receipt path must be absolute")
    build_root = build_root.resolve()
    mat_repo = (workspace_root / "MAT3280-formalization-output").resolve()
    if candidate_root is not None and candidate_root.resolve() != build_root.resolve():
        raise PrepareError("Candidate root must be the checkout used for the focused build")
    if candidate_root is not None and review_supplement_spec is not None:
        raise PrepareError("Review supplements currently bind exact MAT main subjects only")
    if candidate_root is not None and prebuilt_exact_build_receipt is not None:
        raise PrepareError("Prebuilt exact-MAT receipts cannot be used for candidates")
    catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    current_main = _git_text(mat_repo, "rev-parse", "origin/main")
    if current_main != catalog.mat_commit:
        raise PrepareError(
            f"Catalog MAT commit is not current origin/main: {catalog.mat_commit} != {current_main}"
        )
    build_commit = _git_text(build_root, "rev-parse", "HEAD")
    status = _git_text(build_root, "status", "--porcelain", "--untracked-files=all")
    if status and candidate_root is None:
        raise PrepareError(f"Build checkout is not clean: {build_root}")
    lean_delta = _git(
        mat_repo,
        "diff",
        "--name-only",
        build_commit,
        catalog.mat_commit,
        "--",
        "*.lean",
    ).stdout.decode("utf-8", errors="replace").splitlines()
    if lean_delta:
        raise PrepareError(f"Build checkout Lean tree differs from current MAT: {lean_delta[:10]}")

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
    task = _pinned_task(catalog, task_id=task_id, runtime_root=runtime_root)
    primary_module = subject.primary_path.removesuffix(".lean").replace("/", ".")
    primary_modules, owned_modules = catalog_owned_build_modules(catalog, [task_id])
    if primary_modules[task_id] != primary_module:
        raise PrepareError("Catalog primary module does not match the exact subject")
    task_modules = owned_modules[task_id]
    prebuilt_source_path: Path | None = None
    prebuilt_source_hash = ""
    if prebuilt_exact_build_receipt is not None:
        raw_prebuilt = prebuilt_exact_build_receipt.expanduser()
        if not raw_prebuilt.is_absolute():
            raise PrepareError("Prebuilt exact-build receipt path must be absolute")
        prebuilt_source_path = raw_prebuilt.resolve()
        if not prebuilt_source_path.is_file():
            raise PrepareError(
                f"Prebuilt exact-build receipt is missing: {prebuilt_source_path}"
            )
        prebuilt_source_hash = sha256_file(prebuilt_source_path)
        try:
            build_receipt = validate_current_exact_build_receipt(
                prebuilt_source_path,
                subject=subject,
                primary_module=primary_module,
                task_modules=task_modules,
                commit=catalog.mat_commit,
                checkout=build_root,
            )
        except ExactBuildBatchError as exc:
            raise PrepareError(f"Prebuilt exact-build receipt is invalid: {exc}") from exc
        source_bytes = prebuilt_source_path.read_bytes()
        if sha256_bytes(source_bytes) != prebuilt_source_hash:
            raise PrepareError("Prebuilt exact-build receipt changed during validation")
        focused = dict(build_receipt["focused_build"])
        build_receipt_mode = "reused_prebuilt"
    else:
        focused = _focused_build(build_root, task_modules)
        build_receipt_mode = "built_during_prepare"
    findings = _forbidden_findings(
        subject,
        mat_repo,
        content_root=candidate_root,
    )
    if findings:
        raise PrepareError(
            f"Forbidden-token scan failed for {task_id}: findings={findings}"
        )
    if prebuilt_source_path is None:
        focused.update(
            {
                "task_module": primary_module,
                "task_module_in_combined_command": primary_module
                in focused["command"][2:],
                "task_modules": list(task_modules),
                "task_modules_in_combined_command": {
                    module: module in focused["command"][2:] for module in task_modules
                },
                "batch_index": 1,
                "batch_size": 1,
            }
        )
        build_receipt = {
            "schema": (
                "mat.catalog.exact-build.v1"
                if candidate_root is None
                else "mat.catalog.candidate-exact-build.v1"
            ),
            "campaign_id": campaign_id,
            "task_id": task_id,
            "commit": subject.source_commit,
            "subject_id": subject.subject_id,
            "bundle_hash": subject.bundle_hash,
            "primary_hash": subject.primary_hash,
            "primary_path": subject.primary_path,
            "subject_files": subject.manifest(),
            "success": focused["exit_code"] == 0 and not findings,
            "exit_code": focused["exit_code"],
            "focused_build": focused,
            "forbidden_token_scan": {
                "exit_code": 0 if not findings else 1,
                "findings": findings,
                "tokens": sorted(FORBIDDEN_PATTERNS),
            },
            "lean_tree_equivalence": (
                {
                    "build_commit": build_commit,
                    "target_commit": subject.source_commit,
                    "changed_lean_files": lean_delta,
                    "build_checkout_clean": True,
                }
                if candidate_root is None
                else None
            ),
            "candidate_lineage": (
                None
                if candidate_root is None
                else {
                    "parent_commit": catalog.mat_commit,
                    "parent_subject_id": parent_subject.subject_id,
                    "build_commit": build_commit,
                    "complete_base_lean_tree_changed_files": lean_delta,
                    "candidate_root": str(candidate_root),
                    "worktree_status": status.splitlines(),
                }
            ),
            "created_at": utc_now(),
        }
    if not build_receipt["success"]:
        raise PrepareError(
            f"Focused build/forbidden scan failed for {task_id}: "
            f"build={focused['exit_code']} findings={findings}"
        )
    if candidate_root is None:
        _validate_exact_checkout_freshness(
            mat_repo, build_root, catalog.mat_commit
        )
    pack_dir.mkdir(parents=True, exist_ok=True)
    build_path = pack_dir / f"exact_mat_build_receipt_v{attempt}.json"
    if prebuilt_source_path is not None:
        _write_immutable_bytes(build_path, source_bytes)
    else:
        _write_json(build_path, build_receipt)
    if candidate_root is None:
        try:
            validate_current_exact_build_receipt(
                build_path.resolve(),
                subject=subject,
                primary_module=primary_module,
                task_modules=task_modules,
                commit=catalog.mat_commit,
                checkout=build_root,
            )
        except ExactBuildBatchError as exc:
            raise PrepareError(f"Pack-local exact-build receipt is invalid: {exc}") from exc

    settings = get_settings()
    ledger = open_runtime_ledger(settings, read_only=True)
    exact_primary = build_root / Path(subject.primary_path)
    exact_primary_hash = (
        sha256_bytes(canonical_subject_bytes(subject.primary_path, exact_primary.read_bytes()))
        if exact_primary.is_file()
        else ""
    )
    if exact_primary_hash != subject.primary_hash:
        raise PrepareError("Content-equivalent build checkout lacks the exact primary subject")
    candidate_code = (
        git_file_at_ref(mat_repo, subject.source_commit, subject.primary_path).decode("utf-8")
        if candidate_root is None
        else (candidate_root / Path(subject.primary_path)).read_text(encoding="utf-8")
    )
    direct_consumers = _direct_consumers(
        catalog,
        task_id=task_id,
        mat_repo=mat_repo,
    )
    exact_basis = {
        "external_subject": {
            "kind": (
                "mat_exact_git_bundle"
                if candidate_root is None
                else "mat_exact_local_candidate_bundle"
            ),
            "repo": str(mat_repo),
            "ref": "origin/main" if candidate_root is None else "local-candidate",
            "commit": subject.source_commit,
            "subject_id": subject.subject_id,
            "bundle_hash": subject.bundle_hash,
            "primary_hash": subject.primary_hash,
            "primary_path": subject.primary_path,
            "files": subject.manifest(),
            "focused_build_receipt": str(build_path.resolve()),
            "focused_build_receipt_hash": sha256_file(build_path),
        },
        "exact_mat_direct_downstream_consumers": direct_consumers,
        "catalog_id": catalog.catalog_id,
        "review_reason": "all_catalog_modern_gap_closure",
        "build_receipt_mode": build_receipt_mode,
        "build_checkout": str(build_root),
    }
    if prebuilt_source_path is not None:
        exact_basis.update(
            {
                "prebuilt_exact_build_receipt_source": str(prebuilt_source_path),
                "prebuilt_exact_build_receipt_source_hash": prebuilt_source_hash,
            }
        )
    context_parts = ["\n".join(
        [
            (
                "# Exact current MAT catalog authority"
                if candidate_root is None
                else "# Exact repaired MAT candidate"
            ),
            "",
            f"- Repository: `{mat_repo}`",
            "- Ref: `origin/main`" if candidate_root is None else "- Ref: `local-candidate`",
            f"- Commit: `{subject.source_commit}`",
            f"- Exact subject id: `{subject.subject_id}`",
            f"- Exact bundle hash: `{subject.bundle_hash}`",
            f"- Exact primary hash: `{subject.primary_hash}`",
            f"- Focused build receipt: `{build_path.resolve()}`",
            f"- Direct consumers: `{len(direct_consumers)}`",
            (
                "- The build checkout is clean and its complete Lean tree is byte-identical to the reviewed commit."
                if candidate_root is None
                else "- This exact local candidate descends from current MAT main; only the task-owned bundle is authoritative for this review."
            ),
            "- `review_subject_kind=external_pr` is the runtime's bound external-bundle channel; this subject is MAT main, not a pull request.",
            "- Old-rubric PASS evidence is context only and cannot satisfy rubric 9.",
            "- Reject adapter-only shortcuts, relocated public proof premises, forbidden tokens, weakened statements, or open proof debt.",
        ]
    )]
    supplement_path: Path | None = None
    supplement_hash = ""
    supplement_content_hash = ""
    if review_supplement_spec is not None:
        supplement = _build_review_supplement(
            spec_path=review_supplement_spec.resolve(),
            task_id=task_id,
            target_commit=catalog.mat_commit,
            subject=subject,
            mat_repo=mat_repo,
        )
        supplement_path = pack_dir / f"review_supplement_evidence_v{attempt}.json"
        _write_immutable_json(supplement_path, supplement)
        supplement_hash = sha256_file(supplement_path)
        supplement_content_hash = sha256_json(supplement)
        exact_basis.update(
            {
                "review_supplement": supplement,
                "review_supplement_file": str(supplement_path.resolve()),
                "review_supplement_file_sha256": supplement_hash,
                "review_supplement_content_sha256": supplement_content_hash,
            }
        )
        context_parts.append(
            _render_review_supplement_context(
                supplement,
                file_hash=supplement_hash,
                content_hash=supplement_content_hash,
            )
        )
    context_suffix = "\n\n".join(context_parts)
    artifacts = _write_codex_handoff_review_artifacts(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        attempt=attempt,
        candidate_path=Path(subject.primary_path),
        candidate_code=candidate_code,
        build_summary={
            "success": True,
            "kind": "mat_exact_current_focused_build",
            "review_build_gate_satisfied": True,
            "commit": subject.source_commit,
            "command": focused["command"],
            "receipt_file": str(build_path.resolve()),
            "receipt_hash": sha256_file(build_path),
            "subject_id": subject.subject_id,
            "bundle_hash": subject.bundle_hash,
            "primary_hash": subject.primary_hash,
        },
        mode="mat-catalog-existing-review",
        review_subject_kind="external_pr",
        build_result_file=str(build_path.resolve()),
        build_candidate_file=subject.primary_path,
        build_candidate_hash=subject.primary_hash,
        subject_bundle_override={
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
        },
        review_basis_subject_file=exact_primary,
        review_basis_extra=exact_basis,
        review_context_suffix=context_suffix,
    )
    path_keys = {
        "review_input_file": "review_input_hash",
        "review_request_file": "review_request_hash",
        "review_prompt_file": "review_prompt_hash",
        "review_context_file": "review_context_hash",
        "review_result_template_file": "review_result_template_hash",
    }
    metadata: dict[str, Any] = {
        "schema": (
            "mat.catalog.exact-review-pack.v1"
            if candidate_root is None
            else "mat.catalog.candidate-exact-review-pack.v1"
        ),
        "campaign_id": campaign_id,
        "task_id": task_id,
        "attempt": attempt,
        "dependency_wave": -1,
        "review_reason": "all_catalog_modern_gap_closure",
        "ref": "origin/main" if candidate_root is None else "local-candidate",
        "commit": subject.source_commit,
        "subject_id": subject.subject_id,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path,
        "subject_files": subject.manifest(),
        "build_result_file": str(build_path.resolve()),
        "build_result_hash": sha256_file(build_path),
        "build_receipt_mode": build_receipt_mode,
        "build_checkout": str(build_root),
        "expected_review_result_file": str(Path(artifacts["expected_review_result_file"]).resolve()),
        "prepared_at": utc_now(),
    }
    if prebuilt_source_path is not None:
        metadata.update(
            {
                "prebuilt_exact_build_receipt_source": str(prebuilt_source_path),
                "prebuilt_exact_build_receipt_source_hash": prebuilt_source_hash,
            }
        )
    if supplement_path is not None:
        metadata.update(
            {
                "review_supplement_file": str(supplement_path.resolve()),
                "review_supplement_hash": supplement_hash,
                "review_supplement_content_hash": supplement_content_hash,
                "review_supplement_spec_file": str(review_supplement_spec.resolve()),
                "review_supplement_spec_hash": sha256_file(review_supplement_spec.resolve()),
            }
        )
    for file_key, hash_key in path_keys.items():
        path = Path(str(artifacts[file_key])).resolve()
        metadata[file_key] = str(path)
        metadata[hash_key] = (
            sha256_json(json.loads(path.read_text(encoding="utf-8")))
            if file_key == "review_input_file"
            else sha256_file(path)
        )
    if candidate_root is None:
        _validate_exact_checkout_freshness(
            mat_repo, build_root, catalog.mat_commit
        )
    if prebuilt_source_path is not None:
        if (
            sha256_file(prebuilt_source_path) != prebuilt_source_hash
            or sha256_file(build_path) != prebuilt_source_hash
        ):
            raise PrepareError("Prebuilt or pack-local exact-build receipt changed")
    metadata_path = pack_dir / "mat_exact_subject.json"
    _write_json(metadata_path, metadata)
    return {**metadata, "metadata_file": str(metadata_path.resolve())}


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare one p11/r9 exact-current MAT catalog review pack"
    )
    parser.add_argument("--task", required=True)
    parser.add_argument("--attempt", type=int, default=1)
    parser.add_argument("--pack-dir", type=Path, required=True)
    parser.add_argument("--workspace-root", type=Path, default=REPO_ROOT.parent)
    parser.add_argument("--runtime-root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--build-root",
        type=Path,
        default=REPO_ROOT.parent
        / "_review-worktrees"
        / "mat-rubric78-a5b71f46-20260806",
    )
    parser.add_argument(
        "--candidate-root",
        type=Path,
        help="Prepare an exact repaired candidate bundle from this local MAT worktree",
    )
    parser.add_argument("--campaign-id", default=CAMPAIGN_ID)
    parser.add_argument(
        "--review-supplement-spec",
        type=Path,
        help="Hash-bound author/proof-closure context for an exact review attempt",
    )
    parser.add_argument(
        "--prebuilt-exact-build-receipt",
        type=Path,
        help="Absolute canonical exact-MAT build receipt to validate and copy into the pack",
    )
    args = parser.parse_args()
    if args.attempt < 1:
        raise PrepareError("Attempt must be positive")
    result = prepare_review(
        task_id=args.task,
        attempt=args.attempt,
        pack_dir=args.pack_dir.resolve(),
        workspace_root=args.workspace_root.resolve(),
        runtime_root=args.runtime_root.resolve(),
        build_root=args.build_root.resolve(),
        candidate_root=args.candidate_root.resolve() if args.candidate_root else None,
        review_supplement_spec=(
            args.review_supplement_spec.resolve() if args.review_supplement_spec else None
        ),
        prebuilt_exact_build_receipt=args.prebuilt_exact_build_receipt,
        campaign_id=args.campaign_id,
    )
    print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except PrepareError as exc:
        print(f"MAT_CATALOG_REVIEW_PREPARE_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
