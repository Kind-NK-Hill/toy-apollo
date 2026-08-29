#!/usr/bin/env python3
"""Prepare exact-current review packs from a consolidated supplement manifest."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.block_id_naming import canonicalize_block_id, is_canonical_block_id  # noqa: E402
from src.toy_apollo.state_exact_build_batch import (  # noqa: E402
    ExactBuildBatchError,
    catalog_owned_build_modules,
    validate_current_exact_build_receipt,
)
from src.toy_apollo.state_store import SubjectBundle, sha256_file  # noqa: E402
from src.toy_apollo.task_catalog import TaskCatalog, load_catalog  # noqa: E402
from tools.mat_catalog_review_apply import (  # noqa: E402
    ApplyError,
    _read_json as _read_pack_json,
    _validate_prepare_complete_pack,
    _validate_pack,
)
from tools.mat_catalog_review_prepare import (  # noqa: E402
    PrepareError,
    _catalog_subject,
    _git_text,
    prepare_review,
)


MANIFEST_SCHEMA = "mat.catalog.exact-review-supplement-consolidated-manifest.v1"


class PrepareBatchError(RuntimeError):
    pass


@dataclass(frozen=True)
class PrepareBatchItem:
    task_id: str
    target_commit: str
    subject_id: str
    bundle_hash: str
    primary_hash: str
    supplement_spec: Path
    supplement_sha256: str


def load_prepare_batch_manifest(path: Path) -> tuple[str, tuple[PrepareBatchItem, ...]]:
    manifest_path = path.expanduser().resolve()
    try:
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PrepareBatchError(f"Unable to read consolidated manifest {path}: {exc}") from exc
    if not isinstance(payload, Mapping) or payload.get("schema") != MANIFEST_SCHEMA:
        raise PrepareBatchError(f"Unsupported consolidated supplement manifest: {path}")
    commit = str(payload.get("target_commit", "") or "").strip()
    rows = payload.get("items")
    if len(commit) != 40 or not isinstance(rows, list) or not rows:
        raise PrepareBatchError(f"Consolidated manifest header is malformed: {path}")
    items: list[PrepareBatchItem] = []
    seen: set[str] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            raise PrepareBatchError(f"Manifest item {index} is malformed: {path}")
        task_id = canonicalize_block_id(str(row.get("task_id", "") or ""))
        spec = Path(str(row.get("spec_path", "") or "")).expanduser()
        if (
            not task_id
            or not is_canonical_block_id(task_id)
            or task_id in seen
            or not spec.is_absolute()
            or row.get("spec_schema") != "mat.catalog.review-supplement-spec.v1"
            or row.get("canonical_dry_validation") != "PASS"
            or row.get("source_manifest_validation") != "PASS"
        ):
            raise PrepareBatchError(
                f"Manifest item {index} has invalid task/spec identity: {path}"
            )
        item_commit = str(row.get("target_commit", "") or "")
        if item_commit != commit:
            raise PrepareBatchError(f"Manifest item {task_id} target commit mismatch")
        seen.add(task_id)
        items.append(
            PrepareBatchItem(
                task_id=task_id,
                target_commit=item_commit,
                subject_id=str(row.get("subject_id", "") or ""),
                bundle_hash=str(row.get("bundle_hash", "") or ""),
                primary_hash=str(row.get("primary_hash", "") or ""),
                supplement_spec=spec.resolve(),
                supplement_sha256=str(row.get("spec_sha256", "") or ""),
            )
        )
    counts = payload.get("counts")
    declared = counts.get("unique_tasks") if isinstance(counts, Mapping) else None
    expected = payload.get("expected_unique_count")
    if declared != len(items) or expected != len(items):
        raise PrepareBatchError(
            f"Consolidated manifest count mismatch: declared={declared} "
            f"expected={expected} actual={len(items)}"
        )
    return commit, tuple(items)


def _assert_item_subject(item: PrepareBatchItem, subject: SubjectBundle) -> None:
    expected = {
        "subject_id": subject.subject_id,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
    }
    actual = {
        "subject_id": item.subject_id,
        "bundle_hash": item.bundle_hash,
        "primary_hash": item.primary_hash,
    }
    if actual != expected or item.target_commit != subject.source_commit:
        raise PrepareBatchError(f"{item.task_id}: manifest/current subject mismatch")


def _validate_existing_pack(
    *,
    pack_dir: Path,
    item: PrepareBatchItem,
    subject: SubjectBundle,
    catalog: TaskCatalog,
    receipt_path: Path,
    receipt_hash: str,
    checkout: Path,
    attempt: int,
) -> dict[str, Any] | None:
    metadata_path = pack_dir / "mat_exact_subject.json"
    if not pack_dir.exists():
        return None
    if not pack_dir.is_dir() or not metadata_path.is_file():
        raise PrepareBatchError(f"{item.task_id}: existing review pack is partial")
    try:
        metadata = _read_pack_json(metadata_path)
    except ApplyError as exc:
        raise PrepareBatchError(f"{item.task_id}: existing pack metadata is invalid: {exc}") from exc
    bindings = {
        "schema": "mat.catalog.exact-review-pack.v1",
        "task_id": item.task_id,
        "attempt": attempt,
        "commit": catalog.mat_commit,
        "build_receipt_mode": "reused_prebuilt",
        "build_checkout": str(checkout),
        "prebuilt_exact_build_receipt_source": str(receipt_path),
        "prebuilt_exact_build_receipt_source_hash": receipt_hash,
        "review_supplement_spec_file": str(item.supplement_spec),
        "review_supplement_spec_hash": item.supplement_sha256,
    }
    mismatches = {
        key: {"expected": value, "actual": metadata.get(key)}
        for key, value in bindings.items()
        if metadata.get(key) != value
    }
    if mismatches:
        raise PrepareBatchError(
            f"{item.task_id}: existing pack binding mismatch: {mismatches}"
        )
    result_path = Path(
        str(metadata.get("expected_review_result_file", "") or "")
    ).expanduser()
    try:
        validator = _validate_pack if result_path.is_file() else _validate_prepare_complete_pack
        validator(
            pack_dir=pack_dir,
            metadata=metadata,
            subject=subject,
            catalog=catalog,
        )
    except ApplyError as exc:
        raise PrepareBatchError(
            f"{item.task_id}: existing pack failed complete revalidation: {exc}"
        ) from exc
    return {
        "task_id": item.task_id,
        "status": "skipped_existing",
        "pack_dir": str(pack_dir),
        "metadata_file": str(metadata_path),
    }


def prepare_review_batch(
    *,
    manifest_path: Path,
    exact_build_root: Path,
    output_root: Path,
    workspace_root: Path,
    runtime_root: Path,
    checkout: Path,
    attempt: int = 1,
    skip_existing: bool = True,
    campaign_id: str = "current_exact_review_prepare_batch",
) -> dict[str, Any]:
    if attempt <= 0:
        raise PrepareBatchError("attempt must be positive")
    build_root = checkout.expanduser().resolve()
    builds = exact_build_root.expanduser()
    output = output_root.expanduser().resolve()
    if not builds.is_absolute():
        raise PrepareBatchError("exact_build_root must be absolute")
    builds = builds.resolve()
    if output == build_root or output.is_relative_to(build_root):
        raise PrepareBatchError("output_root must be outside the clean checkout")
    commit, items = load_prepare_batch_manifest(manifest_path)
    catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    mat_repo = (workspace_root / "MAT3280-formalization-output").resolve()
    if commit != catalog.mat_commit:
        raise PrepareBatchError("Consolidated manifest commit does not match the catalog")
    if _git_text(mat_repo, "rev-parse", "origin/main") != commit:
        raise PrepareBatchError("MAT origin/main does not match the consolidated manifest")
    if _git_text(build_root, "rev-parse", "HEAD") != commit:
        raise PrepareBatchError("Clean checkout HEAD does not match the consolidated manifest")
    if _git_text(build_root, "status", "--porcelain", "--untracked-files=all"):
        raise PrepareBatchError("Build checkout is not clean")

    primary_modules, owned_modules = catalog_owned_build_modules(
        catalog, [item.task_id for item in items]
    )
    prepared: list[tuple[PrepareBatchItem, SubjectBundle, Path, str, Path]] = []
    skipped: list[dict[str, Any]] = []
    for item in items:
        if not item.supplement_spec.is_file():
            raise PrepareBatchError(
                f"{item.task_id}: supplement spec is missing: {item.supplement_spec}"
            )
        if sha256_file(item.supplement_spec) != item.supplement_sha256:
            raise PrepareBatchError(f"{item.task_id}: supplement spec hash mismatch")
        subject = _catalog_subject(catalog, task_id=item.task_id, mat_repo=mat_repo)
        _assert_item_subject(item, subject)
        receipt = (builds / item.task_id / "exact_mat_build_receipt_v1.json").resolve()
        if not receipt.is_file():
            raise PrepareBatchError(f"{item.task_id}: central exact-build receipt is missing")
        try:
            validate_current_exact_build_receipt(
                receipt,
                subject=subject,
                primary_module=primary_modules[item.task_id],
                task_modules=owned_modules[item.task_id],
                commit=commit,
                checkout=build_root,
            )
        except ExactBuildBatchError as exc:
            raise PrepareBatchError(
                f"{item.task_id}: central exact-build receipt is invalid: {exc}"
            ) from exc
        receipt_hash = sha256_file(receipt)
        pack_dir = output / item.task_id
        existing = _validate_existing_pack(
            pack_dir=pack_dir,
            item=item,
            subject=subject,
            catalog=catalog,
            receipt_path=receipt,
            receipt_hash=receipt_hash,
            checkout=build_root,
            attempt=attempt,
        )
        if existing is not None:
            if not skip_existing:
                raise PrepareBatchError(
                    f"{item.task_id}: immutable review pack already exists"
                )
            skipped.append(existing)
        else:
            prepared.append((item, subject, receipt, receipt_hash, pack_dir))

    emitted: list[dict[str, Any]] = []
    for item, _subject, receipt, receipt_hash, pack_dir in prepared:
        if pack_dir.exists():
            raise PrepareBatchError(
                f"{item.task_id}: review pack appeared concurrently; refusing overwrite"
            )
        if sha256_file(item.supplement_spec) != item.supplement_sha256:
            raise PrepareBatchError(
                f"{item.task_id}: supplement spec changed before preparation"
            )
        if sha256_file(receipt) != receipt_hash:
            raise PrepareBatchError(
                f"{item.task_id}: central exact-build receipt changed before preparation"
            )
        try:
            result = prepare_review(
                task_id=item.task_id,
                attempt=attempt,
                pack_dir=pack_dir,
                workspace_root=workspace_root,
                runtime_root=runtime_root,
                build_root=build_root,
                review_supplement_spec=item.supplement_spec,
                prebuilt_exact_build_receipt=receipt,
                campaign_id=campaign_id,
            )
        except PrepareError as exc:
            raise PrepareBatchError(f"{item.task_id}: prepare failed: {exc}") from exc
        emitted.append(
            {
                "task_id": item.task_id,
                "status": "prepared",
                "pack_dir": str(pack_dir),
                "metadata_file": result["metadata_file"],
            }
        )
    tasks = sorted([*skipped, *emitted], key=lambda row: str(row["task_id"]))
    return {
        "status": "all_existing" if not prepared else "prepared",
        "target_commit": commit,
        "requested": len(items),
        "prepared": len(emitted),
        "skipped_existing": len(skipped),
        "tasks": tasks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare exact-current review packs from a consolidated supplement manifest"
    )
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--exact-build-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--checkout", type=Path, required=True)
    parser.add_argument("--workspace-root", type=Path, default=REPO_ROOT.parent)
    parser.add_argument("--runtime-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--attempt", type=int, default=1)
    parser.add_argument("--campaign-id", default="current_exact_review_prepare_batch")
    parser.add_argument("--no-skip-existing", action="store_true")
    args = parser.parse_args()
    result = prepare_review_batch(
        manifest_path=args.manifest,
        exact_build_root=args.exact_build_root,
        output_root=args.output_root,
        workspace_root=args.workspace_root.resolve(),
        runtime_root=args.runtime_root.resolve(),
        checkout=args.checkout.resolve(),
        attempt=args.attempt,
        skip_existing=not args.no_skip_existing,
        campaign_id=args.campaign_id,
    )
    print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except PrepareBatchError as exc:
        print(f"MAT_CATALOG_REVIEW_PREPARE_BATCH_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
