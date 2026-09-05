"""Safe activation of a changed non-MAT catalog in an existing state database."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from .review_versions import profile_for_catalog
from .state_reconcile import discover_catalog_worktree_subjects
from .state_store import WorkspaceStateStore
from .task_catalog import TaskCatalog, validate_catalog


class CatalogSyncError(RuntimeError):
    pass


def sync_active_catalog(
    *,
    store: WorkspaceStateStore,
    catalog: TaskCatalog,
    workspace_root: Path,
    runtime_root: Path,
    check_only: bool = False,
) -> dict[str, Any]:
    """Persist one current catalog without manufacturing reviewed authority.

    The current worktree is recorded under ``<profile>_current``. Existing
    ``<profile>_reviewed`` heads survive only when their exact bundle remains
    current; changed bundles are marked stale. No current subject is promoted
    to a reviewed role by this operation.
    """

    check = validate_catalog(catalog)
    if not check.get("valid"):
        raise CatalogSyncError(f"Catalog validation failed: {check.get('errors', [])}")
    profile = profile_for_catalog(catalog)
    if profile == "mat":
        raise CatalogSyncError(
            "MAT catalog activation remains governed by state rebuild and exact MAT receipts."
        )
    current_role = f"{profile}_current"
    reviewed_role = f"{profile}_reviewed"
    current_subjects = discover_catalog_worktree_subjects(
        runtime_root,
        catalog=catalog,
        source_repo=profile,
        layout=profile,
    )
    expected = set(catalog.task_ids())
    if set(current_subjects) != expected:
        missing = sorted(expected - set(current_subjects))
        extra = sorted(set(current_subjects) - expected)
        raise CatalogSyncError(
            f"Current {profile} subjects do not match the catalog: missing={missing}, extra={extra}"
        )

    with store._connection(write=False) as connection:
        catalog_present = connection.execute(
            "SELECT 1 FROM catalog_versions WHERE catalog_id = ?",
            (catalog.catalog_id,),
        ).fetchone() is not None
        reviewed_rows = {
            str(row["task_id"]): {
                "bundle_hash": str(row["bundle_hash"]),
                "freshness": str(row["freshness"]),
            }
            for row in connection.execute(
                """
                SELECT h.task_id, h.freshness, s.bundle_hash
                FROM task_heads h
                JOIN subjects s ON s.subject_id = h.subject_id
                WHERE h.role = ?
                """,
                (reviewed_role,),
            ).fetchall()
        }
    preserved = sorted(
        task_id
        for task_id, row in reviewed_rows.items()
        if task_id in current_subjects
        and row["bundle_hash"] == current_subjects[task_id].bundle_hash
    )
    staled = sorted(set(reviewed_rows) - set(preserved))
    payload: dict[str, Any] = {
        "status": "check_only" if check_only else "synced",
        "profile": profile,
        "catalog_id": catalog.catalog_id,
        "catalog_was_present": catalog_present,
        "catalog_task_count": len(expected),
        "current_role": current_role,
        "reviewed_role": reviewed_role,
        "reviewed_exact_preserved": preserved,
        "reviewed_staled": staled,
    }
    if check_only:
        return payload

    with store.bulk_write():
        store.persist_catalog(catalog)
        for task_id, subject in current_subjects.items():
            store.upsert_subject(subject)
            store.set_task_head(
                task_id=task_id,
                role=current_role,
                subject_id=subject.subject_id,
                detail={
                    "catalog_id": catalog.catalog_id,
                    "repo": str(runtime_root.resolve()),
                    "working_tree": True,
                },
            )
        for task_id in staled:
            store.mark_task_head_freshness(
                task_id=task_id,
                role=reviewed_role,
                freshness="stale",
            )
    store.assert_integrity()
    payload["current_heads_written"] = len(current_subjects)
    return payload
