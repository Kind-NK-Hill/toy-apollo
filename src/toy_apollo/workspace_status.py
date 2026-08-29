from __future__ import annotations

import ast
import gzip
import json
import os
import re
import sqlite3
import stat
import subprocess
import tempfile
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping

from .state_migration import rebuild_invariants
from .state_snapshot import build_dataset_payload
from .state_store import WorkspaceStateStore, sha256_json
from .task_catalog import TaskCatalog, load_catalog


STATUS_SCHEMA = "toy-apollo.workspace-status.v1"
FILE_INVENTORY_SCHEMA = "toy-apollo.workspace-file-inventory.v1"
BASELINE_SCHEMA = "toy-apollo.workspace-baseline.v1"


class WorkspaceStatusError(RuntimeError):
    """Raised when the workspace status projection cannot be built safely."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _json_value(raw: Any) -> Any:
    if isinstance(raw, str):
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return raw
    return raw


def _atomic_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(payload, handle, ensure_ascii=False, sort_keys=True, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def _atomic_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def load_workspace_policy(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise WorkspaceStatusError(f"Unable to read workspace policy {path}: {exc}") from exc
    if payload.get("schema_version") != "toy-apollo.workspace-inventory-policy.v1":
        raise WorkspaceStatusError(f"Unsupported workspace policy schema in {path}")
    if not isinstance(payload.get("entries"), dict):
        raise WorkspaceStatusError("Workspace policy entries must be an object")
    return payload


def _git(repo: Path, *args: str, check: bool = True) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repo), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise WorkspaceStatusError(
            f"Git command failed in {repo}: git {' '.join(args)}: {detail}"
        )
    return completed.stdout


def _git_text(repo: Path, *args: str, check: bool = True) -> str:
    return _git(repo, *args, check=check).decode("utf-8", errors="replace").strip()


def _git_paths(repo: Path, *args: str) -> list[str]:
    raw = _git(repo, *args)
    return sorted(
        item.decode("utf-8", errors="surrogateescape").replace("\\", "/")
        for item in raw.split(b"\0")
        if item
    )


def _group_top(paths: Iterable[str]) -> dict[str, int]:
    counts = Counter(path.split("/", 1)[0] for path in paths)
    return dict(sorted(counts.items(), key=lambda item: (-item[1], item[0].lower())))


def repository_status(repo: Path, *, include_file_sets: bool = False) -> dict[str, Any]:
    repo = repo.resolve()
    if not (repo / ".git").exists():
        raise WorkspaceStatusError(f"Not a Git repository or worktree: {repo}")
    tracked = set(_git_paths(repo, "ls-files", "-z"))
    unstaged = set(_git_paths(repo, "diff", "--name-only", "-z"))
    staged = set(_git_paths(repo, "diff", "--cached", "--name-only", "-z"))
    untracked = set(_git_paths(repo, "ls-files", "--others", "--exclude-standard", "-z"))
    branch = _git_text(repo, "branch", "--show-current", check=False)
    head = _git_text(repo, "rev-parse", "HEAD")
    upstream = _git_text(repo, "rev-parse", "--abbrev-ref", "@{upstream}", check=False)
    ahead = behind = None
    if upstream:
        raw_counts = _git_text(repo, "rev-list", "--left-right", "--count", f"HEAD...{upstream}")
        left, right = raw_counts.split()
        ahead, behind = int(left), int(right)
    changed = unstaged | staged | untracked
    payload: dict[str, Any] = {
        "path": str(repo),
        "branch": branch or None,
        "detached": not bool(branch),
        "head": head,
        "upstream": upstream or None,
        "ahead": ahead,
        "behind": behind,
        "dirty": bool(changed),
        "tracked_files": len(tracked),
        "unstaged_files": len(unstaged),
        "staged_files": len(staged),
        "untracked_files": len(untracked),
        "changed_by_top_path": _group_top(changed),
    }
    if include_file_sets:
        payload["_file_sets"] = {
            "tracked": tracked,
            "unstaged": unstaged,
            "staged": staged,
            "untracked": untracked,
        }
    return payload


def registered_worktrees(repositories: Iterable[Path]) -> list[dict[str, Any]]:
    worktrees: dict[str, dict[str, Any]] = {}
    for owner in repositories:
        lines = _git_text(owner, "worktree", "list", "--porcelain").splitlines()
        for line in lines:
            if not line.startswith("worktree "):
                continue
            path = Path(line.removeprefix("worktree ")).resolve()
            key = os.path.normcase(str(path))
            if key in worktrees:
                continue
            status = repository_status(path)
            status["owner_repository"] = str(owner.resolve())
            worktrees[key] = status
    return sorted(worktrees.values(), key=lambda row: row["path"].lower())


def _tree_metrics(path: Path, *, exclude_names: set[str]) -> dict[str, int]:
    if path.is_file():
        try:
            return {
                "files": 1,
                "bytes": path.stat().st_size,
                "metadata_unavailable": 0,
                "reparse_points": 0,
            }
        except OSError:
            return {"files": 1, "bytes": 0, "metadata_unavailable": 1, "reparse_points": 0}
    files = total_bytes = metadata_unavailable = reparse_points = 0
    stack = [path]
    while stack:
        directory = stack.pop()
        try:
            entries = list(os.scandir(directory))
        except OSError:
            metadata_unavailable += 1
            continue
        for entry in entries:
            if _is_reparse_point(entry):
                reparse_points += 1
                continue
            if entry.is_dir(follow_symlinks=False):
                if entry.name not in exclude_names:
                    stack.append(Path(entry.path))
                continue
            if not entry.is_file(follow_symlinks=False):
                continue
            files += 1
            try:
                total_bytes += entry.stat(follow_symlinks=False).st_size
            except OSError:
                metadata_unavailable += 1
    return {
        "files": files,
        "bytes": total_bytes,
        "metadata_unavailable": metadata_unavailable,
        "reparse_points": reparse_points,
    }


def _is_reparse_point(entry: os.DirEntry[str]) -> bool:
    if entry.is_symlink():
        return True
    try:
        attributes = getattr(entry.stat(follow_symlinks=False), "st_file_attributes", 0)
    except OSError:
        return False
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0))


def _analysis_child_classification(path: Path, *, registered: bool) -> dict[str, str]:
    name = path.name.casefold()
    if registered:
        return {
            "role": "registered_worktree",
            "authority": "candidate_only",
            "recoverability": "git_branch_or_detached_head_plus_workspace_baseline",
            "retention": "retain_until_deliberate_git_worktree_closeout",
        }
    if name in {"__pycache__", ".pytest_cache", ".repl_tmp", ".lake"}:
        return {
            "role": "generated_cache",
            "authority": "none",
            "recoverability": "reproducible_cache",
            "retention": "cleanup_candidate_after_explicit_confirmation",
        }
    if "sql_workspace" in name:
        return {
            "role": "linked_state_projection_workspace",
            "authority": "projection_only",
            "recoverability": "junction_targets_and_immutable_evidence",
            "retention": "retain_until_link_consumers_and_rebuild_purpose_are_confirmed",
        }
    if path.is_dir() and not any(path.iterdir()):
        return {
            "role": "empty_scratch",
            "authority": "none",
            "recoverability": "reproducible_or_empty",
            "retention": "cleanup_candidate_after_explicit_confirmation",
        }
    if path.is_dir() and (path / ".git").exists():
        return {
            "role": "unregistered_git_checkout",
            "authority": "reference_or_candidate_unverified",
            "recoverability": "git_metadata_present_but_registration_absent",
            "retention": "inspect_branch_and_dirty_state_before_archive_or_removal",
        }
    if path.is_file() and path.suffix.casefold() in {".py", ".ps1"}:
        return {
            "role": "analysis_tool",
            "authority": "none",
            "recoverability": "preserved_in_place_and_file_inventory",
            "retention": "retain_with_consuming_report_or_classify_for_archive",
        }
    if path.is_file() and path.suffix.casefold() in {".json", ".md", ".txt", ".csv"}:
        return {
            "role": "analysis_report_or_manifest",
            "authority": "evidence_input_unless_receipt_bound",
            "recoverability": "preserved_in_place_and_file_inventory",
            "retention": "retain_until_consumers_and_receipt_binding_are_known",
        }
    if path.is_file() and path.suffix.casefold() == ".lean":
        return {
            "role": "analysis_lean_probe",
            "authority": "candidate_only",
            "recoverability": "preserved_in_place_and_file_inventory",
            "retention": "retain_until_probe_outcome_is_recorded",
        }
    if any(token in name for token in ("fixture", "pytest", "test", "tmp")):
        return {
            "role": "test_or_analysis_fixture",
            "authority": "none",
            "recoverability": "expected_reproducible_fixture",
            "retention": "cleanup_candidate_after_reproducer_is_confirmed",
        }
    if any(
        token in name
        for token in ("review", "rebind", "bridge", "authority", "exact", "recovery", "receipt")
    ):
        return {
            "role": "analysis_evidence_workspace",
            "authority": "evidence_input_unless_receipt_bound",
            "recoverability": "preserved_in_place_and_workspace_baseline",
            "retention": "retain_until_immutable_evidence_destination_is_confirmed",
        }
    if any(token in name for token in ("kenneth", "dradar", "mathlib", "probability")):
        return {
            "role": "external_or_repository_analysis_checkout",
            "authority": "reference_only_unless_separately_bound",
            "recoverability": "inspect_origin_commit_or_source_manifest",
            "retention": "retain_until_reference_commit_and_consumers_are_indexed",
        }
    return {
        "role": "unclassified_analysis_child",
        "authority": "unknown",
        "recoverability": "preserved_in_place_and_workspace_baseline",
        "retention": "inspect_before_change",
    }


def analysis_tmp_inventory(
    *,
    workspace_root: Path,
    worktrees: Iterable[Mapping[str, Any]],
    exclude_names: Iterable[str],
) -> dict[str, Any]:
    root = workspace_root / "_analysis_tmp"
    registered = {
        os.path.normcase(str(Path(str(row["path"])).resolve())): row for row in worktrees
    }
    rows: list[dict[str, Any]] = []
    role_counts: Counter[str] = Counter()
    total_files = total_bytes = metadata_unavailable = reparse_points = 0
    if root.is_dir():
        for child in sorted(root.iterdir(), key=lambda item: item.name.casefold()):
            worktree = registered.get(os.path.normcase(str(child.resolve())))
            classification = _analysis_child_classification(
                child, registered=worktree is not None
            )
            metrics = _tree_metrics(child, exclude_names=set(exclude_names))
            row = {
                "name": child.name,
                "path": str(child.resolve()),
                "kind": "directory" if child.is_dir() else "file",
                "modified_at": datetime.fromtimestamp(
                    child.stat().st_mtime, timezone.utc
                ).isoformat(),
                **metrics,
                **classification,
                "registered_worktree": worktree is not None,
                "git_owner_repository": worktree.get("owner_repository") if worktree else None,
                "git_branch": worktree.get("branch") if worktree else None,
                "git_head": worktree.get("head") if worktree else None,
                "git_dirty": worktree.get("dirty") if worktree else None,
                "git_unstaged_files": worktree.get("unstaged_files") if worktree else None,
                "git_staged_files": worktree.get("staged_files") if worktree else None,
                "git_untracked_files": worktree.get("untracked_files") if worktree else None,
            }
            rows.append(row)
            role_counts[row["role"]] += 1
            total_files += metrics["files"]
            total_bytes += metrics["bytes"]
            metadata_unavailable += metrics["metadata_unavailable"]
            reparse_points += metrics["reparse_points"]
    return {
        "path": str(root / "INDEX.md"),
        "children": len(rows),
        "files": total_files,
        "bytes": total_bytes,
        "metadata_unavailable": metadata_unavailable,
        "reparse_points": reparse_points,
        "role_counts": dict(sorted(role_counts.items())),
        "rows": rows,
    }


def render_analysis_tmp_index(inventory: Mapping[str, Any]) -> str:
    lines = [
        "# `_analysis_tmp` Child Index",
        "",
        "> Generated by `python toy-apollo/tools/workspace_status.py --write`. Do not edit by hand.",
        "",
        "This index classifies each first-level child before any move or deletion.",
        "A registered worktree, evidence input, or unknown child is never a generic cleanup target.",
        "",
        "## Summary",
        "",
        f"- Children: `{inventory['children']}`",
        f"- Files outside excluded Git/cache directories: `{inventory['files']}`",
        f"- Bytes outside excluded Git/cache directories: `{inventory['bytes']}`",
        f"- Metadata-unavailable paths: `{inventory['metadata_unavailable']}`",
        f"- Symlink/reparse points recorded but not traversed: `{inventory['reparse_points']}`",
        f"- Roles: `{json.dumps(inventory['role_counts'], sort_keys=True)}`",
        "",
        "## Children",
        "",
        "| Child | Kind | Files | Bytes | Role | Authority | Worktree | Git state | Recoverability | Retention |",
        "|---|---|---:|---:|---|---|---:|---|---|---|",
    ]
    for row in inventory["rows"]:
        git_state = "—"
        if row["registered_worktree"]:
            git_state = (
                f"{row['git_branch'] or 'detached'}@{str(row['git_head'] or '')[:12]}; "
                f"dirty={row['git_dirty']}; U/S/?="
                f"{row['git_unstaged_files']}/{row['git_staged_files']}/{row['git_untracked_files']}"
            )
        values = [
            f"`{row['name']}`",
            row["kind"],
            row["files"],
            row["bytes"],
            row["role"],
            row["authority"],
            "yes" if row["registered_worktree"] else "no",
            git_state,
            row["recoverability"],
            row["retention"],
        ]
        lines.append("| " + " | ".join(_cell(value) for value in values) + " |")
    lines.append("")
    return "\n".join(lines)


def validate_policy_coverage(workspace_root: Path, policy: Mapping[str, Any]) -> dict[str, Any]:
    declared = set(policy["entries"])
    actual = {path.name for path in workspace_root.iterdir()}
    optional_generated = {
        name
        for name, entry in policy["entries"].items()
        if entry.get("edit_policy") == "generated"
    }
    return {
        "valid": not (actual - declared) and not ((declared - actual) - optional_generated),
        "unclassified_entries": sorted(actual - declared, key=str.lower),
        "missing_declared_entries": sorted((declared - actual) - optional_generated, key=str.lower),
        "optional_generated_absent": sorted((declared - actual) & optional_generated, key=str.lower),
        "actual_entry_count": len(actual),
        "declared_entry_count": len(declared),
    }


def _table_counts(connection: sqlite3.Connection) -> dict[str, int]:
    names = [
        row[0]
        for row in connection.execute(
            "SELECT name FROM sqlite_master "
            "WHERE type='table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
        )
    ]
    return {name: int(connection.execute(f'SELECT COUNT(*) FROM "{name}"').fetchone()[0]) for name in names}


def _path_health(connection: sqlite3.Connection) -> dict[str, dict[str, int]]:
    columns = (
        ("reviews", "evidence_path"),
        ("transformations", "evidence_path"),
        ("authority_bindings", "decision_path"),
        ("authority_bindings", "evidence_path"),
        ("runs", "artifact_path"),
        ("imports", "source_path"),
        ("state_events", "evidence_path"),
    )
    result: dict[str, dict[str, int]] = {}
    for table, column in columns:
        values = [
            str(row[0])
            for row in connection.execute(
                f"SELECT {column} FROM {table} WHERE {column} <> ''"
            )
        ]
        present = sum(Path(value).exists() for value in values)
        result[f"{table}.{column}"] = {
            "nonempty": len(values),
            "present": present,
            "missing": len(values) - present,
        }
    return result


def database_health(
    store: WorkspaceStateStore,
    *,
    catalog: TaskCatalog,
    workspace_root: Path,
    compare_latest_rebuild: bool = False,
) -> dict[str, Any]:
    store.assert_integrity()
    with store._connection(write=False) as connection:
        quick_check = [str(row[0]) for row in connection.execute("PRAGMA quick_check")]
        foreign_key_errors = len(connection.execute("PRAGMA foreign_key_check").fetchall())
        counts = _table_counts(connection)
        meta = {
            str(row["key"]): str(row["value"])
            for row in connection.execute("SELECT key, value FROM meta ORDER BY key")
        }
        anomalies = {
            "noncanonical_verdicts": [
                dict(row)
                for row in connection.execute(
                    "SELECT review_id, task_id, verdict, evidence_path, authority_eligible "
                    "FROM reviews WHERE lower(verdict) NOT IN ('pass','fail','inconclusive','partial')"
                )
            ],
            "noncanonical_phase2_statuses": [
                dict(row)
                for row in connection.execute(
                    "SELECT review_id, task_id, phase2_status, evidence_path, authority_eligible "
                    "FROM reviews WHERE phase2_status <> '' AND lower(phase2_status) NOT IN "
                    "('pass','fail','blocked','allowed_exception','inconclusive',"
                    "'failed_semantic_review','semantic_review_passed','covered')"
                )
            ],
        }
        path_health = _path_health(connection)
    invariants = rebuild_invariants(store, catalog)
    stat = store.path.stat()
    payload: dict[str, Any] = {
        "path": str(store.path),
        "bytes": stat.st_size,
        "modified_at": datetime.fromtimestamp(stat.st_mtime, timezone.utc).isoformat(),
        "quick_check": quick_check,
        "foreign_key_error_count": foreign_key_errors,
        "meta": meta,
        "table_counts": counts,
        "path_health": path_health,
        "anomalies": anomalies,
        "invariants": invariants,
        "latest_rebuild_comparison": None,
    }
    if compare_latest_rebuild:
        candidates = sorted(
            store.path.parent.glob(".state.rebuild-*.sqlite3"),
            key=lambda path: path.stat().st_mtime,
            reverse=True,
        )
        if candidates:
            rebuilt = WorkspaceStateStore(candidates[0])
            rebuilt.assert_integrity()
            with rebuilt._connection(write=False) as connection:
                rebuilt_counts = _table_counts(connection)
            live_dataset = build_dataset_payload(
                store, invariants=invariants, workspace_root=workspace_root
            )
            rebuilt_invariants = rebuild_invariants(rebuilt, catalog)
            rebuilt_dataset = build_dataset_payload(
                rebuilt, invariants=rebuilt_invariants, workspace_root=workspace_root
            )
            live_hash = sha256_json(live_dataset)
            rebuilt_hash = sha256_json(rebuilt_dataset)
            payload["latest_rebuild_comparison"] = {
                "path": str(candidates[0]),
                "modified_at": datetime.fromtimestamp(
                    candidates[0].stat().st_mtime, timezone.utc
                ).isoformat(),
                "table_counts_equal": counts == rebuilt_counts,
                "stable_dataset_equal": live_hash == rebuilt_hash,
                "live_dataset_id": live_hash,
                "rebuilt_dataset_id": rebuilt_hash,
                "rebuilt_all_required_pass": bool(rebuilt_invariants.get("all_required_pass")),
            }
    return payload


def task_status_rows(store: WorkspaceStateStore, catalog: TaskCatalog) -> list[dict[str, Any]]:
    worklist = {row["task_id"]: row for row in store.worklist()}
    with store._connection(write=False) as connection:
        rows = connection.execute(
            """
            WITH compatible AS (
                SELECT r.task_id, MAX(m.prompt_version) AS prompt_version
                FROM reviews r
                JOIN review_metadata m ON m.review_id = r.review_id
                WHERE lower(r.verdict) = 'pass'
                  AND lower(COALESCE(r.phase2_status, '')) IN ('', 'pass')
                  AND m.prompt_version IN (9, 10, 11) AND m.rubric_version = 9
                GROUP BY r.task_id
            ), eligible AS (
                SELECT DISTINCT task_id FROM reviews
                WHERE lower(verdict) = 'pass' AND phase2_status = 'pass'
                  AND authority_eligible = 1
            ), direct AS (
                SELECT DISTINCT h.task_id
                FROM task_heads h
                JOIN subjects current ON current.subject_id = h.subject_id
                JOIN reviews r ON r.task_id = h.task_id
                JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
                JOIN review_metadata m ON m.review_id = r.review_id
                WHERE h.role = 'mat_main' AND h.freshness IN ('fresh', 'local')
                  AND reviewed.bundle_hash = current.bundle_hash
                  AND lower(r.verdict) = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND m.prompt_version IN (9, 10, 11) AND m.rubric_version = 9
            ), transformed AS (
                SELECT DISTINCT h.task_id
                FROM task_heads h
                JOIN subjects current ON current.subject_id = h.subject_id
                JOIN transformations t ON t.target_subject_id = current.subject_id
                JOIN reviews r ON r.subject_id = t.source_subject_id
                JOIN review_metadata m ON m.review_id = r.review_id
                WHERE h.role = 'mat_main' AND h.freshness IN ('fresh', 'local')
                  AND t.mechanical_status = 'pass'
                  AND t.build_status IN ('pass', 'not_required')
                  AND lower(r.verdict) = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND m.prompt_version IN (9, 10, 11) AND m.rubric_version = 9
            ), typed AS (
                SELECT DISTINCT h.task_id
                FROM task_heads h
                JOIN valid_authority_bindings b ON b.target_subject_id = h.subject_id
                WHERE h.role = 'mat_main' AND h.freshness IN ('fresh', 'local')
            )
            SELECT c.task_id, c.family_id, c.chapter, c.task_kind, c.primary_path,
                   h.freshness AS mat_freshness, s.source_commit AS mat_commit,
                   s.bundle_hash AS mat_bundle_hash,
                   compatible.prompt_version AS compatible_prompt_version,
                   CASE WHEN eligible.task_id IS NULL THEN 0 ELSE 1 END AS authority_eligible_pass,
                   CASE WHEN direct.task_id IS NULL THEN 0 ELSE 1 END AS direct_review,
                   CASE WHEN transformed.task_id IS NULL THEN 0 ELSE 1 END AS transformed_review,
                   CASE WHEN typed.task_id IS NULL THEN 0 ELSE 1 END AS typed_authority
            FROM catalog_tasks c
            LEFT JOIN task_heads h ON h.task_id = c.task_id AND h.role = 'mat_main'
            LEFT JOIN subjects s ON s.subject_id = h.subject_id
            LEFT JOIN compatible ON compatible.task_id = c.task_id
            LEFT JOIN eligible ON eligible.task_id = c.task_id
            LEFT JOIN direct ON direct.task_id = c.task_id
            LEFT JOIN transformed ON transformed.task_id = c.task_id
            LEFT JOIN typed ON typed.task_id = c.task_id
            WHERE c.catalog_id = ?
            ORDER BY c.chapter, c.task_id
            """,
            (catalog.catalog_id,),
        ).fetchall()
    result: list[dict[str, Any]] = []
    for raw in rows:
        row = dict(raw)
        if row.pop("direct_review"):
            coverage = "direct_review"
        elif row.pop("transformed_review"):
            coverage = "validated_transformation"
        elif row.get("typed_authority"):
            coverage = "typed_evidence_bridge"
        else:
            coverage = "missing"
        maintenance = worklist.get(str(row["task_id"]), {})
        row.update(
            {
                "compatible_pass": row["compatible_prompt_version"] is not None,
                "authority_eligible_pass": bool(row["authority_eligible_pass"]),
                "typed_authority": bool(row["typed_authority"]),
                "current_mat_coverage": coverage,
                "candidate_maintenance_actions": list(maintenance.get("actions", [])),
                "active_run_count": len(maintenance.get("active_runs", [])),
            }
        )
        result.append(row)
    return result


def _python_purpose(path: Path, *, role: str) -> tuple[str, str]:
    try:
        source = path.read_text(encoding="utf-8")
        tree = ast.parse(source)
    except (OSError, UnicodeDecodeError, SyntaxError):
        return (f"{role} Python module {path.stem}.", "path_policy")
    doc = ast.get_docstring(tree, clean=True)
    declarations = [
        node.name
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
    ]
    if doc:
        summary = doc.strip().splitlines()[0].strip()
        return (summary, "module_docstring")
    if declarations:
        names = ", ".join(declarations[:8])
        suffix = " …" if len(declarations) > 8 else ""
        return (f"{role} Python module; declares {names}{suffix}.", "python_declarations")
    return (f"{role} Python module {path.stem}.", "path_policy")


def _markdown_purpose(path: Path, fallback: str) -> tuple[str, str]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            for _ in range(80):
                line = handle.readline()
                if not line:
                    break
                match = re.match(r"^#{1,3}\s+(.+?)\s*$", line)
                if match:
                    return (f"Document: {match.group(1)}.", "document_heading")
    except (OSError, UnicodeDecodeError):
        pass
    return fallback, "inherited_top_level_role"


def _catalog_module_by_basename(catalog: TaskCatalog) -> dict[str, Any]:
    # Production catalog ``basename`` values are extensionless task identities
    # (for example ``thm_1_1``), while inventory paths contain real filenames.
    # Index by the canonical catalog path filename so both primary and support
    # modules use the same filesystem-shaped interface.
    return {Path(module.path).name.casefold(): module for module in catalog.modules}


def infer_file_purpose(
    path: Path,
    *,
    relative: str,
    top_entry: Mapping[str, Any],
    semantic: bool,
    catalog_modules: Mapping[str, Any],
) -> tuple[str, str]:
    fallback = str(top_entry["description"])
    suffix = path.suffix.lower()
    normalized = relative.replace("\\", "/")
    if not semantic:
        return fallback, "inherited_top_level_role"
    if suffix == ".py":
        if "/tests/" in f"/{normalized}" or normalized.startswith("toy-apollo/tests/"):
            return _python_purpose(path, role="Test")
        if "/tools/" in f"/{normalized}" or normalized.startswith("toy-apollo/tools/"):
            return _python_purpose(path, role="Operator tool")
        return _python_purpose(path, role="Runtime")
    if suffix == ".lean":
        module = catalog_modules.get(path.name.casefold())
        if module is not None:
            if module.module_role == "primary":
                return (
                    f"Task Parent for {module.owner_task_id}; catalog primary Lean module.",
                    "task_catalog",
                )
            if module.module_role == "owned_support":
                return (
                    f"Proof-Layer Support owned by {module.owner_task_id}.",
                    "task_catalog",
                )
            return ("Shared Support Lean module used across task families.", "task_catalog")
        return (f"Lean module {path.stem}; role inherited from {top_entry['role']}.", "path_policy")
    if suffix in {".md", ".markdown"}:
        return _markdown_purpose(path, fallback)
    if suffix == ".tex":
        return ("Textbook Source extraction used to define task statements and proof routes.", "path_policy")
    try:
        file_size = path.stat().st_size
    except OSError:
        file_size = None
    if suffix == ".json" and file_size is not None and file_size <= 512_000:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            return fallback, "inherited_top_level_role"
        if isinstance(payload, dict):
            schema = payload.get("schema_version", payload.get("schema"))
            if schema:
                return (f"JSON document using schema {schema}.", "json_schema")
            keys = ", ".join(list(payload)[:6])
            return (f"JSON data keyed by {keys}.", "json_keys")
    return fallback, "inherited_top_level_role"


def _iter_workspace_files(
    workspace_root: Path, *, exclude_names: set[str], excluded: Counter[str]
) -> Iterator[Path]:
    stack = [workspace_root]
    while stack:
        directory = stack.pop()
        try:
            entries = list(os.scandir(directory))
        except OSError:
            continue
        for entry in entries:
            if _is_reparse_point(entry):
                excluded["symlink_or_reparse_point"] += 1
                continue
            if entry.is_dir(follow_symlinks=False):
                if entry.name in exclude_names:
                    excluded[entry.name] += 1
                else:
                    stack.append(Path(entry.path))
            elif entry.is_file(follow_symlinks=False):
                yield Path(entry.path)


def write_file_inventory(
    *,
    workspace_root: Path,
    output_path: Path,
    policy: Mapping[str, Any],
    catalog: TaskCatalog,
    repository_file_sets: Mapping[str, Mapping[str, set[str]]],
) -> dict[str, Any]:
    exclude_names = set(policy["inventory"].get("exclude_directory_names", []))
    semantic_roots = set(policy["inventory"].get("semantic_inspection_roots", []))
    catalog_modules = _catalog_module_by_basename(catalog)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    excluded: Counter[str] = Counter()
    by_top: Counter[str] = Counter()
    by_role: Counter[str] = Counter()
    purpose_sources: Counter[str] = Counter()
    total_bytes = 0
    count = 0
    metadata_unavailable = 0
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{output_path.name}.", suffix=".tmp", dir=output_path.parent
    )
    os.close(descriptor)
    temporary = Path(temporary_name)
    try:
        with gzip.open(temporary, "wt", encoding="utf-8", newline="\n") as handle:
            header = {
                "schema_version": FILE_INVENTORY_SCHEMA,
                "record_type": "header",
                "generated_at": utc_now(),
                "workspace_root": str(workspace_root),
            }
            handle.write(json.dumps(header, ensure_ascii=False, sort_keys=True) + "\n")
            for path in _iter_workspace_files(
                workspace_root, exclude_names=exclude_names, excluded=excluded
            ):
                if path == temporary:
                    continue
                relative = path.relative_to(workspace_root).as_posix()
                if relative == output_path.relative_to(workspace_root).as_posix():
                    continue
                top = relative.split("/", 1)[0]
                top_entry = policy["entries"].get(top)
                if top_entry is None:
                    top_entry = {
                        "role": "unclassified",
                        "description": "Unclassified workspace file.",
                        "authority": "unknown",
                        "edit_policy": "inspect_before_change",
                        "lifecycle": "unknown",
                    }
                semantic = top in semantic_roots
                purpose, purpose_source = infer_file_purpose(
                    path,
                    relative=relative,
                    top_entry=top_entry,
                    semantic=semantic,
                    catalog_modules=catalog_modules,
                )
                repo_name = top if top in repository_file_sets else None
                git_state = "outside_git"
                if repo_name:
                    repo_relative = relative.split("/", 1)[1] if "/" in relative else ""
                    sets = repository_file_sets[repo_name]
                    if repo_relative in sets["untracked"]:
                        git_state = "untracked"
                    elif repo_relative in sets["staged"] and repo_relative in sets["unstaged"]:
                        git_state = "staged_and_unstaged"
                    elif repo_relative in sets["staged"]:
                        git_state = "staged"
                    elif repo_relative in sets["unstaged"]:
                        git_state = "modified"
                    elif repo_relative in sets["tracked"]:
                        git_state = "tracked_clean"
                    else:
                        git_state = "ignored_or_nested"
                try:
                    stat = path.stat()
                    file_bytes: int | None = stat.st_size
                    modified_at: str | None = datetime.fromtimestamp(
                        stat.st_mtime, timezone.utc
                    ).isoformat()
                except OSError:
                    file_bytes = None
                    modified_at = None
                    metadata_unavailable += 1
                record = {
                    "record_type": "file",
                    "path": relative,
                    "top_level": top,
                    "bytes": file_bytes,
                    "modified_at": modified_at,
                    "role": top_entry["role"],
                    "authority": top_entry["authority"],
                    "edit_policy": top_entry["edit_policy"],
                    "lifecycle": top_entry["lifecycle"],
                    "purpose": purpose,
                    "purpose_source": purpose_source,
                    "repository": repo_name,
                    "git_state": git_state,
                }
                handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
                count += 1
                total_bytes += file_bytes or 0
                by_top[top] += 1
                by_role[str(top_entry["role"])] += 1
                purpose_sources[purpose_source] += 1
        os.replace(temporary, output_path)
    finally:
        temporary.unlink(missing_ok=True)
    return {
        "path": str(output_path),
        "schema_version": FILE_INVENTORY_SCHEMA,
        "files": count,
        "bytes": total_bytes,
        "compressed_bytes": output_path.stat().st_size,
        "metadata_unavailable": metadata_unavailable,
        "by_top_level": dict(sorted(by_top.items(), key=lambda item: (-item[1], item[0].lower()))),
        "by_role": dict(sorted(by_role.items())),
        "purpose_sources": dict(sorted(purpose_sources.items())),
        "excluded_directory_instances": dict(sorted(excluded.items())),
    }


def _public_repository_status(status: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in status.items() if key != "_file_sets"}


def build_workspace_status(
    *,
    workspace_root: Path,
    runtime_root: Path,
    policy_path: Path,
    compare_latest_rebuild: bool = False,
) -> tuple[dict[str, Any], dict[str, Mapping[str, set[str]]]]:
    workspace_root = workspace_root.resolve()
    runtime_root = runtime_root.resolve()
    policy = load_workspace_policy(policy_path.resolve())
    policy_coverage = validate_policy_coverage(workspace_root, policy)
    repositories = [workspace_root / relative for relative in policy["repositories"]]
    detailed_repositories: list[dict[str, Any]] = []
    repository_file_sets: dict[str, Mapping[str, set[str]]] = {}
    for relative, repo in zip(policy["repositories"], repositories):
        status = repository_status(repo, include_file_sets=True)
        repository_file_sets[relative] = status.pop("_file_sets")
        status["workspace_path"] = relative
        status["purpose"] = policy["entries"][relative]["description"]
        detailed_repositories.append(status)
    catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    state_path = workspace_root / str(policy["state_database"])
    store = WorkspaceStateStore(state_path)
    database = database_health(
        store,
        catalog=catalog,
        workspace_root=workspace_root,
        compare_latest_rebuild=compare_latest_rebuild,
    )
    tasks = task_status_rows(store, catalog)
    coverage_counts = Counter(row["current_mat_coverage"] for row in tasks)
    candidate_counts = Counter(
        action for row in tasks for action in row["candidate_maintenance_actions"]
    )
    entries = []
    for name, entry in policy["entries"].items():
        path = workspace_root / name
        entries.append(
            {
                "path": name,
                **entry,
                "exists": path.exists(),
                "modified_at": (
                    datetime.fromtimestamp(path.stat().st_mtime, timezone.utc).isoformat()
                    if path.exists()
                    else None
                ),
            }
        )
    worktrees = registered_worktrees(repositories)
    analysis_inventory = analysis_tmp_inventory(
        workspace_root=workspace_root,
        worktrees=worktrees,
        exclude_names=policy["inventory"].get("exclude_directory_names", []),
    )
    payload = {
        "schema_version": STATUS_SCHEMA,
        "generated_at": utc_now(),
        "workspace_root": str(workspace_root),
        "policy": str(policy_path.resolve()),
        "interpretation": {
            "catalog_completion": "Compatible modern PASS coverage over the fixed 452-task catalog.",
            "current_mat_coverage": "Exact current catalog-pinned MAT bundle coverage through direct review, validated transformation, or typed evidence bridge.",
            "typed_authority": "A typed author/review evidence binding; it is not itself a semantic review.",
            "candidate_maintenance": "Working-tree maintenance only; it is not the catalog completion denominator.",
        },
        "policy_coverage": policy_coverage,
        "database": database,
        "repositories": [_public_repository_status(row) for row in detailed_repositories],
        "worktrees": worktrees,
        "analysis_tmp": analysis_inventory,
        "workspace_entries": sorted(entries, key=lambda row: row["path"].lower()),
        "task_summary": {
            "catalog_tasks": len(tasks),
            "compatible_pass": sum(row["compatible_pass"] for row in tasks),
            "authority_eligible_pass": sum(row["authority_eligible_pass"] for row in tasks),
            "current_mat_coverage": dict(sorted(coverage_counts.items())),
            "typed_authority": sum(row["typed_authority"] for row in tasks),
            "candidate_maintenance_actions": dict(sorted(candidate_counts.items())),
        },
        "tasks": tasks,
        "file_inventory": None,
    }
    return payload, repository_file_sets


def _cell(value: Any) -> str:
    if value is None:
        return "—"
    if isinstance(value, bool):
        return "yes" if value else "no"
    if isinstance(value, list):
        value = ", ".join(str(item) for item in value) or "none"
    return str(value).replace("|", "\\|").replace("\n", " ")


def render_workspace_status(payload: Mapping[str, Any]) -> str:
    database = payload["database"]
    invariants = database["invariants"]
    summary = payload["task_summary"]
    rebuild = database.get("latest_rebuild_comparison")
    lines = [
        "# Formalization Current Status",
        "",
        f"Generated: `{payload['generated_at']}`",
        "",
        "> Generated report. Do not edit by hand. Refresh with "
        "`python toy-apollo/tools/workspace_status.py --write --compare-latest-rebuild`.",
        "",
        "## Interpretation",
        "",
        "Catalog completion, exact current-bundle coverage, typed authority, and candidate maintenance are separate dimensions.",
        "A non-empty worklist or dirty Git repository does not make a catalog task incomplete.",
        "",
        "## Executive status",
        "",
        f"- Catalog completion: **{'PASS' if invariants['all_required_pass'] else 'FAIL'}**",
        f"- Modern compatible PASS: `{summary['compatible_pass']}/{summary['catalog_tasks']}`",
        f"- Exact current MAT coverage: `{sum(summary['current_mat_coverage'].values()) - summary['current_mat_coverage'].get('missing', 0)}/{summary['catalog_tasks']}`",
        f"- Coverage routes: `{json.dumps(summary['current_mat_coverage'], sort_keys=True)}`",
        f"- Typed authority bindings: `{summary['typed_authority']}`",
        f"- Authority-eligible PASS tasks: `{summary['authority_eligible_pass']}`",
        f"- Workspace policy coverage: `{'PASS' if payload['policy_coverage']['valid'] else 'FAIL'}`",
        "",
        "## SQLite state",
        "",
        f"- File: `{database['path']}`",
        f"- Size: `{database['bytes']}` bytes; modified `{database['modified_at']}`",
        f"- Integrity: `quick_check={database['quick_check']}`, foreign-key errors `{database['foreign_key_error_count']}`",
        f"- Schema/model: `{database['meta'].get('schema_version')}/{database['meta'].get('state_model_version')}`",
        f"- Active catalog: `{database['meta'].get('active_catalog_id')}`",
    ]
    if rebuild:
        lines.extend(
            [
                f"- Latest check-only rebuild: `{rebuild['path']}`",
                f"- Rebuild equivalence: table counts `{'equal' if rebuild['table_counts_equal'] else 'DIFFER'}`; stable dataset `{'equal' if rebuild['stable_dataset_equal'] else 'DIFFER'}`",
                f"- Stable dataset ID: `{rebuild['live_dataset_id']}`",
            ]
        )
    lines.extend(["", "### SQLite path health", "", "| Reference | Present | Missing |", "|---|---:|---:|"])
    for name, health in database["path_health"].items():
        lines.append(f"| `{name}` | {health['present']} | {health['missing']} |")
    anomaly_count = sum(len(rows) for rows in database["anomalies"].values())
    lines.extend(
        [
            "",
            f"SQLite noncanonical-field anomalies: `{anomaly_count}`. These rows are historical and authority-ineligible; see `current.json` for exact paths.",
            "",
            "## Git repositories",
            "",
            "| Repository | Branch | HEAD | Tracked | Modified | Staged | Untracked | Ahead/behind |",
            "|---|---|---|---:|---:|---:|---:|---|",
        ]
    )
    for repo in payload["repositories"]:
        lines.append(
            "| `{workspace_path}` | {branch} | `{head}` | {tracked_files} | {unstaged_files} | "
            "{staged_files} | {untracked_files} | {ahead}/{behind} |".format(
                **{**repo, "head": repo["head"][:12]}
            )
        )
    lines.extend(
        [
            "",
            "## Registered worktrees",
            "",
            "| Worktree | Branch | Dirty | Modified | Staged | Untracked |",
            "|---|---|---:|---:|---:|---:|",
        ]
    )
    for worktree in payload["worktrees"]:
        lines.append(
            f"| `{worktree['path']}` | {_cell(worktree['branch'])} | {_cell(worktree['dirty'])} | "
            f"{worktree['unstaged_files']} | {worktree['staged_files']} | {worktree['untracked_files']} |"
        )
    lines.extend(
        [
            "",
            "## Workspace entries",
            "",
            "| Path | Role | Authority | Policy | Lifecycle | Actual purpose |",
            "|---|---|---|---|---|---|",
        ]
    )
    for entry in payload["workspace_entries"]:
        lines.append(
            f"| `{entry['path']}` | {_cell(entry['role'])} | {_cell(entry['authority'])} | "
            f"{_cell(entry['edit_policy'])} | {_cell(entry['lifecycle'])} | {_cell(entry['description'])} |"
        )
    inventory = payload.get("file_inventory")
    if inventory:
        lines.extend(
            [
                "",
                "## File inventory",
                "",
                f"- File: `{inventory['path']}`",
                f"- Files described: `{inventory['files']}`",
                f"- Compressed bytes: `{inventory['compressed_bytes']}`",
                f"- Purpose provenance: `{json.dumps(inventory['purpose_sources'], sort_keys=True)}`",
                f"- Excluded metadata/cache directory instances: `{json.dumps(inventory['excluded_directory_instances'], sort_keys=True)}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Catalog task status",
            "",
            "| Task | Ch. | Kind | Compatible PASS | Prompt | Authority-eligible PASS | Current MAT coverage | Typed authority | Candidate maintenance |",
            "|---|---:|---|---:|---:|---:|---|---:|---|",
        ]
    )
    for task in payload["tasks"]:
        lines.append(
            f"| `{task['task_id']}` | {task['chapter']} | {_cell(task['task_kind'])} | "
            f"{_cell(task['compatible_pass'])} | {_cell(task['compatible_prompt_version'])} | "
            f"{_cell(task['authority_eligible_pass'])} | {_cell(task['current_mat_coverage'])} | "
            f"{_cell(task['typed_authority'])} | {_cell(task['candidate_maintenance_actions'])} |"
        )
    lines.append("")
    return "\n".join(lines)


def write_workspace_outputs(
    *,
    payload: dict[str, Any],
    repository_file_sets: Mapping[str, Mapping[str, set[str]]],
    workspace_root: Path,
    runtime_root: Path,
    policy: Mapping[str, Any],
    output_dir: Path,
    markdown_path: Path,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    analysis_index_path = workspace_root / "_analysis_tmp" / "INDEX.md"
    _atomic_text(analysis_index_path, render_analysis_tmp_index(payload["analysis_tmp"]))
    catalog = load_catalog(workspace_root=workspace_root, runtime_root=runtime_root)
    inventory_path = output_dir / "file_inventory.jsonl.gz"
    payload["file_inventory"] = write_file_inventory(
        workspace_root=workspace_root,
        output_path=inventory_path,
        policy=policy,
        catalog=catalog,
        repository_file_sets=repository_file_sets,
    )
    current_json = output_dir / "current.json"
    _atomic_json(current_json, payload)
    _atomic_text(markdown_path, render_workspace_status(payload))
    return {
        "current_json": str(current_json),
        "current_markdown": str(markdown_path),
        "file_inventory": str(inventory_path),
        "analysis_tmp_index": str(analysis_index_path),
    }


def capture_workspace_baseline(
    *,
    workspace_root: Path,
    repositories: Iterable[Path],
    worktrees: Iterable[Mapping[str, Any]],
    output_root: Path,
) -> dict[str, Any]:
    captured_at = utc_now()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    target = output_root / "baselines" / stamp
    target.mkdir(parents=True, exist_ok=False)
    unique: dict[str, Path] = {}
    for path in repositories:
        unique[os.path.normcase(str(path.resolve()))] = path.resolve()
    for row in worktrees:
        path = Path(str(row["path"])).resolve()
        unique[os.path.normcase(str(path))] = path
    records = []
    for index, repo in enumerate(sorted(unique.values(), key=lambda path: str(path).lower()), start=1):
        relative = os.path.relpath(repo, workspace_root).replace("\\", "/")
        slug = re.sub(r"[^A-Za-z0-9_.-]+", "_", relative).strip("_") or "workspace"
        prefix = f"{index:02d}-{slug}"
        status = repository_status(repo)
        unstaged = _git(repo, "diff", "--binary", "--no-ext-diff")
        staged = _git(repo, "diff", "--cached", "--binary", "--no-ext-diff")
        patch_files: dict[str, str] = {}
        for label, raw in (("unstaged", unstaged), ("staged", staged)):
            if not raw:
                continue
            path = target / f"{prefix}-{label}.patch"
            path.write_bytes(raw)
            patch_files[label] = str(path.relative_to(output_root).as_posix())
        untracked = _git_paths(repo, "ls-files", "--others", "--exclude-standard", "-z")
        listing = target / f"{prefix}-untracked.jsonl.gz"
        with gzip.open(listing, "wt", encoding="utf-8", newline="\n") as handle:
            for item in untracked:
                path = repo / item
                try:
                    stat = path.stat()
                except OSError:
                    continue
                handle.write(
                    json.dumps(
                        {
                            "path": item,
                            "bytes": stat.st_size,
                            "modified_at": datetime.fromtimestamp(
                                stat.st_mtime, timezone.utc
                            ).isoformat(),
                            "content_preserved_in_place": True,
                        },
                        ensure_ascii=False,
                        sort_keys=True,
                    )
                    + "\n"
                )
        records.append(
            {
                "path": str(repo),
                "workspace_path": relative,
                "status": status,
                "tracked_patches": patch_files,
                "untracked_listing": str(listing.relative_to(output_root).as_posix()),
                "untracked_content_policy": "preserved_in_place_not_copied",
            }
        )
    manifest = {
        "schema_version": BASELINE_SCHEMA,
        "captured_at": captured_at,
        "workspace_root": str(workspace_root),
        "destructive_actions": [],
        "records": records,
    }
    manifest_path = target / "manifest.json"
    _atomic_json(manifest_path, manifest)
    return {"path": str(manifest_path), "repositories_and_worktrees": len(records)}
