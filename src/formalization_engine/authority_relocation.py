"""Fail-closed Phase 5 relocation of review authority to unified subjects.

The legacy database is opened read-only and remains the authority for the
181/159/112 route partition.  Repository relocation receipts only prove an
exact subject move.  They never create reviews or change review metadata.
"""

from __future__ import annotations

import argparse
import json
import os
import sqlite3
import subprocess
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from .state_store import (
    SubjectBundle,
    SubjectFile,
    LEGACY_TRANSFORMATION_SCHEMA,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
    stable_absolute_path,
    utc_now,
)


BUILD_SCHEMA = "formalization-engine.unified-build-evidence.v2"
RELOCATION_SCHEMA = "formalization-engine.repository-relocation-receipt.v2"
TYPED_REBIND_SCHEMA = "formalization-engine.typed-authority-rebind-receipt.v2"
BATCH_SCHEMA = "formalization-engine.authority-relocation-batch.v2"
TRANSFORMATION_SCHEMA = "formalization-engine.transformation.v2"
BINDING_SCHEMA = "formalization-engine.typed-authority-binding.v2"
EXPECTED_ROUTE_COUNTS = {
    "direct_review": 181,
    "validated_transformation": 159,
    "typed_evidence_bridge": 112,
}
SUPPORTED_PROMPTS = (9, 10, 11)
SUPPORTED_RUBRIC = 9


class AuthorityRelocationError(RuntimeError):
    """Raised when relocation evidence cannot prove a closed-set migration."""


@dataclass(frozen=True)
class AuthorityRoute:
    task_id: str
    route: str
    old_subject: Mapping[str, Any]
    new_subject: Mapping[str, Any]
    relocation_source: Mapping[str, Any]
    authority: Mapping[str, Any]


def _read_only(path: Path) -> sqlite3.Connection:
    resolved = path.expanduser().resolve()
    if not resolved.is_file():
        raise AuthorityRelocationError(f"State database does not exist: {resolved}")
    connection = sqlite3.connect(f"file:{resolved.as_posix()}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    return connection


def _one(connection: sqlite3.Connection, query: str, parameters: Sequence[Any] = ()) -> sqlite3.Row:
    row = connection.execute(query, parameters).fetchone()
    if row is None:
        raise AuthorityRelocationError("Required database row is missing.")
    return row


def _active_catalog_id(connection: sqlite3.Connection) -> str:
    return str(_one(connection, "SELECT value FROM meta WHERE key = 'active_catalog_id'")[0])


def _subject_row(connection: sqlite3.Connection, subject_id: str) -> dict[str, Any]:
    return dict(_one(connection, "SELECT * FROM subjects WHERE subject_id = ?", (subject_id,)))


def _subject_manifest(row: Mapping[str, Any]) -> list[dict[str, Any]]:
    value = json.loads(str(row["manifest_json"]))
    if not isinstance(value, list) or not value:
        raise AuthorityRelocationError(f"Subject {row['subject_id']} has an invalid manifest.")
    return [dict(item) for item in value]


def _subject_snapshot(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "subject_id": str(row["subject_id"]),
        "task_id": str(row["task_id"]),
        "subject_kind": str(row["subject_kind"]),
        "source_repo": str(row["source_repo"]),
        "source_commit": str(row["source_commit"]),
        "layout": str(row["layout"]),
        "bundle_hash": str(row["bundle_hash"]),
        "primary_hash": str(row["primary_hash"]),
        "primary_path": str(row["primary_path"]),
        "manifest": _subject_manifest(row),
    }


def _bundle_from_row(row: Mapping[str, Any]) -> SubjectBundle:
    files = tuple(
        SubjectFile(
            path=str(item["path"]),
            content_sha256=str(item["content_sha256"]),
            git_blob_sha=str(item["git_blob_sha"]),
            size=int(item["size"]),
        )
        for item in _subject_manifest(row)
    )
    return SubjectBundle(
        subject_id=str(row["subject_id"]),
        task_id=str(row["task_id"]),
        subject_kind=str(row["subject_kind"]),
        source_repo=str(row["source_repo"]),
        source_commit=str(row["source_commit"]),
        layout=str(row["layout"]),
        bundle_hash=str(row["bundle_hash"]),
        primary_hash=str(row["primary_hash"]),
        primary_path=str(row["primary_path"]),
        files=files,
        parent_subject_id=str(row.get("parent_subject_id") or ""),
        created_at=str(row.get("created_at") or ""),
    )


def _assert_exact_subject_move(old: Mapping[str, Any], new: Mapping[str, Any]) -> None:
    fields = ("task_id", "bundle_hash", "primary_hash", "primary_path", "manifest_json")
    mismatches = [field for field in fields if str(old[field]) != str(new[field])]
    if mismatches:
        raise AuthorityRelocationError(
            f"Task {old['task_id']} is not a byte-exact repository move; mismatches: {mismatches}"
        )
    if str(new["source_repo"]).lower() != "probabilitytheoryformalization" or str(
        new["layout"]
    ).lower() != "unified":
        raise AuthorityRelocationError(f"Task {old['task_id']} target is not a unified subject.")


def _eligible_review_sql(alias: str = "r", metadata_alias: str = "m") -> str:
    prompts = ", ".join(str(value) for value in SUPPORTED_PROMPTS)
    return (
        f"{alias}.verdict = 'pass' AND {alias}.phase2_status = 'pass' "
        f"AND {alias}.authority_eligible = 1 "
        f"AND {metadata_alias}.prompt_version IN ({prompts}) "
        f"AND {metadata_alias}.rubric_version = {SUPPORTED_RUBRIC}"
    )


def _direct_candidates(connection: sqlite3.Connection, task_id: str, bundle_hash: str) -> list[dict[str, Any]]:
    rows = connection.execute(
        f"""
        SELECT r.*, m.prompt_version, m.rubric_version
        FROM reviews r
        JOIN review_metadata m ON m.review_id = r.review_id
        JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
        WHERE r.task_id = ? AND reviewed.bundle_hash = ? AND {_eligible_review_sql()}
        ORDER BY r.reviewed_at DESC, r.review_id
        """,
        (task_id, bundle_hash),
    ).fetchall()
    return [dict(row) for row in rows]


def _transformation_candidates(
    connection: sqlite3.Connection, task_id: str, bundle_hash: str
) -> list[dict[str, Any]]:
    rows = connection.execute(
        f"""
        SELECT t.transformation_id, t.source_subject_id, t.target_subject_id,
               t.transformation_kind, t.mechanical_status, t.build_status,
               t.evidence_path AS transformation_evidence_path,
               t.evidence_hash AS transformation_evidence_hash,
               r.review_id, r.reviewed_at, r.evidence_path AS review_evidence_path,
               r.evidence_hash AS review_evidence_hash,
               r.proof_class, r.completion_class, r.authority_scope,
               m.prompt_version, m.rubric_version
        FROM transformations t
        JOIN reviews r ON r.subject_id = t.source_subject_id AND r.task_id = t.task_id
        JOIN review_metadata m ON m.review_id = r.review_id
        JOIN subjects transformed ON transformed.subject_id = t.target_subject_id
        WHERE t.task_id = ? AND transformed.bundle_hash = ?
          AND t.mechanical_status = 'pass'
          AND t.build_status IN ('pass', 'not_required')
          AND t.transformation_kind <> 'verified_evidence_bridge'
          AND {_eligible_review_sql()}
        ORDER BY r.reviewed_at DESC, t.transformation_id, r.review_id
        """,
        (task_id, bundle_hash),
    ).fetchall()
    return [dict(row) for row in rows]


def _typed_candidates(connection: sqlite3.Connection, task_id: str, bundle_hash: str) -> list[dict[str, Any]]:
    rows = connection.execute(
        """
        SELECT b.*, t.transformation_kind, t.mechanical_status, t.build_status
        FROM valid_authority_bindings b
        JOIN transformations t ON t.transformation_id = b.transformation_id
        JOIN subjects bridged ON bridged.subject_id = b.target_subject_id
        WHERE b.task_id = ? AND bridged.bundle_hash = ?
        ORDER BY b.created_at DESC, b.binding_id
        """,
        (task_id, bundle_hash),
    ).fetchall()
    return [dict(row) for row in rows]


def plan_authority_routes(legacy_db: Path, target_db: Path) -> tuple[list[AuthorityRoute], dict[str, str]]:
    """Classify every catalog task from the immutable legacy state projection."""

    with _read_only(legacy_db) as legacy, _read_only(target_db) as target:
        legacy_catalog = _active_catalog_id(legacy)
        target_catalog = _active_catalog_id(target)
        legacy_heads = {
            str(row["task_id"]): str(row["subject_id"])
            for row in legacy.execute(
                """
                SELECT h.task_id, h.subject_id
                FROM task_heads h
                JOIN catalog_tasks c ON c.task_id = h.task_id AND c.catalog_id = ?
                WHERE h.role = 'mat_main' AND h.freshness IN ('fresh', 'local')
                """,
                (legacy_catalog,),
            )
        }
        target_heads = {
            str(row["task_id"]): str(row["subject_id"])
            for row in target.execute(
                """
                SELECT h.task_id, h.subject_id
                FROM task_heads h
                JOIN catalog_tasks c ON c.task_id = h.task_id AND c.catalog_id = ?
                WHERE h.role = 'unified_main' AND h.freshness IN ('fresh', 'local')
                """,
                (target_catalog,),
            )
        }
        if set(legacy_heads) != set(target_heads) or len(legacy_heads) != sum(EXPECTED_ROUTE_COUNTS.values()):
            raise AuthorityRelocationError(
                "Legacy and unified catalog head sets are not the same closed 452-task set."
            )

        routes: list[AuthorityRoute] = []
        for task_id in sorted(legacy_heads):
            old = _subject_row(legacy, legacy_heads[task_id])
            new = _subject_row(target, target_heads[task_id])
            _assert_exact_subject_move(old, new)
            direct = _direct_candidates(legacy, task_id, str(old["bundle_hash"]))
            transformed = _transformation_candidates(legacy, task_id, str(old["bundle_hash"]))
            typed = _typed_candidates(legacy, task_id, str(old["bundle_hash"]))
            present = [bool(direct), bool(transformed), bool(typed)]
            if sum(present) != 1:
                raise AuthorityRelocationError(
                    f"Task {task_id} has a non-disjoint authority classification {present}."
                )
            if direct:
                route, authority = "direct_review", direct[0]
                relocation_source = _subject_row(legacy, str(authority["subject_id"]))
            elif transformed:
                route, authority = "validated_transformation", transformed[0]
                relocation_source = _subject_row(legacy, str(authority["target_subject_id"]))
            else:
                route, authority = "typed_evidence_bridge", typed[0]
                relocation_source = _subject_row(legacy, str(authority["source_subject_id"]))
            if route != "typed_evidence_bridge":
                _assert_exact_subject_move(relocation_source, new)
            target_source = _subject_row(target, str(relocation_source["subject_id"]))
            if _subject_snapshot(target_source) != _subject_snapshot(relocation_source):
                raise AuthorityRelocationError(
                    f"Task {task_id} relocation source was not preserved in the target projection."
                )
            routes.append(
                AuthorityRoute(
                    task_id=task_id,
                    route=route,
                    old_subject=old,
                    new_subject=new,
                    relocation_source=relocation_source,
                    authority=authority,
                )
            )

        counts = Counter(route.route for route in routes)
        if dict(counts) != EXPECTED_ROUTE_COUNTS:
            raise AuthorityRelocationError(
                f"Authority route partition changed: {dict(counts)} != {EXPECTED_ROUTE_COUNTS}."
            )
        return routes, {"legacy": legacy_catalog, "target": target_catalog}


def _run_logged(command: Sequence[str], cwd: Path, log_path: Path) -> dict[str, Any]:
    started_at = utc_now()
    completed = subprocess.run(command, cwd=cwd, capture_output=True, check=False)
    completed_at = utc_now()
    payload = completed.stdout + (b"\n[stderr]\n" + completed.stderr if completed.stderr else b"")
    log_path.write_bytes(payload)
    return {
        "command": list(command),
        "started_at": started_at,
        "completed_at": completed_at,
        "exit_code": completed.returncode,
        "log_path": stable_absolute_path(log_path),
        "log_sha256": sha256_file(log_path),
    }


def _git(repo: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments], cwd=repo, capture_output=True, text=True, check=False
    )
    if result.returncode:
        raise AuthorityRelocationError(result.stderr.strip() or f"git {' '.join(arguments)} failed")
    return result.stdout.strip()


def create_build_evidence(repo: Path, target_commit: str, output_dir: Path) -> Path:
    """Run the fresh corpus/build gates and bind them to an unchanged Git tree."""

    repo = repo.expanduser().resolve()
    output_dir = output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=False)
    observed_head = _git(repo, "rev-parse", "HEAD")
    target_tree = _git(repo, "rev-parse", f"{target_commit}:ProbabilityTheory")
    head_tree = _git(repo, "rev-parse", "HEAD:ProbabilityTheory")
    path_status = _git(repo, "status", "--porcelain", "--untracked-files=all", "--", "ProbabilityTheory")
    diff = subprocess.run(
        ["git", "diff", "--exit-code", target_commit, "--", "ProbabilityTheory"],
        cwd=repo,
        capture_output=True,
        check=False,
    )
    if target_tree != head_tree or path_status or diff.returncode:
        raise AuthorityRelocationError(
            "ProbabilityTheory worktree is not exactly the pinned target tree; refusing build evidence."
        )
    corpus = _run_logged(
        [os.fspath(Path(os.sys.executable)), "tools/check_formal_corpus.py"],
        repo,
        output_dir / "formal-corpus-check.log",
    )
    build = _run_logged(["lake", "build"], repo, output_dir / "lake-build.log")
    if corpus["exit_code"] or build["exit_code"]:
        raise AuthorityRelocationError("Fresh corpus or Lake build gate failed.")
    evidence = {
        "schema": BUILD_SCHEMA,
        "created_at": utc_now(),
        "repository": stable_absolute_path(repo),
        "target_commit": target_commit,
        "observed_head": observed_head,
        "corpus_root": "ProbabilityTheory",
        "target_tree": target_tree,
        "observed_head_tree": head_tree,
        "target_tree_equals_observed_head_tree": True,
        "worktree_corpus_clean": True,
        "semantic_change": False,
        "checks": {"formal_corpus": corpus, "lake_build": build},
    }
    path = output_dir / "unified-build-evidence-v2.json"
    _write_json(path, evidence)
    return path


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def _validate_build_evidence(path: Path, target_commit: str) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != BUILD_SCHEMA or payload.get("target_commit") != target_commit:
        raise AuthorityRelocationError("Build evidence schema or target commit does not match.")
    if not payload.get("target_tree_equals_observed_head_tree") or not payload.get(
        "worktree_corpus_clean"
    ):
        raise AuthorityRelocationError("Build evidence does not prove an exact clean corpus tree.")
    checks = payload.get("checks", {})
    if set(checks) != {"formal_corpus", "lake_build"} or any(
        int(checks[name].get("exit_code", -1)) != 0 for name in checks
    ):
        raise AuthorityRelocationError("Build evidence does not contain two passing gates.")
    for check in checks.values():
        log = Path(str(check["log_path"]))
        if not log.is_file() or sha256_file(log) != str(check["log_sha256"]):
            raise AuthorityRelocationError("Build evidence log path/hash mismatch.")
    return payload


def _relocation_identity(source_id: str, target_id: str, kind: str) -> str:
    return sha256_json(
        {"schema": TRANSFORMATION_SCHEMA, "source": source_id, "target": target_id, "kind": kind}
    )


def _receipt_payload(
    route: AuthorityRoute,
    catalogs: Mapping[str, str],
    build_path: Path,
    build_hash: str,
    created_at: str,
) -> dict[str, Any]:
    old_snapshot = _subject_snapshot(route.old_subject)
    new_snapshot = _subject_snapshot(route.new_subject)
    typed = route.route == "typed_evidence_bridge"
    source_id = str(route.relocation_source["subject_id"])
    kind = "verified_evidence_bridge" if typed else "repository_relocation"
    return {
        "schema": TYPED_REBIND_SCHEMA if typed else RELOCATION_SCHEMA,
        "created_at": created_at,
        "task_id": route.task_id,
        "route": route.route,
        "catalogs": dict(catalogs),
        "old_current_subject": old_snapshot,
        "unified_target_subject": new_snapshot,
        "relocation_source_subject": _subject_snapshot(route.relocation_source),
        "byte_exact": {
            "bundle_hash_equal": True,
            "primary_hash_equal": True,
            "primary_path_equal": True,
            "manifest_equal": True,
        },
        "authority": dict(route.authority),
        "build_evidence": {"path": stable_absolute_path(build_path), "sha256": build_hash},
        "result": {
            "source_subject_id": source_id,
            "target_subject_id": str(route.new_subject["subject_id"]),
            "transformation_kind": kind,
            "transformation_id": _relocation_identity(source_id, str(route.new_subject["subject_id"]), kind),
        },
        "claims": {
            "repository_relocation_only": True,
            "semantic_review_created": False,
            "semantic_upgrade": False,
            "rubric_upgrade": False,
            "completion_class_upgrade": False,
            "authority_eligibility_upgrade": False,
        },
    }


def write_relocation_receipts(
    routes: Iterable[AuthorityRoute],
    catalogs: Mapping[str, str],
    build_evidence: Path,
    output_dir: Path,
) -> tuple[list[dict[str, Any]], Path]:
    output_dir = output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=False)
    build_payload = _validate_build_evidence(build_evidence, str(next(iter(routes)).new_subject["source_commit"]))
    del build_payload
    build_hash = sha256_file(build_evidence)
    created_at = utc_now()
    records: list[dict[str, Any]] = []
    for route in routes:
        receipt = _receipt_payload(route, catalogs, build_evidence, build_hash, created_at)
        receipt_path = output_dir / route.route / f"{route.task_id}.json"
        _write_json(receipt_path, receipt)
        records.append(
            {
                "task_id": route.task_id,
                "route": route.route,
                "path": stable_absolute_path(receipt_path),
                "sha256": sha256_file(receipt_path),
                "transformation_id": receipt["result"]["transformation_id"],
            }
        )
    batch = {
        "schema": BATCH_SCHEMA,
        "created_at": created_at,
        "catalogs": dict(catalogs),
        "route_counts": dict(Counter(record["route"] for record in records)),
        "build_evidence": {"path": stable_absolute_path(build_evidence), "sha256": build_hash},
        "items": records,
    }
    batch_path = output_dir / "authority-relocation-batch-v2.json"
    _write_json(batch_path, batch)
    return records, batch_path


def _assert_receipt(
    receipt_path: Path,
    expected_hash: str,
    route: AuthorityRoute,
    build_evidence: Path,
) -> dict[str, Any]:
    if sha256_file(receipt_path) != expected_hash:
        raise AuthorityRelocationError(f"Receipt hash mismatch: {receipt_path}")
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    expected_schema = TYPED_REBIND_SCHEMA if route.route == "typed_evidence_bridge" else RELOCATION_SCHEMA
    if payload.get("schema") != expected_schema or payload.get("route") != route.route:
        raise AuthorityRelocationError(f"Receipt schema/route mismatch: {receipt_path}")
    if payload.get("old_current_subject") != _subject_snapshot(route.old_subject):
        raise AuthorityRelocationError(f"Receipt old subject mismatch: {receipt_path}")
    if payload.get("unified_target_subject") != _subject_snapshot(route.new_subject):
        raise AuthorityRelocationError(f"Receipt unified subject mismatch: {receipt_path}")
    if payload.get("relocation_source_subject") != _subject_snapshot(route.relocation_source):
        raise AuthorityRelocationError(f"Receipt relocation source mismatch: {receipt_path}")
    if payload.get("authority") != dict(route.authority):
        raise AuthorityRelocationError(f"Receipt authority chain mismatch: {receipt_path}")
    build = payload.get("build_evidence", {})
    if stable_absolute_path(build_evidence) != build.get("path") or sha256_file(build_evidence) != build.get(
        "sha256"
    ):
        raise AuthorityRelocationError(f"Receipt build evidence mismatch: {receipt_path}")
    if payload.get("claims") != {
        "repository_relocation_only": True,
        "semantic_review_created": False,
        "semantic_upgrade": False,
        "rubric_upgrade": False,
        "completion_class_upgrade": False,
        "authority_eligibility_upgrade": False,
    }:
        raise AuthorityRelocationError(f"Receipt upgrade guard mismatch: {receipt_path}")
    return payload


def _ensure_legacy_transformation_chains(
    store: WorkspaceStateStore,
    validated: Sequence[tuple[AuthorityRoute, Mapping[str, Any], Path, dict[str, Any]]],
) -> int:
    """Restore only canonical transformation edges absent from the rebuilt projection."""

    restored = 0
    for route, _record, _receipt_path, payload in validated:
        if route.route != "validated_transformation":
            continue
        authority = route.authority
        transformation_id = str(authority["transformation_id"])
        with store._connection(write=True) as connection:
            row = connection.execute(
                "SELECT * FROM transformations WHERE transformation_id = ?",
                (transformation_id,),
            ).fetchone()
            review = connection.execute(
                "SELECT subject_id FROM reviews WHERE review_id = ?",
                (str(authority["review_id"]),),
            ).fetchone()
        if review is None or str(review["subject_id"]) != str(authority["source_subject_id"]):
            raise AuthorityRelocationError(
                f"Legacy review basis is missing for {route.task_id}."
            )
        expected = {
            "task_id": route.task_id,
            "source_subject_id": str(authority["source_subject_id"]),
            "target_subject_id": str(authority["target_subject_id"]),
            "transformation_kind": str(authority["transformation_kind"]),
            "mechanical_status": str(authority["mechanical_status"]),
            "build_status": str(authority["build_status"]),
            "evidence_path": str(authority["transformation_evidence_path"]),
            "evidence_hash": str(authority["transformation_evidence_hash"]),
        }
        if row is not None:
            if any(str(row[key]) != value for key, value in expected.items()):
                raise AuthorityRelocationError(
                    f"Legacy transformation collision for {route.task_id}."
                )
            continue
        generated = store.record_transformation(
            task_id=route.task_id,
            source_subject_id=expected["source_subject_id"],
            target_subject_id=expected["target_subject_id"],
            transformation_kind=expected["transformation_kind"],
            mechanical_status=expected["mechanical_status"],
            build_status=expected["build_status"],
            evidence_path=expected["evidence_path"],
            evidence_hash=expected["evidence_hash"],
            identity_schema=LEGACY_TRANSFORMATION_SCHEMA,
        )
        if generated != transformation_id:
            raise AuthorityRelocationError(
                f"Legacy transformation identity mismatch for {route.task_id}."
            )
        restored += 1
    return restored


def restore_missing_legacy_transformation_chains(
    target_db: Path,
    routes: Sequence[AuthorityRoute],
    records: Sequence[Mapping[str, Any]],
    build_evidence: Path,
) -> dict[str, Any]:
    """Idempotently complete chains omitted by a stricter check-only rebuild."""

    validated = [
        (
            route,
            record,
            Path(str(record["path"])),
            _assert_receipt(
                Path(str(record["path"])), str(record["sha256"]), route, build_evidence
            ),
        )
        for route, record in zip(routes, records, strict=True)
    ]
    store = WorkspaceStateStore(target_db)
    store.initialize()
    with store.bulk_write():
        restored = _ensure_legacy_transformation_chains(store, validated)
    return {"validated": len(validated), "restored_legacy_transformations": restored}


def apply_relocation_receipts(
    target_db: Path,
    routes: Sequence[AuthorityRoute],
    records: Sequence[Mapping[str, Any]],
    build_evidence: Path,
) -> dict[str, Any]:
    """Validate all receipts, then apply the closed set in one transaction."""

    if len(routes) != len(records) or [route.task_id for route in routes] != [
        str(record["task_id"]) for record in records
    ]:
        raise AuthorityRelocationError("Receipt index does not match the planned task sequence.")
    validated: list[tuple[AuthorityRoute, Mapping[str, Any], Path, dict[str, Any]]] = []
    for route, record in zip(routes, records, strict=True):
        path = Path(str(record["path"]))
        payload = _assert_receipt(path, str(record["sha256"]), route, build_evidence)
        validated.append((route, record, path, payload))

    store = WorkspaceStateStore(target_db)
    store.initialize()
    return _apply_validated_relocation_receipts(store, validated)


def _apply_validated_relocation_receipts(
    store: WorkspaceStateStore,
    validated: Sequence[tuple[AuthorityRoute, Mapping[str, Any], Path, dict[str, Any]]],
) -> dict[str, Any]:
    """Apply a fully validated closed receipt set to one existing store."""

    with store._connection(write=store._bulk_connection is not None) as connection:
        before_reviews = int(connection.execute("SELECT COUNT(*) FROM reviews").fetchone()[0])
        before_eligible = int(
            connection.execute(
                "SELECT COUNT(DISTINCT task_id) FROM reviews WHERE verdict='pass' AND phase2_status='pass' AND authority_eligible=1"
            ).fetchone()[0]
        )
    generated_bindings: list[str] = []
    with store.bulk_write():
        restored_legacy_transformations = _ensure_legacy_transformation_chains(store, validated)
        for route, record, receipt_path, payload in validated:
            receipt_hash = str(record["sha256"])
            target_bundle = _bundle_from_row(route.new_subject)
            if route.route == "typed_evidence_bridge":
                binding_id, transformation_id = store.record_evidence_bridge_binding(
                    source=_bundle_from_row(route.relocation_source),
                    target=target_bundle,
                    bridge_route=str(route.authority["bridge_route"]),
                    authority_type=str(route.authority["authority_type"]),
                    capability=str(route.authority["capability"]),
                    decision_path=str(route.authority["decision_path"]),
                    decision_hash=str(route.authority["decision_hash"]),
                    evidence_path=receipt_path,
                    evidence_hash=receipt_hash,
                    created_at=str(payload["created_at"]),
                    transformation_identity_schema=TRANSFORMATION_SCHEMA,
                    binding_identity_schema=BINDING_SCHEMA,
                )
                generated_bindings.append(binding_id)
            else:
                transformation_id = store.record_transformation(
                    task_id=route.task_id,
                    source_subject_id=str(route.relocation_source["subject_id"]),
                    target_subject_id=str(route.new_subject["subject_id"]),
                    transformation_kind="repository_relocation",
                    mechanical_status="pass",
                    build_status="pass",
                    evidence_path=receipt_path,
                    evidence_hash=receipt_hash,
                    identity_schema=TRANSFORMATION_SCHEMA,
                )
            if transformation_id != str(payload["result"]["transformation_id"]):
                raise AuthorityRelocationError(f"Transformation identity mismatch for {route.task_id}.")
        with store._connection(write=True) as connection:
            after_reviews = int(connection.execute("SELECT COUNT(*) FROM reviews").fetchone()[0])
            after_eligible = int(
                connection.execute(
                    "SELECT COUNT(DISTINCT task_id) FROM reviews WHERE verdict='pass' AND phase2_status='pass' AND authority_eligible=1"
                ).fetchone()[0]
            )
            valid_new_bindings = int(
                connection.execute(
                    "SELECT COUNT(*) FROM valid_authority_bindings_v2 WHERE binding_id IN (%s)"
                    % ",".join("?" for _ in generated_bindings),
                    generated_bindings,
                ).fetchone()[0]
            )
        if before_reviews != after_reviews or before_eligible != after_eligible:
            raise AuthorityRelocationError("Relocation changed review rows or authority eligibility.")
        if valid_new_bindings != EXPECTED_ROUTE_COUNTS["typed_evidence_bridge"]:
            raise AuthorityRelocationError("Relocated typed bindings are not all structurally valid.")
    return {
        "applied": len(validated),
        "route_counts": dict(Counter(route.route for route, *_ in validated)),
        "reviews_unchanged": before_reviews == after_reviews,
        "authority_eligible_tasks_unchanged": before_eligible == after_eligible,
        "valid_new_typed_bindings": valid_new_bindings,
        "restored_legacy_transformations": restored_legacy_transformations,
    }


def replay_authority_relocation_batch(
    store: WorkspaceStateStore,
    batch_path: Path,
) -> dict[str, Any]:
    """Replay the immutable Phase 5 batch without consulting the legacy database.

    The batch and its item receipts contain the closed 452-task route partition.
    A replay still requires every referenced subject, current unified head, review
    basis, decision object, and build log to be present and byte-identical.  It
    creates only mechanical transformations/bindings; it never creates reviews.
    """

    batch_path = batch_path.expanduser().resolve()
    try:
        batch = json.loads(batch_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AuthorityRelocationError(f"Cannot read authority relocation batch: {exc}") from exc
    if not isinstance(batch, Mapping) or batch.get("schema") != BATCH_SCHEMA:
        raise AuthorityRelocationError("Authority relocation batch schema mismatch.")
    items = batch.get("items")
    if not isinstance(items, list) or not all(isinstance(item, Mapping) for item in items):
        raise AuthorityRelocationError("Authority relocation batch items are malformed.")
    counts = Counter(str(item.get("route", "")) for item in items)
    if dict(counts) != EXPECTED_ROUTE_COUNTS or batch.get("route_counts") != EXPECTED_ROUTE_COUNTS:
        raise AuthorityRelocationError("Authority relocation batch route partition is not 181/159/112.")
    task_ids = [str(item.get("task_id", "")) for item in items]
    if len(task_ids) != sum(EXPECTED_ROUTE_COUNTS.values()) or len(set(task_ids)) != len(task_ids):
        raise AuthorityRelocationError("Authority relocation batch is not a unique 452-task set.")

    build_record = batch.get("build_evidence")
    if not isinstance(build_record, Mapping):
        raise AuthorityRelocationError("Authority relocation batch lacks build evidence.")
    build_path = Path(str(build_record.get("path", ""))).expanduser().resolve()
    if not build_path.is_file() or sha256_file(build_path) != str(build_record.get("sha256", "")):
        raise AuthorityRelocationError("Authority relocation build evidence path/hash mismatch.")
    try:
        build_payload = json.loads(build_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AuthorityRelocationError(f"Cannot read relocation build evidence: {exc}") from exc
    target_commit = str(build_payload.get("target_commit", ""))
    _validate_build_evidence(build_path, target_commit)

    receipt_records: list[tuple[Mapping[str, Any], Path, str, dict[str, Any]]] = []
    subject_ids: set[str] = set()
    for record in items:
        receipt_path = Path(str(record.get("path", ""))).expanduser().resolve()
        expected_hash = str(record.get("sha256", ""))
        if not receipt_path.is_file() or sha256_file(receipt_path) != expected_hash:
            raise AuthorityRelocationError(f"Receipt path/hash mismatch: {receipt_path}")
        try:
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise AuthorityRelocationError(
                f"Cannot read relocation receipt {receipt_path}: {exc}"
            ) from exc
        for name in (
            "old_current_subject",
            "relocation_source_subject",
            "unified_target_subject",
        ):
            snapshot = receipt.get(name)
            if not isinstance(snapshot, Mapping) or not str(snapshot.get("subject_id", "")):
                raise AuthorityRelocationError(
                    f"Receipt subject snapshots are malformed: {receipt_path}"
                )
            subject_ids.add(str(snapshot["subject_id"]))
        receipt_records.append((record, receipt_path, expected_hash, receipt))

    store.initialize()
    with store._connection(write=store._bulk_connection is not None) as connection:
        target_catalog = _active_catalog_id(connection)
        catalogs = batch.get("catalogs")
        if not isinstance(catalogs, Mapping) or str(catalogs.get("target", "")) != target_catalog:
            raise AuthorityRelocationError("Authority relocation target catalog is not active.")
        catalog_tasks = {
            str(row["task_id"])
            for row in connection.execute(
                "SELECT task_id FROM catalog_tasks WHERE catalog_id = ?", (target_catalog,)
            )
        }
        if set(task_ids) != catalog_tasks:
            raise AuthorityRelocationError("Authority relocation tasks do not equal the active catalog.")
        unified_heads = {
            str(row["task_id"]): str(row["subject_id"])
            for row in connection.execute(
                """
                SELECT task_id, subject_id FROM task_heads
                WHERE role = 'unified_main' AND freshness IN ('fresh', 'local')
                """
            )
        }
        subject_rows = {
            str(row["subject_id"]): dict(row)
            for row in connection.execute(
                "SELECT * FROM subjects WHERE subject_id IN (%s)"
                % ",".join("?" for _ in subject_ids),
                tuple(subject_ids),
            )
        }

    validated: list[tuple[AuthorityRoute, Mapping[str, Any], Path, dict[str, Any]]] = []
    for record, receipt_path, expected_hash, receipt in receipt_records:
        task_id = str(record.get("task_id", ""))
        route_name = str(record.get("route", ""))
        if receipt.get("task_id") != task_id or receipt.get("route") != route_name:
            raise AuthorityRelocationError(f"Receipt index mismatch: {receipt_path}")
        snapshots = {
            name: receipt.get(name)
            for name in (
                "old_current_subject",
                "relocation_source_subject",
                "unified_target_subject",
            )
        }
        actual: dict[str, Mapping[str, Any]] = {}
        for name, snapshot in snapshots.items():
            subject_id = str(snapshot.get("subject_id", ""))
            row = subject_rows.get(subject_id)
            if row is None or _subject_snapshot(row) != dict(snapshot):
                raise AuthorityRelocationError(
                    f"Receipt {name} is absent or differs from rebuilt state: {receipt_path}"
                )
            actual[name] = row
        if unified_heads.get(task_id) != str(actual["unified_target_subject"]["subject_id"]):
            raise AuthorityRelocationError(f"Receipt target is not the current unified head: {task_id}")
        if str(actual["unified_target_subject"]["source_commit"]) != target_commit:
            raise AuthorityRelocationError(f"Receipt target/build commit mismatch: {task_id}")
        _assert_exact_subject_move(
            actual["old_current_subject"], actual["unified_target_subject"]
        )
        authority = receipt.get("authority")
        if not isinstance(authority, Mapping):
            raise AuthorityRelocationError(f"Receipt authority is malformed: {receipt_path}")
        route = AuthorityRoute(
            task_id=task_id,
            route=route_name,
            old_subject=actual["old_current_subject"],
            new_subject=actual["unified_target_subject"],
            relocation_source=actual["relocation_source_subject"],
            authority=dict(authority),
        )
        checked = _assert_receipt(receipt_path, expected_hash, route, build_path)
        result = checked.get("result")
        if not isinstance(result, Mapping) or (
            str(result.get("transformation_id", ""))
            != str(record.get("transformation_id", ""))
        ):
            raise AuthorityRelocationError(f"Receipt transformation index mismatch: {receipt_path}")
        validated.append((route, record, receipt_path, checked))

    application = _apply_validated_relocation_receipts(store, validated)
    application["batch_path"] = stable_absolute_path(batch_path)
    application["batch_sha256"] = sha256_file(batch_path)
    return application


def execute_phase5(
    *,
    legacy_db: Path,
    target_db: Path,
    repo: Path,
    target_commit: str,
    output_root: Path,
    apply: bool,
) -> dict[str, Any]:
    output_root = output_root.expanduser().resolve()
    output_root.mkdir(parents=True, exist_ok=False)
    build_path = create_build_evidence(repo, target_commit, output_root / "build")
    routes, catalogs = plan_authority_routes(legacy_db, target_db)
    if any(str(route.new_subject["source_commit"]) != target_commit for route in routes):
        raise AuthorityRelocationError("Unified subjects do not all bind the requested target commit.")
    records, batch_path = write_relocation_receipts(
        routes, catalogs, build_path, output_root / "receipts"
    )
    result: dict[str, Any] = {
        "schema": BATCH_SCHEMA,
        "build_evidence": stable_absolute_path(build_path),
        "batch_receipt": stable_absolute_path(batch_path),
        "planned": len(routes),
        "route_counts": dict(Counter(route.route for route in routes)),
        "applied": False,
    }
    if apply:
        result["application"] = apply_relocation_receipts(target_db, routes, records, build_path)
        result["applied"] = True
    _write_json(output_root / "phase5-result.json", result)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--legacy-db", type=Path, required=True)
    parser.add_argument("--target-db", type=Path, required=True)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--target-commit", required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        result = execute_phase5(
            legacy_db=arguments.legacy_db,
            target_db=arguments.target_db,
            repo=arguments.repo,
            target_commit=arguments.target_commit,
            output_root=arguments.output_root,
            apply=arguments.apply,
        )
    except AuthorityRelocationError as error:
        parser.exit(2, f"authority relocation failed: {error}\n")
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
