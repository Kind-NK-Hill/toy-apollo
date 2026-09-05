from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import sqlite3
import tempfile
from contextlib import closing, contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, TypeVar

from .core.settings import DEFAULT_PROFILE, PROFILE_SPECS
from .review_versions import prompt_version_sql_predicate, rubric_version_sql_predicate


SCHEMA_VERSION = 1
STATE_MODEL_VERSION = 2
DEFAULT_BUSY_TIMEOUT_MS = 10_000
LEGACY_SUBJECT_SCHEMA = "toy-apollo.subject.v1"
SUBJECT_SCHEMA_V2 = "formalization-engine.subject.v2"
LEGACY_TRANSFORMATION_SCHEMA = "toy-apollo.transformation.v1"


def subject_identity_schema(source_repo: str, layout: str) -> str:
    if (
        str(source_repo or "").strip().lower() == "probabilitytheoryformalization"
        and str(layout or "").strip().lower() == "unified"
    ):
        return SUBJECT_SCHEMA_V2
    return LEGACY_SUBJECT_SCHEMA


class StateStoreError(RuntimeError):
    """Base error for the workspace state store."""


class StateDatabaseMissingError(StateStoreError):
    """Raised when a read-only operation targets a missing database."""


class StateIntegrityError(StateStoreError):
    """Raised when SQLite cannot prove that the database is structurally sound."""


class StateConcurrencyError(StateStoreError):
    """Raised when a caller tries to save over a newer state revision."""


class StatePathError(StateStoreError):
    """Raised when the canonical state database resolves into a campaign/repo root."""


def canonical_state_path(artifact_root: str | Path) -> Path:
    """Return the explicit artifact-root state path without repository-name inference."""
    return Path(artifact_root).expanduser().resolve() / "state.sqlite3"

def refuse_legacy_ledger_write(
    runtime_root: str | Path,
    *,
    operation: str,
    artifact_root: str | Path | None = None,
) -> None:
    root = Path(runtime_root).expanduser().resolve()
    resolved_artifacts = (
        Path(artifact_root).expanduser().resolve()
        if artifact_root is not None
        else root.parent / "ProbabilityTheoryFormalization-artifacts"
    )
    candidates = [canonical_state_path(resolved_artifacts), root / "state.sqlite3"]
    state_path = next((path for path in candidates if path.is_file()), None)
    if state_path is not None:
        raise StateStoreError(
            f"{operation} is disabled because canonical SQLite state exists at {state_path}. "
            "Use the workspace state API or an explicit state rebuild instead of rewriting project_ledger.json."
        )


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def filesystem_path(path: str | Path) -> Path:
    """Return a Windows extended-length spelling for local file I/O."""

    resolved = Path(path)
    raw = str(resolved)
    if os.name == "nt" and resolved.is_absolute() and not raw.startswith("\\\\?\\"):
        return Path("\\\\?\\" + raw)
    return resolved


def stable_absolute_path(path: str | Path) -> str:
    candidate = Path(path).expanduser()
    return str(candidate if candidate.is_absolute() else candidate.absolute())


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with filesystem_path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_json(payload: Any) -> str:
    raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return sha256_bytes(raw.encode("utf-8"))


def git_blob_sha(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def canonical_subject_bytes(path: str, payload: bytes) -> bytes:
    if not path.lower().endswith(".lean"):
        return payload
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        return payload
    return text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")


@dataclass(frozen=True)
class SubjectFile:
    path: str
    content_sha256: str
    git_blob_sha: str
    size: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "content_sha256": self.content_sha256,
            "git_blob_sha": self.git_blob_sha,
            "size": self.size,
        }


@dataclass(frozen=True)
class SubjectBundle:
    subject_id: str
    task_id: str
    subject_kind: str
    source_repo: str
    source_commit: str
    layout: str
    bundle_hash: str
    primary_hash: str
    primary_path: str
    files: tuple[SubjectFile, ...]
    parent_subject_id: str = ""
    created_at: str = ""
    identity_schema: str = LEGACY_SUBJECT_SCHEMA

    @classmethod
    def from_files(
        cls,
        *,
        task_id: str,
        files: Mapping[str, bytes | str],
        primary_path: str,
        source_repo: str,
        source_commit: str = "",
        layout: str = "",
        subject_kind: str = "bundle",
        parent_subject_id: str = "",
        created_at: str | None = None,
        identity_schema: str | None = None,
    ) -> "SubjectBundle":
        if not files:
            raise ValueError("A subject bundle must contain at least one file.")
        normalized: list[SubjectFile] = []
        primary_hash = ""
        canonical_primary = primary_path.replace("\\", "/")
        for raw_path, raw_content in sorted(files.items(), key=lambda item: item[0].replace("\\", "/").lower()):
            logical_path = raw_path.replace("\\", "/")
            content = raw_content.encode("utf-8") if isinstance(raw_content, str) else raw_content
            content = canonical_subject_bytes(logical_path, content)
            item = SubjectFile(
                path=logical_path,
                content_sha256=sha256_bytes(content),
                git_blob_sha=git_blob_sha(content),
                size=len(content),
            )
            normalized.append(item)
            if logical_path == canonical_primary:
                primary_hash = item.content_sha256
        if not primary_hash:
            raise ValueError(f"Primary path {canonical_primary!r} is not present in the subject bundle.")
        manifest = [item.as_dict() for item in normalized]
        bundle_hash = sha256_json(manifest)
        resolved_schema = identity_schema or subject_identity_schema(source_repo, layout)
        identity = {
            "schema": resolved_schema,
            "task_id": task_id,
            "subject_kind": subject_kind,
            "source_repo": source_repo,
            "source_commit": source_commit,
            "layout": layout,
            "bundle_hash": bundle_hash,
            "primary_path": canonical_primary,
        }
        return cls(
            subject_id=sha256_json(identity),
            task_id=task_id,
            subject_kind=subject_kind,
            source_repo=source_repo,
            source_commit=source_commit,
            layout=layout,
            bundle_hash=bundle_hash,
            primary_hash=primary_hash,
            primary_path=canonical_primary,
            files=tuple(normalized),
            parent_subject_id=parent_subject_id,
            created_at=created_at or utc_now(),
            identity_schema=resolved_schema,
        )

    @classmethod
    def from_manifest(
        cls,
        *,
        task_id: str,
        files: Iterable[Mapping[str, Any]],
        primary_path: str,
        source_repo: str,
        source_commit: str = "",
        layout: str = "",
        subject_kind: str = "bundle",
        parent_subject_id: str = "",
        created_at: str | None = None,
        identity_schema: str | None = None,
    ) -> "SubjectBundle":
        normalized: list[SubjectFile] = []
        canonical_primary = primary_path.replace("\\", "/")
        primary_hash = ""
        for raw in files:
            path = str(raw.get("path", "")).replace("\\", "/")
            if not path:
                continue
            item = SubjectFile(
                path=path,
                content_sha256=str(raw.get("content_sha256", "") or ""),
                git_blob_sha=str(raw.get("git_blob_sha", "") or ""),
                size=int(raw.get("size", 0) or 0),
            )
            normalized.append(item)
            if path == canonical_primary:
                primary_hash = item.content_sha256 or f"git:{item.git_blob_sha}"
        if not normalized:
            raise ValueError("A subject manifest must contain at least one file.")
        if not primary_hash:
            raise ValueError(f"Primary path {canonical_primary!r} is not present in the subject manifest.")
        normalized.sort(key=lambda item: item.path.lower())
        manifest = [item.as_dict() for item in normalized]
        bundle_hash = sha256_json(manifest)
        resolved_schema = identity_schema or subject_identity_schema(source_repo, layout)
        identity = {
            "schema": resolved_schema,
            "task_id": task_id,
            "subject_kind": subject_kind,
            "source_repo": source_repo,
            "source_commit": source_commit,
            "layout": layout,
            "bundle_hash": bundle_hash,
            "primary_path": canonical_primary,
        }
        return cls(
            subject_id=sha256_json(identity),
            task_id=task_id,
            subject_kind=subject_kind,
            source_repo=source_repo,
            source_commit=source_commit,
            layout=layout,
            bundle_hash=bundle_hash,
            primary_hash=primary_hash,
            primary_path=canonical_primary,
            files=tuple(normalized),
            parent_subject_id=parent_subject_id,
            created_at=created_at or utc_now(),
            identity_schema=resolved_schema,
        )

    @classmethod
    def from_legacy_hash(
        cls,
        *,
        task_id: str,
        candidate_hash: str,
        evidence_hash: str,
        source_repo: str,
        primary_path: str = "",
        authority_scope: str = "historical",
        created_at: str | None = None,
        identity_schema: str = LEGACY_SUBJECT_SCHEMA,
    ) -> "SubjectBundle":
        bound_hash = candidate_hash.strip()
        kind = "legacy_bound" if bound_hash else "legacy_unbound"
        synthetic_hash = bound_hash or f"evidence:{evidence_hash}"
        logical_path = primary_path.replace("\\", "/") or f"legacy/{task_id}.lean"
        manifest_file = SubjectFile(
            path=logical_path,
            content_sha256=synthetic_hash,
            git_blob_sha="",
            size=0,
        )
        identity = {
            "schema": identity_schema,
            "task_id": task_id,
            "subject_kind": kind,
            "source_repo": source_repo,
            "authority_scope": authority_scope,
            "primary_hash": synthetic_hash,
            "evidence_hash": evidence_hash,
        }
        return cls(
            subject_id=sha256_json(identity),
            task_id=task_id,
            subject_kind=kind,
            source_repo=source_repo,
            source_commit="",
            layout=authority_scope,
            bundle_hash=sha256_json([manifest_file.as_dict()]),
            primary_hash=synthetic_hash,
            primary_path=logical_path,
            files=(manifest_file,),
            created_at=created_at or utc_now(),
            identity_schema=identity_schema,
        )

    def manifest(self) -> list[dict[str, Any]]:
        return [item.as_dict() for item in self.files]

    def primary_git_sha(self) -> str:
        return next((item.git_blob_sha for item in self.files if item.path == self.primary_path), "")

    def as_dict(self) -> dict[str, Any]:
        return {
            "schema": self.identity_schema,
            "subject_id": self.subject_id,
            "task_id": self.task_id,
            "subject_kind": self.subject_kind,
            "source_repo": self.source_repo,
            "source_commit": self.source_commit,
            "layout": self.layout,
            "bundle_hash": self.bundle_hash,
            "primary_hash": self.primary_hash,
            "primary_path": self.primary_path,
            "files": self.manifest(),
            "parent_subject_id": self.parent_subject_id,
        }


T = TypeVar("T")


SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS meta (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS campaign_ledgers (
    campaign_id TEXT PRIMARY KEY,
    artifact_root TEXT NOT NULL,
    legacy_ledger_path TEXT NOT NULL DEFAULT '',
    ledger_json TEXT NOT NULL,
    revision INTEGER NOT NULL DEFAULT 1,
    imported_from TEXT NOT NULL DEFAULT '',
    updated_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS subjects (
    subject_id TEXT PRIMARY KEY,
    task_id TEXT NOT NULL,
    subject_kind TEXT NOT NULL,
    source_repo TEXT NOT NULL,
    source_commit TEXT NOT NULL DEFAULT '',
    layout TEXT NOT NULL DEFAULT '',
    bundle_hash TEXT NOT NULL,
    primary_hash TEXT NOT NULL,
    primary_git_sha TEXT NOT NULL DEFAULT '',
    primary_path TEXT NOT NULL,
    manifest_json TEXT NOT NULL,
    parent_subject_id TEXT REFERENCES subjects(subject_id),
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS subjects_task_idx ON subjects(task_id, created_at DESC);
CREATE INDEX IF NOT EXISTS subjects_hash_idx ON subjects(task_id, bundle_hash, primary_hash);

CREATE TABLE IF NOT EXISTS reviews (
    review_id TEXT PRIMARY KEY,
    task_id TEXT NOT NULL,
    subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    verdict TEXT NOT NULL,
    proof_class TEXT NOT NULL DEFAULT '',
    completion_class TEXT NOT NULL DEFAULT '',
    phase2_status TEXT NOT NULL DEFAULT '',
    evidence_path TEXT NOT NULL,
    evidence_hash TEXT NOT NULL,
    reviewer_independence TEXT NOT NULL DEFAULT '',
    authority_scope TEXT NOT NULL DEFAULT 'phase2_review_apply',
    authority_eligible INTEGER NOT NULL DEFAULT 0 CHECK(authority_eligible IN (0, 1)),
    reviewed_at TEXT NOT NULL,
    UNIQUE(evidence_hash, subject_id)
);
CREATE INDEX IF NOT EXISTS reviews_task_idx ON reviews(task_id, reviewed_at DESC);
CREATE INDEX IF NOT EXISTS reviews_subject_idx ON reviews(subject_id, reviewed_at DESC);

CREATE TABLE IF NOT EXISTS transformations (
    transformation_id TEXT PRIMARY KEY,
    task_id TEXT NOT NULL,
    source_subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    target_subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    transformation_kind TEXT NOT NULL,
    mechanical_status TEXT NOT NULL,
    build_status TEXT NOT NULL DEFAULT '',
    evidence_path TEXT NOT NULL DEFAULT '',
    evidence_hash TEXT NOT NULL DEFAULT '',
    created_at TEXT NOT NULL,
    UNIQUE(source_subject_id, target_subject_id, transformation_kind)
);

CREATE TABLE IF NOT EXISTS authority_bindings (
    binding_id TEXT PRIMARY KEY,
    task_id TEXT NOT NULL,
    source_subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    target_subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    transformation_id TEXT NOT NULL REFERENCES transformations(transformation_id),
    bridge_route TEXT NOT NULL CHECK(bridge_route IN (
        'kenneth_author_exact_bridge',
        'reviewed_mat_sync_reassembly_bridge'
    )),
    authority_type TEXT NOT NULL CHECK(authority_type IN (
        'kenneth_git_author_exact',
        'historical_review_apply_recovery',
        'mat_exact_review_apply',
        'mat_sync_author_attested_selection'
    )),
    capability TEXT NOT NULL CHECK(capability IN (
        'author_current_exact_acceptance',
        'reviewed_source_mechanical_projection',
        'sync_author_attested_acceptance'
    )),
    decision_path TEXT NOT NULL,
    decision_hash TEXT NOT NULL,
    evidence_path TEXT NOT NULL,
    evidence_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(target_subject_id, capability),
    UNIQUE(evidence_hash, target_subject_id)
);
CREATE INDEX IF NOT EXISTS authority_bindings_task_idx
    ON authority_bindings(task_id, created_at DESC);
CREATE INDEX IF NOT EXISTS authority_bindings_target_idx
    ON authority_bindings(target_subject_id, capability);

CREATE VIEW IF NOT EXISTS valid_authority_bindings AS
SELECT b.*
FROM authority_bindings b
JOIN subjects source ON source.subject_id = b.source_subject_id
JOIN subjects target ON target.subject_id = b.target_subject_id
JOIN transformations t ON t.transformation_id = b.transformation_id
WHERE b.task_id = source.task_id
  AND b.task_id = target.task_id
  AND b.task_id = t.task_id
  AND b.source_subject_id = t.source_subject_id
  AND b.target_subject_id = t.target_subject_id
  AND lower(target.source_repo) = 'mat'
  AND t.transformation_kind = 'verified_evidence_bridge'
  AND t.mechanical_status = 'pass'
  AND t.build_status = 'pass'
  AND (
    (b.bridge_route = 'kenneth_author_exact_bridge'
      AND b.authority_type = 'kenneth_git_author_exact'
      AND b.capability = 'author_current_exact_acceptance')
    OR
    (b.bridge_route = 'reviewed_mat_sync_reassembly_bridge'
      AND b.authority_type IN ('historical_review_apply_recovery', 'mat_exact_review_apply')
      AND b.capability = 'reviewed_source_mechanical_projection')
    OR
    (b.bridge_route = 'reviewed_mat_sync_reassembly_bridge'
      AND b.authority_type = 'mat_sync_author_attested_selection'
      AND b.capability = 'sync_author_attested_acceptance')
  )
  AND b.decision_path <> '' AND length(b.decision_hash) = 64
  AND b.decision_hash NOT GLOB '*[^0-9a-f]*'
  AND b.evidence_path <> '' AND length(b.evidence_hash) = 64
  AND b.evidence_hash NOT GLOB '*[^0-9a-f]*'
  AND NOT EXISTS (
    SELECT 1 FROM reviews r
    WHERE r.subject_id = b.target_subject_id
      AND r.evidence_hash = b.evidence_hash
  );

CREATE VIEW IF NOT EXISTS valid_authority_bindings_v2 AS
SELECT b.*
FROM authority_bindings b
JOIN subjects source ON source.subject_id = b.source_subject_id
JOIN subjects target ON target.subject_id = b.target_subject_id
JOIN transformations t ON t.transformation_id = b.transformation_id
WHERE b.task_id = source.task_id
  AND b.task_id = target.task_id
  AND b.task_id = t.task_id
  AND b.source_subject_id = t.source_subject_id
  AND b.target_subject_id = t.target_subject_id
  AND (
    lower(target.source_repo) = 'mat'
    OR (
      lower(target.source_repo) = 'probabilitytheoryformalization'
      AND lower(target.layout) = 'unified'
    )
  )
  AND t.transformation_kind = 'verified_evidence_bridge'
  AND t.mechanical_status = 'pass'
  AND t.build_status = 'pass'
  AND (
    (b.bridge_route = 'kenneth_author_exact_bridge'
      AND b.authority_type = 'kenneth_git_author_exact'
      AND b.capability = 'author_current_exact_acceptance')
    OR
    (b.bridge_route = 'reviewed_mat_sync_reassembly_bridge'
      AND b.authority_type IN ('historical_review_apply_recovery', 'mat_exact_review_apply')
      AND b.capability = 'reviewed_source_mechanical_projection')
    OR
    (b.bridge_route = 'reviewed_mat_sync_reassembly_bridge'
      AND b.authority_type = 'mat_sync_author_attested_selection'
      AND b.capability = 'sync_author_attested_acceptance')
  )
  AND b.decision_path <> '' AND length(b.decision_hash) = 64
  AND b.decision_hash NOT GLOB '*[^0-9a-f]*'
  AND b.evidence_path <> '' AND length(b.evidence_hash) = 64
  AND b.evidence_hash NOT GLOB '*[^0-9a-f]*'
  AND NOT EXISTS (
    SELECT 1 FROM reviews r
    WHERE r.subject_id = b.target_subject_id
      AND r.evidence_hash = b.evidence_hash
  );

CREATE TABLE IF NOT EXISTS runs (
    run_id TEXT PRIMARY KEY,
    campaign_id TEXT NOT NULL DEFAULT '',
    task_id TEXT NOT NULL,
    operation TEXT NOT NULL,
    status TEXT NOT NULL,
    subject_id TEXT REFERENCES subjects(subject_id),
    artifact_path TEXT NOT NULL DEFAULT '',
    detail_json TEXT NOT NULL DEFAULT '{}',
    started_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    completed_at TEXT NOT NULL DEFAULT ''
);
CREATE INDEX IF NOT EXISTS runs_task_idx ON runs(task_id, updated_at DESC);

CREATE TABLE IF NOT EXISTS integrations (
    integration_id TEXT PRIMARY KEY,
    task_id TEXT NOT NULL,
    subject_id TEXT REFERENCES subjects(subject_id),
    target_repo TEXT NOT NULL,
    integration_kind TEXT NOT NULL,
    state TEXT NOT NULL,
    branch TEXT NOT NULL DEFAULT '',
    pr_number INTEGER,
    head_sha TEXT NOT NULL DEFAULT '',
    merge_sha TEXT NOT NULL DEFAULT '',
    head_subject_id TEXT REFERENCES subjects(subject_id),
    observed_at TEXT NOT NULL,
    remote_freshness TEXT NOT NULL DEFAULT 'unknown',
    detail_json TEXT NOT NULL DEFAULT '{}',
    claimed_by TEXT NOT NULL DEFAULT '',
    claimed_at TEXT NOT NULL DEFAULT ''
);
CREATE INDEX IF NOT EXISTS integrations_task_idx ON integrations(task_id, observed_at DESC);
CREATE INDEX IF NOT EXISTS integrations_queue_idx ON integrations(integration_kind, target_repo, state, observed_at);

CREATE TABLE IF NOT EXISTS task_heads (
    task_id TEXT NOT NULL,
    role TEXT NOT NULL,
    subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    observed_at TEXT NOT NULL,
    freshness TEXT NOT NULL DEFAULT 'fresh',
    detail_json TEXT NOT NULL DEFAULT '{}',
    PRIMARY KEY(task_id, role)
);

CREATE TABLE IF NOT EXISTS dependency_pins (
    consumer_task_id TEXT NOT NULL,
    dependency_task_id TEXT NOT NULL,
    subject_id TEXT NOT NULL REFERENCES subjects(subject_id),
    required_role TEXT NOT NULL DEFAULT 'mat_main',
    state TEXT NOT NULL DEFAULT 'waiting',
    created_at TEXT NOT NULL,
    validated_at TEXT NOT NULL DEFAULT '',
    detail_json TEXT NOT NULL DEFAULT '{}',
    PRIMARY KEY(consumer_task_id, dependency_task_id)
);
CREATE INDEX IF NOT EXISTS dependency_pins_dependency_idx
    ON dependency_pins(dependency_task_id, required_role, state);

CREATE TABLE IF NOT EXISTS imports (
    source_path TEXT PRIMARY KEY,
    source_hash TEXT NOT NULL,
    source_kind TEXT NOT NULL,
    imported_at TEXT NOT NULL,
    record_count INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS catalog_versions (
    catalog_id TEXT PRIMARY KEY,
    schema_version TEXT NOT NULL,
    catalog_name TEXT NOT NULL,
    toy_commit TEXT NOT NULL,
    mat_commit TEXT NOT NULL,
    manifest_sha256 TEXT NOT NULL,
    plan_set_sha256 TEXT NOT NULL,
    policy_sha256 TEXT NOT NULL,
    counts_json TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    imported_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS catalog_families (
    catalog_id TEXT NOT NULL REFERENCES catalog_versions(catalog_id) ON DELETE CASCADE,
    family_id TEXT NOT NULL,
    book_label TEXT NOT NULL,
    family_kind TEXT NOT NULL,
    count_policy TEXT NOT NULL,
    PRIMARY KEY(catalog_id, family_id)
);

CREATE TABLE IF NOT EXISTS catalog_tasks (
    catalog_id TEXT NOT NULL REFERENCES catalog_versions(catalog_id) ON DELETE CASCADE,
    task_id TEXT NOT NULL,
    family_id TEXT NOT NULL,
    chapter INTEGER NOT NULL,
    task_kind TEXT NOT NULL,
    source_plan TEXT NOT NULL,
    source_plan_path TEXT NOT NULL,
    source_hash TEXT NOT NULL,
    primary_path TEXT NOT NULL,
    legacy_manifest_role TEXT NOT NULL,
    lifecycle_state TEXT NOT NULL,
    PRIMARY KEY(catalog_id, task_id),
    FOREIGN KEY(catalog_id, family_id)
        REFERENCES catalog_families(catalog_id, family_id)
);
CREATE INDEX IF NOT EXISTS catalog_tasks_family_idx
    ON catalog_tasks(catalog_id, family_id, task_id);

CREATE TABLE IF NOT EXISTS catalog_family_members (
    catalog_id TEXT NOT NULL,
    family_id TEXT NOT NULL,
    task_id TEXT NOT NULL,
    member_order INTEGER NOT NULL,
    PRIMARY KEY(catalog_id, family_id, task_id),
    FOREIGN KEY(catalog_id, family_id)
        REFERENCES catalog_families(catalog_id, family_id),
    FOREIGN KEY(catalog_id, task_id)
        REFERENCES catalog_tasks(catalog_id, task_id)
);

CREATE TABLE IF NOT EXISTS catalog_modules (
    catalog_id TEXT NOT NULL REFERENCES catalog_versions(catalog_id) ON DELETE CASCADE,
    path TEXT NOT NULL,
    basename TEXT NOT NULL,
    module_name TEXT NOT NULL,
    module_role TEXT NOT NULL CHECK(module_role IN ('primary', 'owned_support', 'shared')),
    owner_task_id TEXT,
    legacy_manifest_role TEXT NOT NULL,
    chapter INTEGER,
    PRIMARY KEY(catalog_id, path),
    UNIQUE(catalog_id, module_name),
    UNIQUE(catalog_id, basename),
    FOREIGN KEY(catalog_id, owner_task_id)
        REFERENCES catalog_tasks(catalog_id, task_id),
    CHECK(
        (module_role = 'shared' AND owner_task_id IS NULL)
        OR (module_role IN ('primary', 'owned_support') AND owner_task_id IS NOT NULL)
    )
);
CREATE INDEX IF NOT EXISTS catalog_modules_owner_idx
    ON catalog_modules(catalog_id, owner_task_id, module_role);

CREATE TABLE IF NOT EXISTS catalog_cohorts (
    catalog_id TEXT NOT NULL REFERENCES catalog_versions(catalog_id) ON DELETE CASCADE,
    cohort_id TEXT NOT NULL,
    task_id TEXT NOT NULL,
    PRIMARY KEY(catalog_id, cohort_id, task_id),
    FOREIGN KEY(catalog_id, task_id)
        REFERENCES catalog_tasks(catalog_id, task_id)
);

CREATE TABLE IF NOT EXISTS evidence_roots (
    root_id TEXT PRIMARY KEY,
    root_path TEXT NOT NULL UNIQUE,
    root_kind TEXT NOT NULL,
    active INTEGER NOT NULL DEFAULT 1 CHECK(active IN (0, 1)),
    detail_json TEXT NOT NULL DEFAULT '{}',
    registered_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS review_metadata (
    review_id TEXT PRIMARY KEY REFERENCES reviews(review_id) ON DELETE CASCADE,
    prompt_version INTEGER,
    rubric_version INTEGER,
    review_input_path TEXT NOT NULL DEFAULT '',
    review_input_hash TEXT NOT NULL DEFAULT '',
    reviewer_backend_id TEXT NOT NULL DEFAULT '',
    provenance_json TEXT NOT NULL DEFAULT '{}'
);

CREATE TABLE IF NOT EXISTS state_events (
    event_id TEXT PRIMARY KEY,
    event_type TEXT NOT NULL,
    task_id TEXT NOT NULL DEFAULT '',
    subject_id TEXT REFERENCES subjects(subject_id),
    evidence_path TEXT NOT NULL DEFAULT '',
    evidence_hash TEXT NOT NULL DEFAULT '',
    occurred_at TEXT NOT NULL,
    payload_json TEXT NOT NULL DEFAULT '{}',
    imported_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS state_events_task_idx
    ON state_events(task_id, occurred_at, event_type);
CREATE INDEX IF NOT EXISTS state_events_evidence_idx
    ON state_events(evidence_hash, event_type);

CREATE TABLE IF NOT EXISTS dataset_snapshots (
    dataset_id TEXT PRIMARY KEY,
    schema_version TEXT NOT NULL,
    catalog_id TEXT NOT NULL REFERENCES catalog_versions(catalog_id),
    payload_path TEXT NOT NULL DEFAULT '',
    payload_hash TEXT NOT NULL,
    invariants_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE VIEW IF NOT EXISTS evaluations AS
SELECT
    r.review_id AS evaluation_id,
    r.task_id,
    r.subject_id,
    r.verdict,
    r.proof_class,
    r.completion_class,
    r.phase2_status,
    r.evidence_path,
    r.evidence_hash,
    r.reviewer_independence,
    r.authority_scope,
    r.authority_eligible,
    r.reviewed_at,
    m.prompt_version,
    m.rubric_version,
    m.review_input_path,
    m.review_input_hash,
    m.reviewer_backend_id,
    m.provenance_json
FROM reviews r
LEFT JOIN review_metadata m ON m.review_id = r.review_id;
"""


class WorkspaceStateStore:
    """One workspace-level state database with immutable evidence bindings.

    The database owns current projections and cross-repository relationships.
    Large review/build artifacts remain files; rows retain their absolute path
    and hash so the database can be rebuilt without copying artifact contents.
    """

    def __init__(
        self,
        path: str | Path,
        *,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
        review_profile: str | None = None,
    ):
        self.path = Path(path).expanduser().resolve()
        self.busy_timeout_ms = int(busy_timeout_ms)
        self._initialized = False
        self._bulk_connection: sqlite3.Connection | None = None
        self._savepoint_serial = 0
        # Per-profile supported review versions ("mat" keeps the historical
        # prompt 9/10/11 + rubric 9 predicates; "cordis" uses prompt 1/rubric 1).
        profile = str(review_profile or "").strip().lower()
        if not profile:
            artifact_name = self.path.parent.name.lower()
            if artifact_name.endswith("-artifacts"):
                profile = artifact_name.removesuffix("-artifacts")
        self.review_profile = profile if profile in PROFILE_SPECS else DEFAULT_PROFILE

    def _prompt_version_pred(self, column: str = "m.prompt_version") -> str:
        return prompt_version_sql_predicate(self.review_profile, column)

    def _rubric_version_pred(self, column: str = "m.rubric_version") -> str:
        return rubric_version_sql_predicate(self.review_profile, column)

    @staticmethod
    def validate_canonical_path(path: Path, *, runtime_root: Path, artifact_root: Path) -> None:
        resolved = path.resolve()
        runtime = runtime_root.resolve()
        artifact = artifact_root.resolve()
        expected = canonical_state_path(artifact).resolve()
        if resolved != expected:
            raise StatePathError(
                f"Production state database must use the workspace canonical path {expected}; got {resolved}."
            )
        if resolved == runtime or runtime in resolved.parents:
            raise StatePathError(f"Canonical state database must not live inside the runtime repository: {resolved}")
        campaign_marker = artifact / "campaigns"
        if campaign_marker == resolved or campaign_marker in resolved.parents or "campaigns" in {
            part.lower() for part in resolved.parts
        }:
            raise StatePathError(f"Canonical state database must not live inside a campaign: {resolved}")

    @property
    def exists(self) -> bool:
        return self.path.is_file()

    def _connect(self, *, write: bool) -> sqlite3.Connection:
        if not self.exists and not write:
            raise StateDatabaseMissingError(f"Workspace state database does not exist: {self.path}")
        if write:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            connection = sqlite3.connect(self.path, timeout=self.busy_timeout_ms / 1000, isolation_level=None)
        else:
            uri = f"file:{self.path.as_posix()}?mode=ro"
            connection = sqlite3.connect(uri, timeout=self.busy_timeout_ms / 1000, isolation_level=None, uri=True)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute(f"PRAGMA busy_timeout = {self.busy_timeout_ms}")
        return connection

    @contextmanager
    def _connection(self, *, write: bool):
        if write and self._bulk_connection is not None:
            yield self._bulk_connection
            return
        connection = self._connect(write=write)
        try:
            with connection:
                yield connection
        finally:
            connection.close()

    @contextmanager
    def bulk_write(self):
        """Use one transaction for a rebuild's many immutable history rows."""

        if self._bulk_connection is not None:
            yield
            return
        self.initialize()
        connection = self._connect(write=True)
        try:
            connection.execute("PRAGMA journal_mode = MEMORY")
            connection.execute("PRAGMA synchronous = OFF")
            connection.execute("PRAGMA temp_store = MEMORY")
            connection.execute("PRAGMA cache_size = -262144")
            connection.execute("PRAGMA cache_spill = OFF")
            connection.execute("BEGIN IMMEDIATE")
            self._bulk_connection = connection
            yield
            connection.execute("COMMIT")
        except Exception:
            if connection.in_transaction:
                connection.execute("ROLLBACK")
            raise
        finally:
            self._bulk_connection = None
            connection.close()

    @contextmanager
    def atomic_write(self, label: str = "state_batch"):
        """Run a mutation group atomically, nesting through a SQLite savepoint."""

        self.initialize()
        if self._bulk_connection is not None:
            connection = self._bulk_connection
            self._savepoint_serial += 1
            name = f"{re.sub(r'[^A-Za-z0-9_]', '_', label)}_{self._savepoint_serial}"
            connection.execute(f"SAVEPOINT {name}")
            try:
                yield connection
                connection.execute(f"RELEASE SAVEPOINT {name}")
            except Exception:
                connection.execute(f"ROLLBACK TO SAVEPOINT {name}")
                connection.execute(f"RELEASE SAVEPOINT {name}")
                raise
            return
        connection = self._connect(write=True)
        try:
            connection.execute("BEGIN IMMEDIATE")
            self._bulk_connection = connection
            yield connection
            connection.execute("COMMIT")
        except Exception:
            if connection.in_transaction:
                connection.execute("ROLLBACK")
            raise
        finally:
            self._bulk_connection = None
            connection.close()

    def initialize(self) -> None:
        if self._initialized and self.exists:
            return
        existed = self.exists
        if existed:
            self.assert_integrity()
        try:
            with self._connection(write=True) as connection:
                connection.execute("PRAGMA journal_mode = DELETE")
                connection.execute("PRAGMA synchronous = FULL")
                connection.executescript(SCHEMA_SQL)
                row = connection.execute("SELECT value FROM meta WHERE key = 'schema_version'").fetchone()
                if row is None:
                    connection.execute(
                        "INSERT INTO meta(key, value) VALUES('schema_version', ?)",
                        (str(SCHEMA_VERSION),),
                    )
                else:
                    version = int(row["value"])
                    if version > SCHEMA_VERSION:
                        raise StateIntegrityError(
                            f"State database schema {version} is newer than supported schema {SCHEMA_VERSION}."
                        )
                    if version < SCHEMA_VERSION:
                        raise StateIntegrityError(
                            "A schema migration is required; use the explicit rebuild/migration command."
                        )
                if not existed:
                    connection.execute(
                        "INSERT INTO meta(key, value) VALUES('created_at', ?)",
                        (utc_now(),),
                    )
                self._initialized = True
        except sqlite3.DatabaseError as exc:
            raise StateIntegrityError(f"Unable to initialize workspace state database {self.path}: {exc}") from exc

    def assert_integrity(self) -> None:
        try:
            with self._connection(write=False) as connection:
                rows = connection.execute("PRAGMA quick_check").fetchall()
        except (sqlite3.DatabaseError, OSError) as exc:
            raise StateIntegrityError(f"Workspace state database is unreadable: {self.path}: {exc}") from exc
        messages = [str(row[0]) for row in rows]
        if messages != ["ok"]:
            raise StateIntegrityError(
                f"Workspace state database failed quick_check: {self.path}: {'; '.join(messages)}"
            )

    def summary(self) -> dict[str, Any]:
        self.assert_integrity()
        with self._connection(write=self._bulk_connection is not None) as connection:
            def count(table: str) -> int:
                present = connection.execute(
                    "SELECT 1 FROM sqlite_master WHERE type IN ('table', 'view') AND name = ?",
                    (table,),
                ).fetchone()
                if present is None:
                    return 0
                return int(connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0])

            version_row = connection.execute("SELECT value FROM meta WHERE key = 'schema_version'").fetchone()
            return {
                "path": str(self.path),
                "schema_version": int(version_row[0]) if version_row else 0,
                "campaign_ledgers": count("campaign_ledgers"),
                "subjects": count("subjects"),
                "reviews": count("reviews"),
                "authority_bindings": count("authority_bindings"),
                "runs": count("runs"),
                "integrations": count("integrations"),
                "task_heads": count("task_heads"),
                "dependency_pins": count("dependency_pins"),
                "imports": count("imports"),
                "catalog_versions": count("catalog_versions"),
                "catalog_tasks": count("catalog_tasks"),
                "catalog_families": count("catalog_families"),
                "catalog_modules": count("catalog_modules"),
                "evaluations": count("evaluations"),
                "state_events": count("state_events"),
                "dataset_snapshots": count("dataset_snapshots"),
            }

    def persist_catalog(self, catalog: Any, *, active: bool = True) -> str:
        """Persist one immutable task/family/module catalog.

        ``Any`` avoids coupling this low-level store to the catalog loader.  The
        accepted object is intentionally structural and must expose the frozen
        dataclass fields from :mod:`formalization_engine.task_catalog`.
        """

        self.initialize()
        payload = catalog.as_dict()
        serialized = json.dumps(payload, ensure_ascii=False, sort_keys=True)
        counts_json = json.dumps(catalog.counts(), ensure_ascii=False, sort_keys=True)
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT OR IGNORE INTO catalog_versions(
                    catalog_id, schema_version, catalog_name, toy_commit, mat_commit,
                    manifest_sha256, plan_set_sha256, policy_sha256, counts_json,
                    payload_json, imported_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    catalog.catalog_id,
                    catalog.schema_version,
                    catalog.catalog_name,
                    catalog.toy_commit,
                    catalog.mat_commit,
                    catalog.manifest_sha256,
                    catalog.plan_set_sha256,
                    catalog.policy_sha256,
                    counts_json,
                    serialized,
                    utc_now(),
                ),
            )
            existing = connection.execute(
                "SELECT payload_json FROM catalog_versions WHERE catalog_id = ?",
                (catalog.catalog_id,),
            ).fetchone()
            if existing is None or str(existing["payload_json"]) != serialized:
                raise StateIntegrityError(f"Catalog identity collision for {catalog.catalog_id}.")
            for family in catalog.families:
                connection.execute(
                    """
                    INSERT OR IGNORE INTO catalog_families(
                        catalog_id, family_id, book_label, family_kind, count_policy
                    ) VALUES (?, ?, ?, ?, ?)
                    """,
                    (
                        catalog.catalog_id,
                        family.family_id,
                        family.book_label,
                        family.family_kind,
                        family.count_policy,
                    ),
                )
            for task in catalog.tasks:
                connection.execute(
                    """
                    INSERT OR IGNORE INTO catalog_tasks(
                        catalog_id, task_id, family_id, chapter, task_kind,
                        source_plan, source_plan_path, source_hash, primary_path,
                        legacy_manifest_role, lifecycle_state
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        catalog.catalog_id,
                        task.task_id,
                        task.family_id,
                        task.chapter,
                        task.task_kind,
                        task.source_plan,
                        task.source_plan_path,
                        task.source_hash,
                        task.primary_path,
                        task.legacy_manifest_role,
                        task.lifecycle_state,
                    ),
                )
            for family in catalog.families:
                for index, task_id in enumerate(family.members):
                    connection.execute(
                        """
                        INSERT OR IGNORE INTO catalog_family_members(
                            catalog_id, family_id, task_id, member_order
                        ) VALUES (?, ?, ?, ?)
                        """,
                        (catalog.catalog_id, family.family_id, task_id, index),
                    )
            for module in catalog.modules:
                connection.execute(
                    """
                    INSERT OR IGNORE INTO catalog_modules(
                        catalog_id, path, basename, module_name, module_role,
                        owner_task_id, legacy_manifest_role, chapter
                    ) VALUES (?, ?, ?, ?, ?, NULLIF(?, ''), ?, ?)
                    """,
                    (
                        catalog.catalog_id,
                        module.path,
                        module.basename,
                        module.module_name,
                        module.module_role,
                        module.owner_task_id,
                        module.legacy_manifest_role,
                        module.chapter,
                    ),
                )
            for cohort_id, members in sorted(catalog.cohorts.items()):
                for task_id in members:
                    connection.execute(
                        """
                        INSERT OR IGNORE INTO catalog_cohorts(catalog_id, cohort_id, task_id)
                        VALUES (?, ?, ?)
                        """,
                        (catalog.catalog_id, cohort_id, task_id),
                    )
            if active:
                connection.execute(
                    "INSERT OR REPLACE INTO meta(key, value) VALUES('active_catalog_id', ?)",
                    (catalog.catalog_id,),
                )
                connection.execute(
                    "INSERT OR REPLACE INTO meta(key, value) VALUES('state_model_version', ?)",
                    (str(STATE_MODEL_VERSION),),
                )
        return str(catalog.catalog_id)

    def active_catalog_id(self) -> str:
        if not self.exists:
            return ""
        with self._connection(write=False) as connection:
            present = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = 'catalog_versions'"
            ).fetchone()
            if present is None:
                return ""
            row = connection.execute(
                "SELECT value FROM meta WHERE key = 'active_catalog_id'"
            ).fetchone()
        return str(row["value"]) if row is not None else ""

    def register_evidence_root(
        self,
        *,
        root_path: str | Path,
        root_kind: str,
        active: bool = True,
        detail: Mapping[str, Any] | None = None,
    ) -> str:
        self.initialize()
        resolved = str(Path(root_path).expanduser().resolve())
        root_id = sha256_json(
            {"schema": "toy-apollo.evidence-root.v1", "path": resolved.lower()}
        )
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO evidence_roots(
                    root_id, root_path, root_kind, active, detail_json, registered_at
                ) VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(root_id) DO UPDATE SET
                    root_kind = excluded.root_kind,
                    active = excluded.active,
                    detail_json = excluded.detail_json
                """,
                (
                    root_id,
                    resolved,
                    root_kind,
                    1 if active else 0,
                    json.dumps(dict(detail or {}), ensure_ascii=False, sort_keys=True),
                    utc_now(),
                ),
            )
        return root_id

    @staticmethod
    def _insert_event(
        connection: sqlite3.Connection,
        *,
        event_type: str,
        task_id: str = "",
        subject_id: str = "",
        evidence_path: str | Path = "",
        evidence_hash: str = "",
        occurred_at: str,
        payload: Mapping[str, Any] | None = None,
    ) -> str:
        event_payload = dict(payload or {})
        identity = {
            "schema": "toy-apollo.state-event.v1",
            "event_type": event_type,
            "task_id": task_id,
            "subject_id": subject_id,
            "evidence_path": str(evidence_path),
            "evidence_hash": evidence_hash,
            "occurred_at": occurred_at,
            "payload": event_payload,
        }
        event_id = sha256_json(identity)
        connection.execute(
            """
            INSERT OR IGNORE INTO state_events(
                event_id, event_type, task_id, subject_id, evidence_path,
                evidence_hash, occurred_at, payload_json, imported_at
            ) VALUES (?, ?, ?, NULLIF(?, ''), ?, ?, ?, ?, ?)
            """,
            (
                event_id,
                event_type,
                task_id,
                subject_id,
                str(evidence_path),
                evidence_hash,
                occurred_at,
                json.dumps(event_payload, ensure_ascii=False, sort_keys=True),
                utc_now(),
            ),
        )
        return event_id

    def record_event(
        self,
        *,
        event_type: str,
        task_id: str = "",
        subject_id: str = "",
        evidence_path: str | Path = "",
        evidence_hash: str = "",
        occurred_at: str | None = None,
        payload: Mapping[str, Any] | None = None,
    ) -> str:
        self.initialize()
        with self._connection(write=True) as connection:
            return self._insert_event(
                connection,
                event_type=event_type,
                task_id=task_id,
                subject_id=subject_id,
                evidence_path=evidence_path,
                evidence_hash=evidence_hash,
                occurred_at=occurred_at or utc_now(),
                payload=payload,
            )

    def record_dataset_snapshot(
        self,
        *,
        dataset_id: str,
        schema_version: str,
        catalog_id: str,
        payload_path: str | Path = "",
        payload_hash: str,
        invariants: Mapping[str, Any] | None = None,
        created_at: str | None = None,
    ) -> str:
        """Register one immutable, content-addressed analysis snapshot."""

        self.initialize()
        serialized_invariants = json.dumps(
            dict(invariants or {}), ensure_ascii=False, sort_keys=True
        )
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT OR IGNORE INTO dataset_snapshots(
                    dataset_id, schema_version, catalog_id, payload_path,
                    payload_hash, invariants_json, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    dataset_id,
                    schema_version,
                    catalog_id,
                    str(payload_path),
                    payload_hash,
                    serialized_invariants,
                    created_at or utc_now(),
                ),
            )
            row = connection.execute(
                """
                SELECT schema_version, catalog_id, payload_hash, invariants_json
                FROM dataset_snapshots
                WHERE dataset_id = ?
                """,
                (dataset_id,),
            ).fetchone()
        if row is None or (
            str(row["schema_version"]) != schema_version
            or str(row["catalog_id"]) != catalog_id
            or str(row["payload_hash"]) != payload_hash
            or str(row["invariants_json"]) != serialized_invariants
        ):
            raise StateIntegrityError(f"Dataset snapshot identity collision for {dataset_id}.")
        return dataset_id

    def backup(self, *, label: str = "migration") -> Path:
        if not self.exists:
            raise StateDatabaseMissingError(f"Cannot back up missing state database: {self.path}")
        self.assert_integrity()
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        target = self.path.with_name(f"{self.path.stem}.backup-{label}-{stamp}{self.path.suffix}")
        with self._connection(write=False) as source, closing(sqlite3.connect(target)) as destination:
            source.backup(destination)
        return target

    def replace_from(self, rebuilt_path: Path, *, backup_label: str = "rebuild") -> Path | None:
        rebuilt = WorkspaceStateStore(rebuilt_path)
        rebuilt.assert_integrity()
        backup_path = self.backup(label=backup_label) if self.exists else None
        self.path.parent.mkdir(parents=True, exist_ok=True)
        os.replace(rebuilt.path, self.path)
        self.assert_integrity()
        return backup_path

    def load_campaign_ledger(self, campaign_id: str) -> tuple[dict[str, Any], int] | None:
        if not self.exists:
            return None
        with self._connection(write=False) as connection:
            row = connection.execute(
                "SELECT ledger_json, revision FROM campaign_ledgers WHERE campaign_id = ?",
                (campaign_id,),
            ).fetchone()
        if row is None:
            return None
        payload = json.loads(row["ledger_json"])
        if not isinstance(payload, dict):
            raise StateIntegrityError(f"Campaign {campaign_id!r} does not contain a JSON object ledger.")
        return payload, int(row["revision"])

    def import_campaign_ledger(
        self,
        *,
        campaign_id: str,
        artifact_root: str | Path,
        ledger: Mapping[str, Any],
        legacy_ledger_path: str | Path = "",
        imported_from: str = "",
    ) -> int:
        self.initialize()
        serialized = json.dumps(dict(ledger), ensure_ascii=False, sort_keys=True)
        now = utc_now()
        owns_transaction = self._bulk_connection is None
        with self._connection(write=True) as connection:
            if owns_transaction:
                connection.execute("BEGIN IMMEDIATE")
            row = connection.execute(
                "SELECT revision FROM campaign_ledgers WHERE campaign_id = ?",
                (campaign_id,),
            ).fetchone()
            if row is None:
                connection.execute(
                    """
                    INSERT INTO campaign_ledgers(
                        campaign_id, artifact_root, legacy_ledger_path, ledger_json,
                        revision, imported_from, updated_at
                    ) VALUES (?, ?, ?, ?, 1, ?, ?)
                    """,
                    (
                        campaign_id,
                        str(Path(artifact_root).resolve()),
                        str(legacy_ledger_path),
                        serialized,
                        imported_from,
                        now,
                    ),
                )
                revision = 1
            else:
                revision = int(row["revision"])
            if owns_transaction:
                connection.execute("COMMIT")
        return revision

    def mutate_campaign_ledger(
        self,
        *,
        campaign_id: str,
        artifact_root: str | Path,
        mutator: Callable[[dict[str, Any]], T],
        legacy_ledger_path: str | Path = "",
    ) -> tuple[dict[str, Any], int, T]:
        self.initialize()
        with self._connection(write=True) as connection:
            try:
                connection.execute("BEGIN IMMEDIATE")
                row = connection.execute(
                    "SELECT ledger_json, revision FROM campaign_ledgers WHERE campaign_id = ?",
                    (campaign_id,),
                ).fetchone()
                if row is None:
                    ledger: dict[str, Any] = {"tasks": {}, "symbols": {}}
                    revision = 0
                else:
                    ledger = json.loads(row["ledger_json"])
                    revision = int(row["revision"])
                if not isinstance(ledger, dict):
                    raise StateIntegrityError(f"Campaign {campaign_id!r} ledger is not an object.")
                result = mutator(ledger)
                serialized = json.dumps(ledger, ensure_ascii=False, sort_keys=True)
                next_revision = revision + 1
                connection.execute(
                    """
                    INSERT INTO campaign_ledgers(
                        campaign_id, artifact_root, legacy_ledger_path, ledger_json,
                        revision, imported_from, updated_at
                    ) VALUES (?, ?, ?, ?, ?, '', ?)
                    ON CONFLICT(campaign_id) DO UPDATE SET
                        artifact_root = excluded.artifact_root,
                        legacy_ledger_path = excluded.legacy_ledger_path,
                        ledger_json = excluded.ledger_json,
                        revision = excluded.revision,
                        updated_at = excluded.updated_at
                    """,
                    (
                        campaign_id,
                        str(Path(artifact_root).resolve()),
                        str(legacy_ledger_path),
                        serialized,
                        next_revision,
                        utc_now(),
                    ),
                )
                connection.execute("COMMIT")
                return ledger, next_revision, result
            except Exception:
                connection.execute("ROLLBACK")
                raise

    def mutate_campaign_with_normalized_state(
        self,
        *,
        campaign_id: str,
        artifact_root: str | Path,
        expected_revision: int,
        ledger_mutator: Callable[[dict[str, Any]], T],
        normalized_mutator: Callable[["WorkspaceStateStore", dict[str, Any], T], None],
        legacy_ledger_path: str | Path = "",
    ) -> tuple[dict[str, Any], int, T]:
        """Atomically CAS one campaign row and its normalized authority rows.

        This path intentionally retains the database's normal DELETE/FULL
        durability settings.  It is for small authority mutations, not rebuilds.
        """

        if self._bulk_connection is not None:
            raise StateConcurrencyError("Nested normalized state transactions are not supported.")
        self.initialize()
        connection = self._connect(write=True)
        try:
            connection.execute("BEGIN IMMEDIATE")
            row = connection.execute(
                "SELECT ledger_json, revision FROM campaign_ledgers WHERE campaign_id = ?",
                (campaign_id,),
            ).fetchone()
            if row is None:
                raise StateConcurrencyError(
                    f"Campaign {campaign_id!r} is missing; initialize operational state first."
                )
            current_revision = int(row["revision"])
            if current_revision != int(expected_revision):
                raise StateConcurrencyError(
                    f"Campaign ledger changed since load: expected revision {expected_revision}, "
                    f"current revision {current_revision}."
                )
            ledger = json.loads(row["ledger_json"])
            if not isinstance(ledger, dict):
                raise StateIntegrityError(f"Campaign {campaign_id!r} ledger is not an object.")
            self._bulk_connection = connection
            result = ledger_mutator(ledger)
            normalized_mutator(self, ledger, result)
            next_revision = current_revision + 1
            cursor = connection.execute(
                """
                UPDATE campaign_ledgers
                SET artifact_root = ?, legacy_ledger_path = ?, ledger_json = ?,
                    revision = ?, updated_at = ?
                WHERE campaign_id = ? AND revision = ?
                """,
                (
                    str(Path(artifact_root).resolve()),
                    str(legacy_ledger_path),
                    json.dumps(ledger, ensure_ascii=False, sort_keys=True),
                    next_revision,
                    utc_now(),
                    campaign_id,
                    current_revision,
                ),
            )
            if cursor.rowcount != 1:
                raise StateConcurrencyError("Campaign ledger CAS update did not apply.")
            connection.execute("COMMIT")
            return ledger, next_revision, result
        except Exception:
            if connection.in_transaction:
                connection.execute("ROLLBACK")
            raise
        finally:
            self._bulk_connection = None
            connection.close()

    def run_record(self, run_id: str) -> dict[str, Any] | None:
        if not self.exists:
            return None
        with self._connection(write=False) as connection:
            row = connection.execute(
                "SELECT * FROM runs WHERE run_id = ?",
                (run_id,),
            ).fetchone()
        return dict(row) if row is not None else None

    def save_campaign_ledger(
        self,
        *,
        campaign_id: str,
        artifact_root: str | Path,
        ledger: Mapping[str, Any],
        expected_revision: int | None,
        legacy_ledger_path: str | Path = "",
    ) -> int:
        self.initialize()
        with self._connection(write=True) as connection:
            try:
                connection.execute("BEGIN IMMEDIATE")
                row = connection.execute(
                    "SELECT revision FROM campaign_ledgers WHERE campaign_id = ?",
                    (campaign_id,),
                ).fetchone()
                current_revision = int(row["revision"]) if row else 0
                if expected_revision is not None and current_revision != expected_revision:
                    raise StateConcurrencyError(
                        f"Campaign ledger changed since load: expected revision {expected_revision}, "
                        f"current revision {current_revision}."
                    )
                next_revision = current_revision + 1
                connection.execute(
                    """
                    INSERT INTO campaign_ledgers(
                        campaign_id, artifact_root, legacy_ledger_path, ledger_json,
                        revision, imported_from, updated_at
                    ) VALUES (?, ?, ?, ?, ?, '', ?)
                    ON CONFLICT(campaign_id) DO UPDATE SET
                        artifact_root = excluded.artifact_root,
                        legacy_ledger_path = excluded.legacy_ledger_path,
                        ledger_json = excluded.ledger_json,
                        revision = excluded.revision,
                        updated_at = excluded.updated_at
                    """,
                    (
                        campaign_id,
                        str(Path(artifact_root).resolve()),
                        str(legacy_ledger_path),
                        json.dumps(dict(ledger), ensure_ascii=False, sort_keys=True),
                        next_revision,
                        utc_now(),
                    ),
                )
                connection.execute("COMMIT")
                return next_revision
            except Exception:
                connection.execute("ROLLBACK")
                raise

    def upsert_subject(self, subject: SubjectBundle) -> str:
        self.initialize()
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT OR IGNORE INTO subjects(
                    subject_id, task_id, subject_kind, source_repo, source_commit,
                    layout, bundle_hash, primary_hash, primary_git_sha, primary_path, manifest_json,
                    parent_subject_id, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, NULLIF(?, ''), ?)
                """,
                (
                    subject.subject_id,
                    subject.task_id,
                    subject.subject_kind,
                    subject.source_repo,
                    subject.source_commit,
                    subject.layout,
                    subject.bundle_hash,
                    subject.primary_hash,
                    subject.primary_git_sha(),
                    subject.primary_path,
                    json.dumps(subject.manifest(), ensure_ascii=False, sort_keys=True),
                    subject.parent_subject_id,
                    subject.created_at or utc_now(),
                ),
            )
            row = connection.execute(
                "SELECT task_id, bundle_hash, primary_hash FROM subjects WHERE subject_id = ?",
                (subject.subject_id,),
            ).fetchone()
            self._insert_event(
                connection,
                event_type="subject_observed",
                task_id=subject.task_id,
                subject_id=subject.subject_id,
                occurred_at=subject.created_at or utc_now(),
                payload={
                    "subject_kind": subject.subject_kind,
                    "source_repo": subject.source_repo,
                    "source_commit": subject.source_commit,
                    "layout": subject.layout,
                    "bundle_hash": subject.bundle_hash,
                    "primary_hash": subject.primary_hash,
                    "primary_path": subject.primary_path,
                    "file_count": len(subject.files),
                },
            )
        if row is None or row["task_id"] != subject.task_id or row["bundle_hash"] != subject.bundle_hash:
            raise StateIntegrityError(f"Subject identity collision for {subject.subject_id}.")
        return subject.subject_id

    def record_review(
        self,
        *,
        task_id: str,
        subject_id: str,
        verdict: str,
        proof_class: str,
        completion_class: str,
        phase2_status: str,
        evidence_path: str | Path,
        evidence_hash: str,
        reviewer_independence: str = "",
        authority_scope: str = "phase2_review_apply",
        authority_eligible: bool = False,
        reviewed_at: str | None = None,
        prompt_version: int | None = None,
        rubric_version: int | None = None,
        review_input_path: str | Path = "",
        review_input_hash: str = "",
        reviewer_backend_id: str = "",
        provenance: Mapping[str, Any] | None = None,
    ) -> str:
        self.initialize()
        with self._connection(write=self._bulk_connection is not None) as connection:
            subject_row = connection.execute(
                "SELECT task_id FROM subjects WHERE subject_id = ?", (subject_id,)
            ).fetchone()
        if subject_row is None:
            raise StateIntegrityError(f"Review subject does not exist: {subject_id}.")
        if subject_row["task_id"] != task_id:
            raise StateIntegrityError(
                f"Review task {task_id} does not match subject task {subject_row['task_id']}."
            )
        identity = {
            "schema": "toy-apollo.review.v1",
            "task_id": task_id,
            "subject_id": subject_id,
            "evidence_hash": evidence_hash,
            "authority_scope": authority_scope,
        }
        review_id = sha256_json(identity)
        resolved_reviewed_at = reviewed_at or utc_now()
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO reviews(
                    review_id, task_id, subject_id, verdict, proof_class,
                    completion_class, phase2_status, evidence_path, evidence_hash,
                    reviewer_independence, authority_scope, authority_eligible, reviewed_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT DO UPDATE SET
                    verdict = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.verdict ELSE reviews.verdict END,
                    proof_class = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.proof_class ELSE reviews.proof_class END,
                    completion_class = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.completion_class ELSE reviews.completion_class END,
                    phase2_status = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.phase2_status
                        WHEN reviews.phase2_status = '' THEN excluded.phase2_status
                        ELSE reviews.phase2_status END,
                    evidence_path = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.evidence_path ELSE reviews.evidence_path END,
                    reviewer_independence = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.reviewer_independence ELSE reviews.reviewer_independence END,
                    authority_scope = CASE
                        WHEN excluded.authority_eligible > reviews.authority_eligible
                        THEN excluded.authority_scope ELSE reviews.authority_scope END,
                    authority_eligible = MAX(reviews.authority_eligible, excluded.authority_eligible),
                    reviewed_at = MAX(reviews.reviewed_at, excluded.reviewed_at)
                """,
                (
                    review_id,
                    task_id,
                    subject_id,
                    verdict,
                    proof_class,
                    completion_class,
                    phase2_status,
                    str(evidence_path),
                    evidence_hash,
                    reviewer_independence,
                    authority_scope,
                    1 if authority_eligible else 0,
                    resolved_reviewed_at,
                ),
            )
            row = connection.execute(
                """
                SELECT review_id, task_id, subject_id, evidence_hash
                FROM reviews
                WHERE review_id = ? OR (subject_id = ? AND evidence_hash = ?)
                ORDER BY authority_eligible DESC
                LIMIT 1
                """,
                (review_id, subject_id, evidence_hash),
            ).fetchone()
            resolved_review_id = str(row["review_id"]) if row is not None else review_id
            connection.execute(
                """
                INSERT INTO review_metadata(
                    review_id, prompt_version, rubric_version, review_input_path,
                    review_input_hash, reviewer_backend_id, provenance_json
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(review_id) DO UPDATE SET
                    prompt_version = COALESCE(excluded.prompt_version, review_metadata.prompt_version),
                    rubric_version = COALESCE(excluded.rubric_version, review_metadata.rubric_version),
                    review_input_path = CASE
                        WHEN excluded.review_input_path != '' THEN excluded.review_input_path
                        ELSE review_metadata.review_input_path END,
                    review_input_hash = CASE
                        WHEN excluded.review_input_hash != '' THEN excluded.review_input_hash
                        ELSE review_metadata.review_input_hash END,
                    reviewer_backend_id = CASE
                        WHEN excluded.reviewer_backend_id != '' THEN excluded.reviewer_backend_id
                        ELSE review_metadata.reviewer_backend_id END,
                    provenance_json = CASE
                        WHEN excluded.provenance_json != '{}' THEN excluded.provenance_json
                        ELSE review_metadata.provenance_json END
                """,
                (
                    resolved_review_id,
                    prompt_version,
                    rubric_version,
                    str(review_input_path),
                    review_input_hash,
                    reviewer_backend_id,
                    json.dumps(dict(provenance or {}), ensure_ascii=False, sort_keys=True),
                ),
            )
            self._insert_event(
                connection,
                event_type="review_evaluated",
                task_id=task_id,
                subject_id=subject_id,
                evidence_path=evidence_path,
                evidence_hash=evidence_hash,
                occurred_at=resolved_reviewed_at,
                payload={
                    "review_id": resolved_review_id,
                    "verdict": verdict,
                    "phase2_status": phase2_status,
                    "authority_scope": authority_scope,
                    "authority_eligible": bool(authority_eligible),
                    "prompt_version": prompt_version,
                    "rubric_version": rubric_version,
                },
            )
        if row is None or row["task_id"] != task_id or row["subject_id"] != subject_id:
            raise StateIntegrityError(f"Review identity collision for {review_id}.")
        return str(row["review_id"])

    def record_transformation(
        self,
        *,
        task_id: str,
        source_subject_id: str,
        target_subject_id: str,
        transformation_kind: str,
        mechanical_status: str,
        build_status: str = "",
        evidence_path: str | Path = "",
        evidence_hash: str = "",
        identity_schema: str = LEGACY_TRANSFORMATION_SCHEMA,
    ) -> str:
        self.initialize()
        identity = {
            "schema": identity_schema,
            "source": source_subject_id,
            "target": target_subject_id,
            "kind": transformation_kind,
        }
        transformation_id = sha256_json(identity)
        created_at = utc_now()
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO transformations(
                    transformation_id, task_id, source_subject_id, target_subject_id,
                    transformation_kind, mechanical_status, build_status,
                    evidence_path, evidence_hash, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(transformation_id) DO UPDATE SET
                    mechanical_status = excluded.mechanical_status,
                    build_status = excluded.build_status,
                    evidence_path = excluded.evidence_path,
                    evidence_hash = excluded.evidence_hash
                """,
                (
                    transformation_id,
                    task_id,
                    source_subject_id,
                    target_subject_id,
                    transformation_kind,
                    mechanical_status,
                    build_status,
                    str(evidence_path),
                    evidence_hash,
                    created_at,
                ),
            )
            self._insert_event(
                connection,
                event_type="subject_transformed",
                task_id=task_id,
                subject_id=target_subject_id,
                evidence_path=evidence_path,
                evidence_hash=evidence_hash,
                occurred_at=created_at,
                payload={
                    "transformation_id": transformation_id,
                    "source_subject_id": source_subject_id,
                    "target_subject_id": target_subject_id,
                    "transformation_kind": transformation_kind,
                    "mechanical_status": mechanical_status,
                    "build_status": build_status,
                },
            )
        return transformation_id

    def record_evidence_bridge_binding(
        self,
        *,
        source: SubjectBundle,
        target: SubjectBundle,
        bridge_route: str,
        authority_type: str,
        capability: str,
        decision_path: str | Path,
        decision_hash: str,
        evidence_path: str | Path,
        evidence_hash: str,
        created_at: str,
        record_import: bool = True,
        transformation_identity_schema: str = LEGACY_TRANSFORMATION_SCHEMA,
        binding_identity_schema: str = "toy-apollo.typed-authority-binding.v1",
    ) -> tuple[str, str]:
        """Atomically import one immutable mechanical authority edge.

        This deliberately does not touch ``reviews`` or ``task_heads``.  The
        typed capability describes why the target may be consumed; it is not
        a target semantic-review verdict.
        """

        routes = {
            "kenneth_author_exact_bridge": {"kenneth_git_author_exact"},
            "reviewed_mat_sync_reassembly_bridge": {
                "historical_review_apply_recovery",
                "mat_exact_review_apply",
                "mat_sync_author_attested_selection",
            },
        }
        capabilities = {
            "kenneth_git_author_exact": "author_current_exact_acceptance",
            "historical_review_apply_recovery": "reviewed_source_mechanical_projection",
            "mat_exact_review_apply": "reviewed_source_mechanical_projection",
            "mat_sync_author_attested_selection": "sync_author_attested_acceptance",
        }
        if source.task_id != target.task_id:
            raise StateIntegrityError("Evidence bridge source and target tasks differ.")
        if bridge_route not in routes or authority_type not in routes[bridge_route]:
            raise StateIntegrityError("Evidence bridge route/authority type is outside the closed registry.")
        if capabilities.get(authority_type) != capability:
            raise StateIntegrityError("Evidence bridge typed capability does not match its authority.")
        if not re.fullmatch(r"[0-9a-f]{64}", decision_hash) or not re.fullmatch(
            r"[0-9a-f]{64}", evidence_hash
        ):
            raise StateIntegrityError("Evidence bridge decision/evidence hashes must be SHA-256.")
        if not created_at:
            raise StateIntegrityError("Evidence bridge lacks an immutable creation time.")

        transformation_id = sha256_json(
            {
                "schema": transformation_identity_schema,
                "source": source.subject_id,
                "target": target.subject_id,
                "kind": "verified_evidence_bridge",
            }
        )
        binding_id = sha256_json(
            {
                "schema": binding_identity_schema,
                "task_id": target.task_id,
                "source_subject_id": source.subject_id,
                "target_subject_id": target.subject_id,
                "bridge_route": bridge_route,
                "authority_type": authority_type,
                "capability": capability,
                "decision_hash": decision_hash,
                "evidence_hash": evidence_hash,
            }
        )
        self.initialize()
        with self.atomic_write("evidence_bridge_item") as connection:
            for subject in (source, target):
                connection.execute(
                    """
                    INSERT OR IGNORE INTO subjects(
                        subject_id, task_id, subject_kind, source_repo, source_commit,
                        layout, bundle_hash, primary_hash, primary_git_sha, primary_path,
                        manifest_json, parent_subject_id, created_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, NULLIF(?, ''), ?)
                    """,
                    (
                        subject.subject_id, subject.task_id, subject.subject_kind,
                        subject.source_repo, subject.source_commit, subject.layout,
                        subject.bundle_hash, subject.primary_hash, subject.primary_git_sha(),
                        subject.primary_path,
                        json.dumps(subject.manifest(), ensure_ascii=False, sort_keys=True),
                        subject.parent_subject_id, subject.created_at or created_at,
                    ),
                )
                row = connection.execute(
                    """
                    SELECT task_id, subject_kind, source_repo, source_commit, layout,
                           bundle_hash, primary_hash, primary_path, manifest_json
                    FROM subjects WHERE subject_id = ?
                    """,
                    (subject.subject_id,),
                ).fetchone()
                expected = {
                    "task_id": subject.task_id, "subject_kind": subject.subject_kind,
                    "source_repo": subject.source_repo, "source_commit": subject.source_commit,
                    "layout": subject.layout, "bundle_hash": subject.bundle_hash,
                    "primary_hash": subject.primary_hash, "primary_path": subject.primary_path,
                    "manifest_json": json.dumps(subject.manifest(), ensure_ascii=False, sort_keys=True),
                }
                if row is None or any(str(row[key]) != str(value) for key, value in expected.items()):
                    raise StateIntegrityError(f"Evidence bridge subject collision for {subject.subject_id}.")

            connection.execute(
                """
                INSERT OR IGNORE INTO transformations(
                    transformation_id, task_id, source_subject_id, target_subject_id,
                    transformation_kind, mechanical_status, build_status,
                    evidence_path, evidence_hash, created_at
                ) VALUES (?, ?, ?, ?, 'verified_evidence_bridge', 'pass', 'pass', ?, ?, ?)
                """,
                (
                    transformation_id, target.task_id, source.subject_id, target.subject_id,
                    stable_absolute_path(evidence_path), evidence_hash, created_at,
                ),
            )
            transformation = connection.execute(
                "SELECT * FROM transformations WHERE transformation_id = ?",
                (transformation_id,),
            ).fetchone()
            expected_transformation = {
                "task_id": target.task_id, "source_subject_id": source.subject_id,
                "target_subject_id": target.subject_id,
                "transformation_kind": "verified_evidence_bridge",
                "mechanical_status": "pass", "build_status": "pass",
                "evidence_path": stable_absolute_path(evidence_path),
                "evidence_hash": evidence_hash,
            }
            if transformation is None or any(
                str(transformation[key]) != str(value)
                for key, value in expected_transformation.items()
            ):
                raise StateIntegrityError("Evidence bridge transformation identity collision.")

            connection.execute(
                """
                INSERT OR IGNORE INTO authority_bindings(
                    binding_id, task_id, source_subject_id, target_subject_id,
                    transformation_id, bridge_route, authority_type, capability,
                    decision_path, decision_hash, evidence_path, evidence_hash, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    binding_id, target.task_id, source.subject_id, target.subject_id,
                    transformation_id, bridge_route, authority_type, capability,
                    stable_absolute_path(decision_path), decision_hash,
                    stable_absolute_path(evidence_path), evidence_hash, created_at,
                ),
            )
            binding = connection.execute(
                "SELECT * FROM authority_bindings WHERE binding_id = ?",
                (binding_id,),
            ).fetchone()
            expected_binding = {
                "task_id": target.task_id, "source_subject_id": source.subject_id,
                "target_subject_id": target.subject_id,
                "transformation_id": transformation_id, "bridge_route": bridge_route,
                "authority_type": authority_type, "capability": capability,
                "decision_path": stable_absolute_path(decision_path),
                "decision_hash": decision_hash,
                "evidence_path": stable_absolute_path(evidence_path),
                "evidence_hash": evidence_hash,
            }
            if binding is None or any(
                str(binding[key]) != str(value) for key, value in expected_binding.items()
            ):
                raise StateIntegrityError("Evidence bridge authority identity collision.")

            if record_import:
                source_path = stable_absolute_path(evidence_path)
                connection.execute(
                    """
                    INSERT OR IGNORE INTO imports(
                        source_path, source_hash, source_kind, imported_at, record_count
                    ) VALUES (?, ?, 'validated_evidence_bridge_receipt', ?, 1)
                    """,
                    (source_path, evidence_hash, utc_now()),
                )
                imported = connection.execute(
                    "SELECT source_hash, source_kind, record_count FROM imports WHERE source_path = ?",
                    (source_path,),
                ).fetchone()
                if (
                    imported is None or imported["source_hash"] != evidence_hash
                    or imported["source_kind"] != "validated_evidence_bridge_receipt"
                    or int(imported["record_count"]) != 1
                ):
                    raise StateIntegrityError("Evidence bridge import path already binds different bytes.")
            self._insert_event(
                connection,
                event_type="validated_evidence_bridge_imported",
                task_id=target.task_id,
                subject_id=target.subject_id,
                evidence_path=evidence_path,
                evidence_hash=evidence_hash,
                occurred_at=created_at,
                payload={
                    "binding_id": binding_id,
                    "transformation_id": transformation_id,
                    "bridge_route": bridge_route,
                    "authority_type": authority_type,
                    "capability": capability,
                    "source_subject_id": source.subject_id,
                    "target_subject_id": target.subject_id,
                    "semantic_upgrade": False,
                    "rubric_upgrade": False,
                    "creates_review": False,
                },
            )
        return binding_id, transformation_id

    def record_run(
        self,
        *,
        task_id: str,
        operation: str,
        status: str,
        campaign_id: str = "",
        subject_id: str = "",
        artifact_path: str | Path = "",
        detail: Mapping[str, Any] | None = None,
        run_id: str = "",
        started_at: str | None = None,
        updated_at: str | None = None,
        completed_at: str = "",
    ) -> str:
        self.initialize()
        now = utc_now()
        resolved_started_at = started_at or now
        resolved_updated_at = updated_at or now
        resolved_run_id = run_id or sha256_json(
            {
                "schema": "toy-apollo.run.v1",
                "task_id": task_id,
                "operation": operation,
                "campaign_id": campaign_id,
                "artifact_path": str(artifact_path),
                "started_at": resolved_started_at,
            }
        )
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO runs(
                    run_id, campaign_id, task_id, operation, status, subject_id,
                    artifact_path, detail_json, started_at, updated_at, completed_at
                ) VALUES (?, ?, ?, ?, ?, NULLIF(?, ''), ?, ?, ?, ?, ?)
                ON CONFLICT(run_id) DO UPDATE SET
                    status = excluded.status,
                    subject_id = excluded.subject_id,
                    artifact_path = excluded.artifact_path,
                    detail_json = excluded.detail_json,
                    updated_at = excluded.updated_at,
                    completed_at = excluded.completed_at
                """,
                (
                    resolved_run_id,
                    campaign_id,
                    task_id,
                    operation,
                    status,
                    subject_id,
                    str(artifact_path),
                    json.dumps(dict(detail or {}), ensure_ascii=False, sort_keys=True),
                    resolved_started_at,
                    resolved_updated_at,
                    completed_at,
                ),
            )
            self._insert_event(
                connection,
                event_type="run_state_changed",
                task_id=task_id,
                subject_id=subject_id,
                evidence_path=artifact_path,
                occurred_at=completed_at or resolved_updated_at,
                payload={
                    "run_id": resolved_run_id,
                    "campaign_id": campaign_id,
                    "operation": operation,
                    "status": status,
                    "detail": dict(detail or {}),
                },
            )
        return resolved_run_id

    def record_integration(
        self,
        *,
        task_id: str,
        target_repo: str,
        integration_kind: str,
        state: str,
        subject_id: str = "",
        branch: str = "",
        pr_number: int | None = None,
        head_sha: str = "",
        merge_sha: str = "",
        head_subject_id: str = "",
        observed_at: str | None = None,
        remote_freshness: str = "unknown",
        detail: Mapping[str, Any] | None = None,
        integration_id: str = "",
    ) -> str:
        self.initialize()
        resolved_id = integration_id or sha256_json(
            {
                "schema": "toy-apollo.integration.v1",
                "task_id": task_id,
                "target_repo": target_repo,
                "kind": integration_kind,
                "pr_number": pr_number,
                "branch": branch,
                "subject_id": subject_id,
            }
        )
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO integrations(
                    integration_id, task_id, subject_id, target_repo,
                    integration_kind, state, branch, pr_number, head_sha,
                    merge_sha, head_subject_id, observed_at, remote_freshness,
                    detail_json
                ) VALUES (?, ?, NULLIF(?, ''), ?, ?, ?, ?, ?, ?, ?, NULLIF(?, ''), ?, ?, ?)
                ON CONFLICT(integration_id) DO UPDATE SET
                    subject_id = excluded.subject_id,
                    state = excluded.state,
                    branch = excluded.branch,
                    pr_number = excluded.pr_number,
                    head_sha = excluded.head_sha,
                    merge_sha = excluded.merge_sha,
                    head_subject_id = excluded.head_subject_id,
                    observed_at = excluded.observed_at,
                    remote_freshness = excluded.remote_freshness,
                    detail_json = excluded.detail_json
                """,
                (
                    resolved_id,
                    task_id,
                    subject_id,
                    target_repo,
                    integration_kind,
                    state,
                    branch,
                    pr_number,
                    head_sha,
                    merge_sha,
                    head_subject_id,
                    observed_at or utc_now(),
                    remote_freshness,
                    json.dumps(dict(detail or {}), ensure_ascii=False, sort_keys=True),
                ),
            )
        return resolved_id

    def claim_next_integration(
        self,
        *,
        integration_kind: str,
        target_repo: str,
        worker_id: str,
    ) -> dict[str, Any] | None:
        self.initialize()
        with self._connection(write=True) as connection:
            try:
                connection.execute("BEGIN IMMEDIATE")
                row = connection.execute(
                    """
                    SELECT * FROM integrations
                    WHERE integration_kind = ? AND target_repo = ? AND state = 'ready'
                      AND NOT EXISTS (
                          SELECT 1 FROM dependency_pins pin
                          WHERE pin.consumer_task_id = integrations.task_id
                            AND pin.state != 'validated'
                      )
                    ORDER BY observed_at, integration_id
                    LIMIT 1
                    """,
                    (integration_kind, target_repo),
                ).fetchone()
                if row is None:
                    connection.execute("COMMIT")
                    return None
                claimed_at = utc_now()
                cursor = connection.execute(
                    """
                    UPDATE integrations
                    SET state = 'claimed', claimed_by = ?, claimed_at = ?
                    WHERE integration_id = ? AND state = 'ready'
                    """,
                    (worker_id, claimed_at, row["integration_id"]),
                )
                if cursor.rowcount != 1:
                    raise StateConcurrencyError("Promotion queue item was claimed by another worker.")
                connection.execute("COMMIT")
                payload = dict(row)
                payload.update({"state": "claimed", "claimed_by": worker_id, "claimed_at": claimed_at})
                return payload
            except Exception:
                connection.execute("ROLLBACK")
                raise

    def finish_integration(
        self,
        *,
        integration_id: str,
        worker_id: str,
        state: str,
        detail: Mapping[str, Any] | None = None,
    ) -> None:
        if state not in {"completed", "failed", "cancelled"}:
            raise ValueError("Integration terminal state must be completed, failed, or cancelled.")
        self.initialize()
        with self._connection(write=True) as connection:
            cursor = connection.execute(
                """
                UPDATE integrations
                SET state = ?, observed_at = ?, detail_json = ?
                WHERE integration_id = ? AND state = 'claimed' AND claimed_by = ?
                """,
                (
                    state,
                    utc_now(),
                    json.dumps(dict(detail or {}), ensure_ascii=False, sort_keys=True),
                    integration_id,
                    worker_id,
                ),
            )
            if cursor.rowcount != 1:
                raise StateConcurrencyError("Integration is not claimed by this worker.")

    def pin_dependency_candidate(
        self,
        *,
        consumer_task_id: str,
        dependency_task_id: str,
        subject_id: str,
        required_role: str = "mat_main",
        detail: Mapping[str, Any] | None = None,
    ) -> None:
        self.initialize()
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO dependency_pins(
                    consumer_task_id, dependency_task_id, subject_id,
                    required_role, state, created_at, detail_json
                ) VALUES (?, ?, ?, ?, 'waiting', ?, ?)
                ON CONFLICT(consumer_task_id, dependency_task_id) DO UPDATE SET
                    subject_id = excluded.subject_id,
                    required_role = excluded.required_role,
                    state = 'waiting',
                    created_at = excluded.created_at,
                    validated_at = '',
                    detail_json = excluded.detail_json
                """,
                (
                    consumer_task_id,
                    dependency_task_id,
                    subject_id,
                    required_role,
                    utc_now(),
                    json.dumps(dict(detail or {}), ensure_ascii=False, sort_keys=True),
                ),
            )
        self.revalidate_dependency_pins(consumer_task_id=consumer_task_id)

    def revalidate_dependency_pins(self, *, consumer_task_id: str = "") -> list[dict[str, Any]]:
        if not self.exists:
            return []
        clause = "WHERE pin.consumer_task_id = ?" if consumer_task_id else ""
        parameters: tuple[Any, ...] = (consumer_task_id,) if consumer_task_id else ()
        with self._connection(write=True) as connection:
            rows = connection.execute(
                f"""
                SELECT pin.*, pinned.bundle_hash AS pinned_bundle_hash,
                       head.subject_id AS current_subject_id,
                       current.bundle_hash AS current_bundle_hash
                FROM dependency_pins pin
                JOIN subjects pinned ON pinned.subject_id = pin.subject_id
                LEFT JOIN task_heads head
                  ON head.task_id = pin.dependency_task_id
                 AND head.role = pin.required_role
                 AND head.freshness IN ('fresh', 'local')
                LEFT JOIN subjects current ON current.subject_id = head.subject_id
                {clause}
                ORDER BY pin.consumer_task_id, pin.dependency_task_id
                """,
                parameters,
            ).fetchall()
            results: list[dict[str, Any]] = []
            for row in rows:
                if not row["current_subject_id"]:
                    state = "waiting"
                elif row["current_bundle_hash"] == row["pinned_bundle_hash"]:
                    state = "validated"
                else:
                    state = "mismatch"
                validated_at = utc_now() if state == "validated" else ""
                connection.execute(
                    """
                    UPDATE dependency_pins
                    SET state = ?, validated_at = ?
                    WHERE consumer_task_id = ? AND dependency_task_id = ?
                    """,
                    (state, validated_at, row["consumer_task_id"], row["dependency_task_id"]),
                )
                payload = dict(row)
                payload.update({"state": state, "validated_at": validated_at})
                results.append(payload)
            return results

    def set_task_head(
        self,
        *,
        task_id: str,
        role: str,
        subject_id: str,
        observed_at: str | None = None,
        freshness: str = "fresh",
        detail: Mapping[str, Any] | None = None,
    ) -> None:
        self.initialize()
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO task_heads(task_id, role, subject_id, observed_at, freshness, detail_json)
                VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(task_id, role) DO UPDATE SET
                    subject_id = excluded.subject_id,
                    observed_at = excluded.observed_at,
                    freshness = excluded.freshness,
                    detail_json = excluded.detail_json
                """,
                (
                    task_id,
                    role,
                    subject_id,
                    observed_at or utc_now(),
                    freshness,
                    json.dumps(dict(detail or {}), ensure_ascii=False, sort_keys=True),
                ),
            )

    def mark_task_head_freshness(self, *, task_id: str, role: str, freshness: str) -> None:
        if not self.exists:
            return
        with self._connection(write=True) as connection:
            connection.execute(
                "UPDATE task_heads SET freshness = ?, observed_at = ? WHERE task_id = ? AND role = ?",
                (freshness, utc_now(), task_id, role),
            )

    def mark_role_freshness(self, *, role: str, freshness: str) -> None:
        if not self.exists:
            return
        with self._connection(write=True) as connection:
            connection.execute(
                "UPDATE task_heads SET freshness = ?, observed_at = ? WHERE role = ?",
                (freshness, utc_now(), role),
            )

    def mark_integrations_freshness(self, *, target_repo: str, freshness: str) -> None:
        if not self.exists:
            return
        with self._connection(write=True) as connection:
            connection.execute(
                "UPDATE integrations SET remote_freshness = ?, observed_at = ? WHERE target_repo = ?",
                (freshness, utc_now(), target_repo),
            )

    def mark_imported(
        self,
        *,
        source_path: Path,
        source_kind: str,
        record_count: int,
        source_hash: str = "",
    ) -> None:
        self.initialize()
        with self._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO imports(source_path, source_hash, source_kind, imported_at, record_count)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(source_path) DO UPDATE SET
                    source_hash = excluded.source_hash,
                    source_kind = excluded.source_kind,
                    imported_at = excluded.imported_at,
                    record_count = excluded.record_count
                """,
                (
                    stable_absolute_path(source_path),
                    source_hash or sha256_file(source_path),
                    source_kind,
                    utc_now(),
                    int(record_count),
                ),
            )

    def mark_imported_many(
        self,
        records: Iterable[tuple[Path, str, str, int]],
    ) -> None:
        """Register already-hashed evidence paths with one SQLite statement."""

        prepared = [
            (
                stable_absolute_path(source_path),
                source_hash,
                source_kind,
                utc_now(),
                int(record_count),
            )
            for source_path, source_hash, source_kind, record_count in records
        ]
        if not prepared:
            return
        if any(not row[1] for row in prepared):
            raise ValueError("Bulk import registration requires precomputed source hashes.")
        self.initialize()
        with self._connection(write=True) as connection:
            connection.executemany(
                """
                INSERT INTO imports(source_path, source_hash, source_kind, imported_at, record_count)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(source_path) DO UPDATE SET
                    source_hash = excluded.source_hash,
                    source_kind = excluded.source_kind,
                    imported_at = excluded.imported_at,
                    record_count = excluded.record_count
                """,
                prepared,
            )

    def import_is_current(self, source_path: Path, *, source_hash: str = "") -> bool:
        if not self.exists or (not source_hash and not source_path.is_file()):
            return False
        with self._connection(write=self._bulk_connection is not None) as connection:
            row = connection.execute(
                "SELECT source_hash FROM imports WHERE source_path = ?",
                (stable_absolute_path(source_path),),
            ).fetchone()
        return bool(row and row["source_hash"] == (source_hash or sha256_file(source_path)))

    def eligible_review_basis(
        self,
        *,
        task_id: str,
        evidence_hash: str,
        primary_hash: str,
    ) -> dict[str, Any] | None:
        """Return an applied pass that may serve as a scope-rebind basis."""

        if not self.exists:
            return None
        with self._connection(write=self._bulk_connection is not None) as connection:
            row = connection.execute(
                f"""
                SELECT r.*, s.primary_hash, s.bundle_hash,
                       m.prompt_version, m.rubric_version,
                       m.review_input_path, m.review_input_hash,
                       m.reviewer_backend_id, m.provenance_json
                FROM reviews r
                JOIN subjects s ON s.subject_id = r.subject_id
                JOIN review_metadata m ON m.review_id = r.review_id
                WHERE r.task_id = ?
                  AND r.evidence_hash = ?
                  AND s.primary_hash = ?
                  AND r.verdict = 'pass'
                  AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND {self._prompt_version_pred()}
                  AND {self._rubric_version_pred()}
                ORDER BY r.reviewed_at DESC
                LIMIT 1
                """,
                (task_id, evidence_hash, primary_hash),
            ).fetchone()
        return dict(row) if row is not None else None

    def review_coverage(self, subject_id: str) -> dict[str, Any] | None:
        if not self.exists:
            return None
        with self._connection(write=False) as connection:
            present = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name='authority_bindings'"
            ).fetchone()
            if present is None:
                return None
            subject = connection.execute(
                "SELECT task_id, bundle_hash FROM subjects WHERE subject_id = ?",
                (subject_id,),
            ).fetchone()
            if subject is None:
                return None
            row = connection.execute(
                f"""
                SELECT r.*, 'exact_bundle' AS coverage_kind,
                       ? AS covered_subject_id
                FROM reviews r
                JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
                LEFT JOIN review_metadata m ON m.review_id = r.review_id
                WHERE reviewed.task_id = ? AND reviewed.bundle_hash = ?
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND (
                    r.authority_scope = 'kenneth_pr_exact_head_review'
                    OR ({self._prompt_version_pred()} AND {self._rubric_version_pred()})
                  )
                ORDER BY r.reviewed_at DESC
                LIMIT 1
                """,
                (subject_id, subject["task_id"], subject["bundle_hash"]),
            ).fetchone()
            if row is not None:
                return dict(row)
            row = connection.execute(
                f"""
                SELECT r.*, t.transformation_kind AS coverage_kind,
                       t.mechanical_status, t.build_status, t.transformation_id
                FROM transformations t
                JOIN reviews r ON r.subject_id = t.source_subject_id
                JOIN subjects transformed ON transformed.subject_id = t.target_subject_id
                LEFT JOIN review_metadata m ON m.review_id = r.review_id
                WHERE transformed.task_id = ? AND transformed.bundle_hash = ?
                  AND t.mechanical_status = 'pass'
                  AND (t.build_status = 'pass' OR t.build_status = 'not_required')
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND (
                    r.authority_scope = 'kenneth_pr_exact_head_review'
                    OR ({self._prompt_version_pred()} AND {self._rubric_version_pred()})
                  )
                ORDER BY r.reviewed_at DESC
                LIMIT 1
                """,
                (subject["task_id"], subject["bundle_hash"]),
            ).fetchone()
        return dict(row) if row is not None else None

    def authority_coverage(self, subject_id: str) -> dict[str, Any] | None:
        """Return typed mechanical authority without calling it a review."""

        if not self.exists:
            return None
        with self._connection(write=False) as connection:
            subject = connection.execute(
                "SELECT task_id, bundle_hash FROM subjects WHERE subject_id = ?",
                (subject_id,),
            ).fetchone()
            if subject is None:
                return None
            row = connection.execute(
                """
                SELECT b.*, t.mechanical_status, t.build_status,
                       'typed_evidence_bridge' AS coverage_kind,
                       ? AS covered_subject_id
                FROM valid_authority_bindings_v2 b
                JOIN transformations t ON t.transformation_id = b.transformation_id
                JOIN subjects target ON target.subject_id = b.target_subject_id
                WHERE b.target_subject_id = ?
                  AND target.task_id = ? AND target.bundle_hash = ?
                ORDER BY b.created_at DESC, b.binding_id
                LIMIT 1
                """,
                (subject_id, subject_id, subject["task_id"], subject["bundle_hash"]),
            ).fetchone()
        return dict(row) if row is not None else None

    def validate_authority_bindings(self) -> dict[str, Any]:
        """Read-only relational checks for the typed bridge authority table."""

        if not self.exists:
            return {"valid": True, "schema_present": False, "count": 0, "violations": []}
        capability_by_type = {
            "kenneth_git_author_exact": "author_current_exact_acceptance",
            "historical_review_apply_recovery": "reviewed_source_mechanical_projection",
            "mat_exact_review_apply": "reviewed_source_mechanical_projection",
            "mat_sync_author_attested_selection": "sync_author_attested_acceptance",
        }
        violations: list[str] = []
        with self._connection(write=False) as connection:
            present = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name='authority_bindings'"
            ).fetchone()
            if present is None:
                return {"valid": True, "schema_present": False, "count": 0, "violations": []}
            rows = connection.execute(
                """
                SELECT b.*, source.task_id AS source_task,
                       target.task_id AS target_task,
                       target.source_repo AS target_repo,
                       target.layout AS target_layout,
                       t.task_id AS transformation_task,
                       t.source_subject_id AS transformation_source,
                       t.target_subject_id AS transformation_target,
                       t.transformation_kind, t.mechanical_status, t.build_status,
                       r.review_id AS target_review_id
                FROM authority_bindings b
                JOIN subjects source ON source.subject_id = b.source_subject_id
                JOIN subjects target ON target.subject_id = b.target_subject_id
                JOIN transformations t ON t.transformation_id = b.transformation_id
                LEFT JOIN reviews r
                  ON r.subject_id = b.target_subject_id
                 AND r.evidence_hash = b.evidence_hash
                ORDER BY b.binding_id
                """
            ).fetchall()
        for row in rows:
            binding_id = str(row["binding_id"])
            expected_route = {
                "kenneth_git_author_exact": "kenneth_author_exact_bridge",
                "historical_review_apply_recovery": "reviewed_mat_sync_reassembly_bridge",
                "mat_exact_review_apply": "reviewed_mat_sync_reassembly_bridge",
                "mat_sync_author_attested_selection": "reviewed_mat_sync_reassembly_bridge",
            }.get(str(row["authority_type"]))
            if row["bridge_route"] != expected_route:
                violations.append(f"{binding_id}:route_authority_mismatch")
            if row["capability"] != capability_by_type.get(str(row["authority_type"])):
                violations.append(f"{binding_id}:capability_authority_mismatch")
            if not (
                row["task_id"] == row["source_task"] == row["target_task"]
                == row["transformation_task"]
            ):
                violations.append(f"{binding_id}:task_mismatch")
            if (
                row["source_subject_id"] != row["transformation_source"]
                or row["target_subject_id"] != row["transformation_target"]
                or row["transformation_kind"] != "verified_evidence_bridge"
                or row["mechanical_status"] != "pass"
                or row["build_status"] != "pass"
            ):
                violations.append(f"{binding_id}:transformation_mismatch")
            supported_target = str(row["target_repo"]).lower() == "mat" or (
                str(row["target_repo"]).lower() == "probabilitytheoryformalization"
                and str(row["target_layout"]).lower() == "unified"
            )
            if not supported_target:
                violations.append(f"{binding_id}:target_not_mat")
            if (
                not str(row["decision_path"])
                or re.fullmatch(r"[0-9a-f]{64}", str(row["decision_hash"])) is None
                or not str(row["evidence_path"])
                or re.fullmatch(r"[0-9a-f]{64}", str(row["evidence_hash"])) is None
            ):
                violations.append(f"{binding_id}:evidence_binding_malformed")
            if row["target_review_id"] is not None:
                violations.append(f"{binding_id}:bridge_evidence_created_target_review")
        return {
            "valid": not violations, "schema_present": True,
            "count": len(rows), "violations": violations,
        }

    def partial_review_coverage(self, subject_id: str) -> dict[str, Any] | None:
        """Return honest legacy evidence that binds the primary file but not the full bundle.

        This is deliberately not review coverage: it cannot authorize promotion.  It
        exists so status reports do not erase an applied legacy review merely because
        the older artifact format failed to hash every task-owned support file.
        """

        if not self.exists:
            return None
        with self._connection(write=False) as connection:
            subject = connection.execute(
                "SELECT task_id, bundle_hash, primary_hash FROM subjects WHERE subject_id = ?",
                (subject_id,),
            ).fetchone()
            if subject is None:
                return None
            row = connection.execute(
                f"""
                SELECT r.*, reviewed.bundle_hash AS reviewed_bundle_hash,
                       reviewed.primary_hash AS reviewed_primary_hash,
                       'primary_only_bundle_mismatch' AS coverage_kind,
                       ? AS compared_subject_id
                FROM reviews r
                JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
                LEFT JOIN review_metadata m ON m.review_id = r.review_id
                WHERE reviewed.task_id = ?
                  AND reviewed.primary_hash = ?
                  AND reviewed.bundle_hash != ?
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                  AND (
                    r.authority_scope = 'kenneth_pr_exact_head_review'
                    OR ({self._prompt_version_pred()} AND {self._rubric_version_pred()})
                  )
                ORDER BY r.reviewed_at DESC
                LIMIT 1
                """,
                (
                    subject_id,
                    subject["task_id"],
                    subject["primary_hash"],
                    subject["bundle_hash"],
                ),
            ).fetchone()
        return dict(row) if row is not None else None

    def task_report(self, task_id: str, *, verify_integrity: bool = True) -> dict[str, Any]:
        if not self.exists:
            return {"task_id": task_id, "database_status": "missing", "actions": ["state_rebuild_required"]}
        if verify_integrity:
            self.assert_integrity()
        with self._connection(write=False) as connection:
            catalog_row = None
            cohort_rows: list[sqlite3.Row] = []
            catalog_table = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = 'catalog_tasks'"
            ).fetchone()
            if catalog_table is not None:
                active_catalog = connection.execute(
                    "SELECT value FROM meta WHERE key = 'active_catalog_id'"
                ).fetchone()
                if active_catalog is not None:
                    catalog_row = connection.execute(
                        """
                        SELECT * FROM catalog_tasks
                        WHERE catalog_id = ? AND task_id = ?
                        """,
                        (active_catalog["value"], task_id),
                    ).fetchone()
                    cohort_rows = connection.execute(
                        """
                        SELECT cohort_id FROM catalog_cohorts
                        WHERE catalog_id = ? AND task_id = ?
                        ORDER BY cohort_id
                        """,
                        (active_catalog["value"], task_id),
                    ).fetchall()
            head_rows = connection.execute(
                """
                SELECT h.*, s.subject_kind, s.source_repo, s.source_commit,
                       s.layout, s.bundle_hash, s.primary_hash, s.primary_git_sha, s.primary_path,
                       s.manifest_json
                FROM task_heads h
                JOIN subjects s ON s.subject_id = h.subject_id
                WHERE h.task_id = ?
                ORDER BY h.role
                """,
                (task_id,),
            ).fetchall()
            review_rows = connection.execute(
                """
                SELECT r.*, s.bundle_hash, s.primary_hash, s.source_repo, s.layout
                FROM reviews r JOIN subjects s ON s.subject_id = r.subject_id
                WHERE r.task_id = ?
                ORDER BY r.reviewed_at DESC
                """,
                (task_id,),
            ).fetchall()
            integration_rows = connection.execute(
                """
                SELECT i.*,
                       head.bundle_hash AS head_bundle_hash,
                       head.primary_hash AS head_primary_hash,
                       head.primary_git_sha AS head_primary_git_sha,
                       subject.bundle_hash AS subject_bundle_hash,
                       subject.primary_hash AS subject_primary_hash,
                       subject.primary_git_sha AS subject_primary_git_sha
                FROM integrations i
                LEFT JOIN subjects head ON head.subject_id = i.head_subject_id
                LEFT JOIN subjects subject ON subject.subject_id = i.subject_id
                WHERE i.task_id = ?
                ORDER BY i.observed_at DESC
                """,
                (task_id,),
            ).fetchall()
            run_rows = connection.execute(
                "SELECT * FROM runs WHERE task_id = ? ORDER BY updated_at DESC LIMIT 10",
                (task_id,),
            ).fetchall()
            pin_rows = connection.execute(
                """
                SELECT pin.*, pinned.bundle_hash AS pinned_bundle_hash
                FROM dependency_pins pin
                JOIN subjects pinned ON pinned.subject_id = pin.subject_id
                WHERE pin.consumer_task_id = ?
                ORDER BY pin.dependency_task_id
                """,
                (task_id,),
            ).fetchall()
        heads = {str(row["role"]): dict(row) for row in head_rows}
        current_heads = {
            role: head
            for role, head in heads.items()
            if str(head.get("freshness", "")) in {"fresh", "local"}
        }
        actions: list[str] = []
        def same_primary(left: Mapping[str, Any], right: Mapping[str, Any]) -> bool:
            left_git = str(left.get("primary_git_sha", "") or left.get("head_primary_git_sha", "") or "")
            right_git = str(right.get("primary_git_sha", "") or right.get("head_primary_git_sha", "") or "")
            if left_git and right_git:
                return left_git == right_git
            return str(left.get("primary_hash", "") or "") == str(right.get("primary_hash", "") or "")
        candidate = current_heads.get("mat_candidate") or current_heads.get("local_review_candidate")
        mat_main = current_heads.get("mat_main")
        kenneth_main = current_heads.get("kenneth_main")
        candidate_coverage = self.review_coverage(candidate["subject_id"]) if candidate else None
        candidate_authority = self.authority_coverage(candidate["subject_id"]) if candidate else None
        candidate_partial_review = (
            self.partial_review_coverage(candidate["subject_id"])
            if candidate and candidate_coverage is None and candidate_authority is None
            else None
        )
        if candidate:
            if candidate_coverage is None and candidate_authority is None:
                actions.append(
                    "review_scope_rebind_required" if candidate_partial_review else "needs_review"
                )
            elif not mat_main or mat_main["bundle_hash"] != candidate["bundle_hash"]:
                actions.append("reviewed_not_promoted_to_mat")
        head_review_coverage = {
            role: coverage
            for role, head in current_heads.items()
            if (coverage := self.review_coverage(head["subject_id"])) is not None
        }
        head_authority_coverage = {
            role: coverage
            for role, head in current_heads.items()
            if role not in head_review_coverage
            and (coverage := self.authority_coverage(head["subject_id"])) is not None
        }
        head_partial_review_coverage = {
            role: partial
            for role, head in current_heads.items()
            if role not in head_review_coverage
            and (partial := self.partial_review_coverage(head["subject_id"])) is not None
        }
        current_coverages = sorted(
            head_review_coverage.values(),
            key=lambda row: str(row.get("reviewed_at", "")),
            reverse=True,
        )
        latest_current_review = current_coverages[0] if current_coverages else None
        kenneth_integrations = [dict(row) for row in integration_rows if row["target_repo"] == "kenneth"]
        reviewed_mat = None
        if candidate and candidate_coverage:
            reviewed_mat = candidate
        elif mat_main and head_review_coverage.get("mat_main"):
            reviewed_mat = mat_main
        if reviewed_mat and kenneth_main and not same_primary(reviewed_mat, kenneth_main):
            open_kenneth_pr = next(
                (row for row in kenneth_integrations if row.get("state") == "open"), None
            )
            matching = [
                row
                for row in kenneth_integrations
                if (
                    row.get("subject_id") == reviewed_mat["subject_id"]
                    or (
                        row.get("head_primary_git_sha")
                        and row.get("head_primary_git_sha") == reviewed_mat.get("primary_git_sha")
                    )
                    or row.get("head_primary_hash") == reviewed_mat["primary_hash"]
                )
                and row.get("state") in {"ready", "claimed", "open", "merged"}
            ]
            if not matching and open_kenneth_pr is None:
                actions.append("reviewed_ready_for_pr")
        if kenneth_integrations and reviewed_mat:
            open_pr = next((row for row in kenneth_integrations if row["state"] == "open"), None)
            if (
                open_pr
                and open_pr.get("head_subject_id")
                and not same_primary(open_pr, reviewed_mat)
            ):
                actions.append("pr_behind_reviewed_local")
        if mat_main and kenneth_main and not same_primary(mat_main, kenneth_main):
            actions.append("upstream_changed_requires_reconciliation")
        if heads.get("kenneth_main", {}).get("freshness") == "unavailable":
            actions.append("kenneth_refresh_unavailable")
        dependency_pins = [dict(row) for row in pin_rows]
        if any(pin["state"] == "waiting" for pin in dependency_pins):
            actions.append("dependency_pin_waiting")
        if any(pin["state"] == "mismatch" for pin in dependency_pins):
            actions.append("dependency_pin_changed_requires_revalidation")
        active_runs = [dict(row) for row in run_rows if row["status"] in {"active", "running", "claimed"}]
        if catalog_row is not None:
            if not current_heads:
                actions.append("current_subject_missing")
            elif (
                not head_review_coverage
                and not head_authority_coverage
                and not head_partial_review_coverage
            ):
                actions.append("current_bundle_review_missing")
            if not review_rows:
                actions.append("review_history_missing")
        report = {
            "task_id": task_id,
            "database_status": "ok",
            "heads": heads,
            "current_heads": current_heads,
            "latest_review": dict(review_rows[0]) if review_rows else None,
            "latest_current_review": latest_current_review,
            "head_review_coverage": head_review_coverage,
            "head_authority_coverage": head_authority_coverage,
            "head_partial_review_coverage": head_partial_review_coverage,
            "candidate_review_coverage": candidate_coverage,
            "candidate_authority_coverage": candidate_authority,
            "candidate_partial_review": candidate_partial_review,
            "integrations": [dict(row) for row in integration_rows],
            "active_runs": active_runs,
            "dependency_pins": dependency_pins,
            "catalog_task": dict(catalog_row) if catalog_row is not None else None,
            "catalog_cohorts": [str(row["cohort_id"]) for row in cohort_rows],
            "actions": list(dict.fromkeys(actions)),
        }
        return report

    def worklist(self) -> list[dict[str, Any]]:
        if not self.exists:
            return [{"task_id": "*", "actions": ["state_rebuild_required"]}]
        self.assert_integrity()
        with self._connection(write=False) as connection:
            catalog_table = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = 'catalog_tasks'"
            ).fetchone()
            active_catalog = (
                connection.execute("SELECT value FROM meta WHERE key = 'active_catalog_id'").fetchone()
                if catalog_table is not None
                else None
            )
            if active_catalog is not None:
                rows = connection.execute(
                    """
                    SELECT task_id FROM catalog_tasks WHERE catalog_id = ?
                    UNION SELECT task_id FROM subjects
                    UNION SELECT task_id FROM reviews
                    UNION SELECT task_id FROM runs
                    UNION SELECT task_id FROM integrations
                    UNION SELECT task_id FROM task_heads
                    UNION SELECT consumer_task_id AS task_id FROM dependency_pins
                    ORDER BY task_id
                    """,
                    (active_catalog["value"],),
                ).fetchall()
            else:
                rows = connection.execute(
                    """
                    SELECT task_id FROM subjects
                    UNION SELECT task_id FROM reviews
                    UNION SELECT task_id FROM runs
                    UNION SELECT task_id FROM integrations
                    UNION SELECT task_id FROM task_heads
                    UNION SELECT consumer_task_id AS task_id FROM dependency_pins
                    ORDER BY task_id
                    """
                ).fetchall()
        reports = [
            self.task_report(str(row["task_id"]), verify_integrity=False) for row in rows
        ]
        return [report for report in reports if report.get("actions") or report.get("active_runs")]

    @classmethod
    def temporary_rebuild_store(cls, target: Path) -> "WorkspaceStateStore":
        target.parent.mkdir(parents=True, exist_ok=True)
        fd, raw_path = tempfile.mkstemp(prefix=f".{target.stem}.rebuild-", suffix=target.suffix, dir=target.parent)
        os.close(fd)
        temp_path = Path(raw_path)
        temp_path.unlink(missing_ok=True)
        store = cls(temp_path)
        store.initialize()
        return store


def copy_state_database(source: Path, target: Path) -> None:
    """Copy a closed database for diagnostics/tests; normal backups use SQLite backup()."""

    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
