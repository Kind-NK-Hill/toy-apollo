from __future__ import annotations

import hashlib
import json
import os
import shutil
import sqlite3
import tempfile
from contextlib import closing, contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, TypeVar


SCHEMA_VERSION = 1
DEFAULT_BUSY_TIMEOUT_MS = 10_000


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


def canonical_state_path(runtime_root: str | Path) -> Path:
    runtime = Path(runtime_root).expanduser().resolve()
    state_dir_name = "toy-apollo-artifacts" if runtime.name.lower() == "toy-apollo" else f"{runtime.name}-artifacts"
    return runtime.parent / state_dir_name / "state.sqlite3"


def refuse_legacy_ledger_write(runtime_root: str | Path, *, operation: str) -> None:
    root = Path(runtime_root).expanduser().resolve()
    candidates = [canonical_state_path(root), root / "state.sqlite3"]
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


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
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
        identity = {
            "schema": "toy-apollo.subject.v1",
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
        identity = {
            "schema": "toy-apollo.subject.v1",
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
            "schema": "toy-apollo.subject.v1",
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
        )

    def manifest(self) -> list[dict[str, Any]]:
        return [item.as_dict() for item in self.files]

    def primary_git_sha(self) -> str:
        return next((item.git_blob_sha for item in self.files if item.path == self.primary_path), "")


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
"""


class WorkspaceStateStore:
    """One workspace-level state database with immutable evidence bindings.

    The database owns current projections and cross-repository relationships.
    Large review/build artifacts remain files; rows retain their absolute path
    and hash so the database can be rebuilt without copying artifact contents.
    """

    def __init__(self, path: str | Path, *, busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS):
        self.path = Path(path).expanduser().resolve()
        self.busy_timeout_ms = int(busy_timeout_ms)
        self._initialized = False
        self._bulk_connection: sqlite3.Connection | None = None

    @staticmethod
    def validate_canonical_path(path: Path, *, runtime_root: Path, artifact_root: Path) -> None:
        resolved = path.resolve()
        runtime = runtime_root.resolve()
        artifact = artifact_root.resolve()
        expected = canonical_state_path(runtime).resolve()
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
                return int(connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0])

            version_row = connection.execute("SELECT value FROM meta WHERE key = 'schema_version'").fetchone()
            return {
                "path": str(self.path),
                "schema_version": int(version_row[0]) if version_row else 0,
                "campaign_ledgers": count("campaign_ledgers"),
                "subjects": count("subjects"),
                "reviews": count("reviews"),
                "runs": count("runs"),
                "integrations": count("integrations"),
                "task_heads": count("task_heads"),
                "dependency_pins": count("dependency_pins"),
                "imports": count("imports"),
            }

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
                    reviewed_at or utc_now(),
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
    ) -> str:
        self.initialize()
        identity = {
            "schema": "toy-apollo.transformation.v1",
            "source": source_subject_id,
            "target": target_subject_id,
            "kind": transformation_kind,
        }
        transformation_id = sha256_json(identity)
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
                    utc_now(),
                ),
            )
        return transformation_id

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
        completed_at: str = "",
    ) -> str:
        self.initialize()
        now = utc_now()
        resolved_run_id = run_id or sha256_json(
            {
                "schema": "toy-apollo.run.v1",
                "task_id": task_id,
                "operation": operation,
                "campaign_id": campaign_id,
                "artifact_path": str(artifact_path),
                "started_at": started_at or now,
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
                    started_at or now,
                    now,
                    completed_at,
                ),
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

    def mark_imported(self, *, source_path: Path, source_kind: str, record_count: int) -> None:
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
                (str(source_path.resolve()), sha256_file(source_path), source_kind, utc_now(), int(record_count)),
            )

    def import_is_current(self, source_path: Path) -> bool:
        if not self.exists or not source_path.is_file():
            return False
        with self._connection(write=self._bulk_connection is not None) as connection:
            row = connection.execute(
                "SELECT source_hash FROM imports WHERE source_path = ?",
                (str(source_path.resolve()),),
            ).fetchone()
        return bool(row and row["source_hash"] == sha256_file(source_path))

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
                """
                SELECT r.*, s.primary_hash, s.bundle_hash
                FROM reviews r
                JOIN subjects s ON s.subject_id = r.subject_id
                WHERE r.task_id = ?
                  AND r.evidence_hash = ?
                  AND s.primary_hash = ?
                  AND r.verdict = 'pass'
                  AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
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
            subject = connection.execute(
                "SELECT task_id, bundle_hash FROM subjects WHERE subject_id = ?",
                (subject_id,),
            ).fetchone()
            if subject is None:
                return None
            row = connection.execute(
                """
                SELECT r.*, 'exact_bundle' AS coverage_kind,
                       ? AS covered_subject_id
                FROM reviews r
                JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
                WHERE reviewed.task_id = ? AND reviewed.bundle_hash = ?
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                ORDER BY r.reviewed_at DESC
                LIMIT 1
                """,
                (subject_id, subject["task_id"], subject["bundle_hash"]),
            ).fetchone()
            if row is not None:
                return dict(row)
            row = connection.execute(
                """
                SELECT r.*, t.transformation_kind AS coverage_kind,
                       t.mechanical_status, t.build_status, t.transformation_id
                FROM transformations t
                JOIN reviews r ON r.subject_id = t.source_subject_id
                JOIN subjects transformed ON transformed.subject_id = t.target_subject_id
                WHERE transformed.task_id = ? AND transformed.bundle_hash = ?
                  AND t.mechanical_status = 'pass'
                  AND (t.build_status = 'pass' OR t.build_status = 'not_required')
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
                ORDER BY r.reviewed_at DESC
                LIMIT 1
                """,
                (subject["task_id"], subject["bundle_hash"]),
            ).fetchone()
        return dict(row) if row is not None else None

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
                """
                SELECT r.*, reviewed.bundle_hash AS reviewed_bundle_hash,
                       reviewed.primary_hash AS reviewed_primary_hash,
                       'primary_only_bundle_mismatch' AS coverage_kind,
                       ? AS compared_subject_id
                FROM reviews r
                JOIN subjects reviewed ON reviewed.subject_id = r.subject_id
                WHERE reviewed.task_id = ?
                  AND reviewed.primary_hash = ?
                  AND reviewed.bundle_hash != ?
                  AND r.verdict = 'pass' AND r.phase2_status = 'pass'
                  AND r.authority_eligible = 1
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
        candidate_partial_review = (
            self.partial_review_coverage(candidate["subject_id"])
            if candidate and candidate_coverage is None
            else None
        )
        if candidate:
            if candidate_coverage is None:
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
        report = {
            "task_id": task_id,
            "database_status": "ok",
            "heads": heads,
            "current_heads": current_heads,
            "latest_review": dict(review_rows[0]) if review_rows else None,
            "latest_current_review": latest_current_review,
            "head_review_coverage": head_review_coverage,
            "head_partial_review_coverage": head_partial_review_coverage,
            "candidate_review_coverage": candidate_coverage,
            "candidate_partial_review": candidate_partial_review,
            "integrations": [dict(row) for row in integration_rows],
            "active_runs": active_runs,
            "dependency_pins": dependency_pins,
            "actions": list(dict.fromkeys(actions)),
        }
        return report

    def worklist(self) -> list[dict[str, Any]]:
        if not self.exists:
            return [{"task_id": "*", "actions": ["state_rebuild_required"]}]
        self.assert_integrity()
        with self._connection(write=False) as connection:
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
