from __future__ import annotations

import json
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

from .state_store import StateIntegrityError, WorkspaceStateStore, sha256_json


DATASET_SCHEMA_VERSION = "toy-apollo.analysis-dataset.v2"


@dataclass(frozen=True)
class DatasetSnapshot:
    dataset_id: str
    catalog_id: str
    payload: Mapping[str, Any]
    invariants: Mapping[str, Any]
    payload_path: str = ""

    def as_dict(self) -> dict[str, Any]:
        return {
            "dataset_id": self.dataset_id,
            "schema_version": DATASET_SCHEMA_VERSION,
            "catalog_id": self.catalog_id,
            "payload_hash": self.dataset_id,
            "payload_path": self.payload_path,
            "invariants": dict(self.invariants),
            "counts": dict(self.payload.get("counts", {})),
        }


def _normalize_value(value: Any, *, workspace_root: Path | None) -> Any:
    if isinstance(value, Mapping):
        return {
            str(key): _normalize_value(item, workspace_root=workspace_root)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if isinstance(value, (list, tuple)):
        return [_normalize_value(item, workspace_root=workspace_root) for item in value]
    if not isinstance(value, str):
        return value
    normalized = value.replace("\\", "/")
    if workspace_root is None:
        return normalized
    root = workspace_root.resolve().as_posix().rstrip("/")
    if normalized.lower() == root.lower():
        return "${WORKSPACE}"
    prefix = f"{root}/"
    if normalized.lower().startswith(prefix.lower()):
        return "${WORKSPACE}/" + normalized[len(prefix) :]
    return normalized


def _json_value(raw: Any) -> Any:
    if raw in (None, ""):
        return {} if raw == "" else None
    if not isinstance(raw, str):
        return raw
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return raw


def _rows(
    connection,
    query: str,
    *,
    json_fields: Iterable[str] = (),
    workspace_root: Path | None,
) -> list[dict[str, Any]]:
    parsed_fields = set(json_fields)
    result: list[dict[str, Any]] = []
    for row in connection.execute(query).fetchall():
        item = dict(row)
        for field in parsed_fields:
            if field in item:
                item[field.removesuffix("_json")] = _json_value(item.pop(field))
        result.append(_normalize_value(item, workspace_root=workspace_root))
    return result


def build_dataset_payload(
    store: WorkspaceStateStore,
    *,
    invariants: Mapping[str, Any] | None = None,
    workspace_root: Path | None = None,
) -> dict[str, Any]:
    """Build the stable, analysis-facing projection of one state database.

    Rebuild/import timestamps and local observation timestamps are deliberately
    excluded. Evidence timestamps remain because they describe the historical
    process rather than the act of rebuilding the database.
    """

    store.assert_integrity()
    catalog_id = store.active_catalog_id()
    if not catalog_id:
        raise StateIntegrityError("A dataset snapshot requires an active task catalog.")
    resolved_workspace = workspace_root.resolve() if workspace_root is not None else None
    with store._connection(write=False) as connection:
        catalog_row = connection.execute(
            "SELECT payload_json FROM catalog_versions WHERE catalog_id = ?",
            (catalog_id,),
        ).fetchone()
        if catalog_row is None:
            raise StateIntegrityError(f"Active catalog {catalog_id} is missing.")
        catalog = _normalize_value(
            _json_value(catalog_row["payload_json"]), workspace_root=resolved_workspace
        )
        sections = {
            "campaigns": _rows(
                connection,
                """
                SELECT campaign_id, artifact_root, legacy_ledger_path,
                       revision, imported_from
                FROM campaign_ledgers ORDER BY campaign_id
                """,
                workspace_root=resolved_workspace,
            ),
            "subjects": _rows(
                connection,
                """
                SELECT subject_id, task_id, subject_kind, source_repo,
                       source_commit, layout, bundle_hash, primary_hash,
                       primary_git_sha, primary_path, manifest_json,
                       COALESCE(parent_subject_id, '') AS parent_subject_id
                FROM subjects ORDER BY subject_id
                """,
                json_fields=("manifest_json",),
                workspace_root=resolved_workspace,
            ),
            "evaluations": _rows(
                connection,
                """
                SELECT evaluation_id, task_id, subject_id, verdict, proof_class,
                       completion_class, phase2_status, evidence_path,
                       evidence_hash, reviewer_independence, authority_scope,
                       authority_eligible, reviewed_at, prompt_version,
                       rubric_version, review_input_path, review_input_hash,
                       reviewer_backend_id, provenance_json
                FROM evaluations ORDER BY evaluation_id
                """,
                json_fields=("provenance_json",),
                workspace_root=resolved_workspace,
            ),
            "transformations": _rows(
                connection,
                """
                SELECT transformation_id, task_id, source_subject_id,
                       target_subject_id, transformation_kind,
                       mechanical_status, build_status, evidence_path,
                       evidence_hash
                FROM transformations ORDER BY transformation_id
                """,
                workspace_root=resolved_workspace,
            ),
            "runs": _rows(
                connection,
                """
                SELECT run_id, campaign_id, task_id, operation, status,
                       COALESCE(subject_id, '') AS subject_id, artifact_path,
                       detail_json, started_at, completed_at
                FROM runs ORDER BY run_id
                """,
                json_fields=("detail_json",),
                workspace_root=resolved_workspace,
            ),
            "integrations": _rows(
                connection,
                """
                SELECT integration_id, task_id,
                       COALESCE(subject_id, '') AS subject_id, target_repo,
                       integration_kind, state, branch, pr_number, head_sha,
                       merge_sha, COALESCE(head_subject_id, '') AS head_subject_id,
                       remote_freshness, detail_json
                FROM integrations ORDER BY integration_id
                """,
                json_fields=("detail_json",),
                workspace_root=resolved_workspace,
            ),
            "task_heads": _rows(
                connection,
                """
                SELECT task_id, role, subject_id, freshness, detail_json
                FROM task_heads ORDER BY task_id, role
                """,
                json_fields=("detail_json",),
                workspace_root=resolved_workspace,
            ),
            "dependency_pins": _rows(
                connection,
                """
                SELECT consumer_task_id, dependency_task_id, subject_id,
                       required_role, state, detail_json
                FROM dependency_pins
                ORDER BY consumer_task_id, dependency_task_id
                """,
                json_fields=("detail_json",),
                workspace_root=resolved_workspace,
            ),
            "imports": _rows(
                connection,
                """
                SELECT source_path, source_hash, source_kind, record_count
                FROM imports ORDER BY source_path
                """,
                workspace_root=resolved_workspace,
            ),
            "events": _rows(
                connection,
                """
                SELECT event_id, event_type, task_id,
                       COALESCE(subject_id, '') AS subject_id, evidence_path,
                       evidence_hash, occurred_at, payload_json
                FROM state_events
                WHERE event_type NOT IN ('subject_observed', 'subject_transformed')
                ORDER BY event_id
                """,
                json_fields=("payload_json",),
                workspace_root=resolved_workspace,
            ),
            "evidence_roots": _rows(
                connection,
                """
                SELECT root_id, root_path, root_kind, active, detail_json
                FROM evidence_roots ORDER BY root_id
                """,
                json_fields=("detail_json",),
                workspace_root=resolved_workspace,
            ),
        }
    normalized_invariants = _normalize_value(
        dict(invariants or {}), workspace_root=resolved_workspace
    )
    counts = {name: len(rows) for name, rows in sections.items()}
    return {
        "schema_version": DATASET_SCHEMA_VERSION,
        "catalog_id": catalog_id,
        "catalog": catalog,
        "invariants": normalized_invariants,
        "counts": counts,
        **sections,
    }


def _write_payload(path: Path, payload: Mapping[str, Any]) -> None:
    path = path.expanduser().resolve()
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


def create_dataset_snapshot(
    store: WorkspaceStateStore,
    *,
    invariants: Mapping[str, Any] | None = None,
    workspace_root: Path | None = None,
    output_path: Path | None = None,
    persist: bool = True,
) -> DatasetSnapshot:
    payload = build_dataset_payload(
        store,
        invariants=invariants,
        workspace_root=workspace_root,
    )
    dataset_id = sha256_json(payload)
    written_path = ""
    if output_path is not None:
        resolved = output_path.expanduser().resolve()
        _write_payload(resolved, {"dataset_id": dataset_id, **payload})
        written_path = str(resolved)
    if persist:
        store.record_dataset_snapshot(
            dataset_id=dataset_id,
            schema_version=DATASET_SCHEMA_VERSION,
            catalog_id=str(payload["catalog_id"]),
            payload_path=written_path,
            payload_hash=dataset_id,
            invariants=dict(payload["invariants"]),
        )
    return DatasetSnapshot(
        dataset_id=dataset_id,
        catalog_id=str(payload["catalog_id"]),
        payload=payload,
        invariants=dict(payload["invariants"]),
        payload_path=written_path,
    )
