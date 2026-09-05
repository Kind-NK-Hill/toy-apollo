from __future__ import annotations

import json
from pathlib import Path

from ..state_store import canonical_subject_bytes, sha256_bytes


class LegacySupportProjectionError(RuntimeError):
    """Raised when immutable v1 support-projection evidence is invalid."""


def read_legacy_support_projection(runtime_root: Path, task_id: str) -> dict[str, bytes]:
    """Read a v1 support projection without writing or treating it as current authority."""

    root = runtime_root.resolve()
    projection_path = (
        root / "phase2_prompt_packs" / task_id / "subject_support_projection.json"
    )
    if not projection_path.is_file():
        return {}
    try:
        projection = json.loads(projection_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LegacySupportProjectionError(
            f"Invalid legacy support projection {projection_path}: {exc}"
        ) from exc
    if not isinstance(projection, dict):
        raise LegacySupportProjectionError(
            f"Legacy support projection must be an object: {projection_path}"
        )
    if projection.get("schema_version") != "toy-apollo.subject-support-projection.v1":
        raise LegacySupportProjectionError(
            f"Unsupported legacy support projection schema: {projection_path}"
        )
    if str(projection.get("task_id", "") or "") != task_id:
        raise LegacySupportProjectionError(
            f"Legacy support projection task mismatch: {projection_path}"
        )
    files = projection.get("files")
    if not isinstance(files, list) or not files:
        raise LegacySupportProjectionError(
            f"Legacy support projection needs a non-empty files list: {projection_path}"
        )
    support: dict[str, bytes] = {}
    for entry in files:
        if not isinstance(entry, dict):
            raise LegacySupportProjectionError(
                f"Legacy support projection file entry must be an object: {projection_path}"
            )
        logical_path = str(entry.get("path", "") or "").replace("\\", "/")
        expected_hash = str(entry.get("content_sha256", "") or "").lower()
        if not logical_path.startswith("ToyApollo/Output/") or not logical_path.endswith(".lean"):
            raise LegacySupportProjectionError(
                f"Legacy projected support has an invalid path: {logical_path}"
            )
        projected_path = (root / logical_path).resolve()
        try:
            projected_path.relative_to(root)
        except ValueError as exc:
            raise LegacySupportProjectionError(
                f"Legacy projected support escapes runtime root: {logical_path}"
            ) from exc
        if not projected_path.is_file():
            raise LegacySupportProjectionError(
                f"Legacy projected support file is missing: {logical_path}"
            )
        payload = projected_path.read_bytes()
        actual_hash = sha256_bytes(canonical_subject_bytes(logical_path, payload))
        if not expected_hash or actual_hash != expected_hash:
            raise LegacySupportProjectionError(
                f"Legacy projected support hash mismatch for {logical_path}: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        support[logical_path] = payload
    return support
