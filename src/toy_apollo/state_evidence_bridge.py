"""Strict non-semantic evidence bridges for exact author/review authority.

This module is deliberately inspect/validate only.  It can construct a
canonical receipt in memory so fixtures and a later emitter can replay the
contract, but it never publishes a receipt, runs Lean, or writes workspace
state.  State import is owned by :mod:`state_migration`.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
from contextlib import contextmanager
from contextvars import ContextVar
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.block_id_naming import canonicalize_block_id, is_canonical_block_id

from .state_boundary_delta_receipt import (
    BoundaryDeltaReceiptError,
    _atomic_publish_no_replace,
    _bundle_content,
    _consumer_evidence,
    _declaration_signatures,
    _imports_and_payload,
    _normalize_tokens,
    _open_namespaces_and_payload,
    _receipt_match_payload,
    _section_commands_and_payload,
    _target_build,
    _exact_catalog_context,
    _run,
    _validate_context_exact_build,
)
from .state_review_apply_recovery import (
    RECOVERY_SCHEMA,
    validate_historical_review_apply_recovery,
)
from .state_store import SubjectBundle, sha256_file, sha256_json
from .task_catalog import (
    CatalogError,
    TaskCatalog,
    load_catalog,
    validate_catalog_compatible_mat_commit,
)


EVIDENCE_BRIDGE_SCHEMA = "toy-apollo.validated-evidence-bridge-receipt.v1"
EVIDENCE_BRIDGE_INPUT_SCHEMA = "toy-apollo.evidence-bridge-input-manifest.v1"
KENNETH_BATCH_AUTHORITY_SCHEMA = "mat.catalog.kenneth-author-exact-bridge-manifest.v1"
FINAL122_MINIMAL_INDEX_SCHEMA = "mat.catalog.final122-evidence-bridge-minimal-index.v1"
FINAL122_BATCH_RECEIPT_SCHEMA = "toy-apollo.validated-evidence-bridge-batch-receipt.v1"
KENNETH_DECISION_SCHEMA = "toy-apollo.kenneth-author-exact-decision.v1"
MAT_SYNC_DECISION_SCHEMA = "toy-apollo.reviewed-mat-sync-decision.v1"
TRANSFORMATION_KIND = "verified_evidence_bridge"

ROUTE_A = "kenneth_author_exact_bridge"
ROUTE_B = "reviewed_mat_sync_reassembly_bridge"
ROUTES = frozenset({ROUTE_A, ROUTE_B})

AUTHORITY_KENNETH = "kenneth_git_author_exact"
AUTHORITY_RECOVERY = "historical_review_apply_recovery"
AUTHORITY_MAT_APPLY = "mat_exact_review_apply"
AUTHORITY_MAT_SYNC = "mat_sync_author_attested_selection"
AUTHORITY_TYPES = frozenset(
    {AUTHORITY_KENNETH, AUTHORITY_RECOVERY, AUTHORITY_MAT_APPLY, AUTHORITY_MAT_SYNC}
)

CAPABILITY_BY_AUTHORITY = {
    AUTHORITY_KENNETH: "author_current_exact_acceptance",
    AUTHORITY_RECOVERY: "reviewed_source_mechanical_projection",
    AUTHORITY_MAT_APPLY: "reviewed_source_mechanical_projection",
    AUTHORITY_MAT_SYNC: "sync_author_attested_acceptance",
}

_HEX40 = re.compile(r"[0-9a-f]{40}")
_HEX64 = re.compile(r"[0-9a-f]{64}")
_CANONICAL_DECLARATION_EXTRACTOR = "mat.audit.full-named-declaration-token-extractor.v1"
_DECLARATION_SELECTOR_TEMPLATE = (
    r"(?m)^\s*(?:@\[[^\n]+\]\s*)*"
    r"(?:(?:noncomputable|private|protected|unsafe)\s+)*"
    r"(?P<kind>def|abbrev|theorem|lemma|structure|class|inductive)\s+{name}\b"
)
_NEXT_FULL_DECLARATION = re.compile(
    r"(?m)^\s*(?:@\[[^\n]+\]\s*)*"
    r"(?:(?:noncomputable|private|protected|unsafe)\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|instance)\s+[A-Za-z_]"
)
_AUDIT_TOKEN_RE = re.compile(
    r'"(?:\\.|[^"\\])*"|`[^`]*`|'
    r"[A-Za-z_][A-Za-z_0-9\u2080-\u2089\u2070-\u2079\u208a-\u208e"
    r"\u207a-\u207f\u03b1-\u03c9\u0391-\u03a9\u211d\u2115\u2124"
    r"\u2264\u2265\u2200\u2203\u2208\u2209\u2192\u2194\u21d2\u21d4"
    r"\u2205\u2229\u222a\u2211\u220f\u222b\u221e]*|"
    r":=|=>|->|<-|<->|<=|>=|==|!=|[(){}\[\],.:;|+*/^=<>\\-]"
)
_EXACTNESS_MODES = frozenset(
    {"complete_bundle_blob_exact", "author_carrier_blob_exact", "full_named_declaration_exact"}
)
_PAIR_KINDS = ("declaration_pairs", "proof_pairs", "support_pairs")
_PASS_CHECKS = frozenset(
    {
        "source_authority_validated",
        "source_complete_bundle",
        "target_complete_bundle_at_pinned_commit",
        "complete_scope_coverage",
        "ordered_lean_tokens_unchanged",
        "public_declarations_unchanged",
        "proof_support_scope_unchanged",
        "target_build_and_forbidden_scan",
        "direct_consumers_built_and_scanned",
        "no_semantic_or_rubric_upgrade",
    }
)
_SNAPSHOT_RESOLVER: ContextVar[Mapping[str, Mapping[str, str]]] = ContextVar(
    "evidence_bridge_snapshot_resolver", default={},
)


class EvidenceBridgeError(ValueError):
    """A fail-closed evidence bridge rejection with a stable category."""

    def __init__(self, message: str, *, code: str = "R_ROUTE"):
        super().__init__(f"{code}: {message}")
        self.code = code


def _resolved_snapshot(path: Path, expected_sha256: str = "") -> Path:
    entry = _SNAPSHOT_RESOLVER.get().get(str(path.resolve()))
    if not isinstance(entry, Mapping):
        return path.resolve()
    if expected_sha256 and entry.get("sha256") != expected_sha256:
        raise EvidenceBridgeError("snapshot resolver hash mismatch", code="R_IMMUTABILITY")
    return Path(str(entry.get("path", "") or "")).resolve()


@contextmanager
def _snapshot_resolution(
    entries: Sequence[Mapping[str, Any]], *, expected_root: Path | None = None,
):
    resolver: dict[str, dict[str, str]] = {}
    for entry in entries:
        original = entry.get("original"); snapshot = entry.get("snapshot")
        if not isinstance(original, Mapping) or not isinstance(snapshot, Mapping):
            raise EvidenceBridgeError("snapshot graph entry is malformed", code="R_IMMUTABILITY")
        original_path = str(Path(str(original.get("path", "") or "")).resolve())
        snapshot_path = Path(str(snapshot.get("path", "") or "")).resolve()
        digest = str(snapshot.get("sha256", "") or "")
        try:
            data = snapshot_path.read_bytes()
        except OSError as exc:
            raise EvidenceBridgeError(f"cannot read evidence snapshot: {exc}", code="R_IMMUTABILITY") from exc
        if (
            not _HEX64.fullmatch(digest) or hashlib.sha256(data).hexdigest() != digest
            or str(original.get("sha256", "") or "") != digest
            or snapshot_path.stem != digest
            or (expected_root is not None and snapshot_path.parent != expected_root.resolve() / "objects")
            or original_path in resolver
        ):
            raise EvidenceBridgeError("content-addressed snapshot binding mismatch", code="R_IMMUTABILITY")
        resolver[original_path] = {"path": str(snapshot_path), "sha256": digest}
    token = _SNAPSHOT_RESOLVER.set(resolver)
    try:
        yield
    finally:
        _SNAPSHOT_RESOLVER.reset(token)


def _read_json(path: Path, *, label: str) -> Mapping[str, Any]:
    path = _resolved_snapshot(path)
    try:
        data = path.read_bytes()
        if _HEX64.fullmatch(path.stem) and hashlib.sha256(data).hexdigest() != path.stem:
            raise EvidenceBridgeError(f"content-addressed {label} changed: {path}", code="R_IMMUTABILITY")
        payload = json.loads(data.decode("utf-8"))
    except EvidenceBridgeError:
        raise
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceBridgeError(f"cannot read {label} JSON {path}: {exc}", code="R_IMMUTABILITY") from exc
    if not isinstance(payload, Mapping):
        raise EvidenceBridgeError(f"{label} is not a JSON object", code="R_IMMUTABILITY")
    return payload


def _resolve_ref(base: Path, raw: Any, *, label: str) -> tuple[Path, Mapping[str, Any]]:
    if not isinstance(raw, Mapping):
        raise EvidenceBridgeError(f"{label} reference is missing", code="R_IMMUTABILITY")
    path = Path(str(raw.get("path", "") or "")).expanduser()
    path = path if path.is_absolute() else base / path
    expected = str(raw.get("sha256", "") or "")
    path = _resolved_snapshot(path.resolve(), expected)
    try:
        data = path.read_bytes()
        payload = json.loads(data.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceBridgeError(f"cannot read bound {label}: {exc}", code="R_IMMUTABILITY") from exc
    if (
        not _HEX64.fullmatch(expected)
        or hashlib.sha256(data).hexdigest() != expected
        or not isinstance(payload, Mapping)
    ):
        raise EvidenceBridgeError(f"{label} path/hash mismatch", code="R_IMMUTABILITY")
    return path, payload


def _ref(path: Path) -> dict[str, str]:
    resolved = _resolved_snapshot(path)
    try:
        data = resolved.read_bytes()
    except OSError as exc:
        raise EvidenceBridgeError(f"cannot read referenced evidence: {exc}", code="R_IMMUTABILITY") from exc
    return {"path": str(resolved), "sha256": hashlib.sha256(data).hexdigest()}


def _subject(raw: Any, *, task_id: str, label: str) -> SubjectBundle:
    if not isinstance(raw, Mapping):
        raise EvidenceBridgeError(f"{label} subject is missing", code="R_BUNDLE")
    if canonicalize_block_id(str(raw.get("task_id", task_id) or "")) != task_id:
        raise EvidenceBridgeError(f"{label} task mismatch", code="R_BUNDLE")
    try:
        subject = SubjectBundle.from_manifest(
            task_id=task_id,
            files=raw.get("files", raw.get("subject_files", [])),
            primary_path=str(raw.get("primary_path", "") or ""),
            source_repo=str(raw.get("source_repo", "") or ""),
            source_commit=str(raw.get("source_commit", raw.get("commit", "")) or ""),
            layout=str(raw.get("layout", "") or ""),
            subject_kind=str(raw.get("subject_kind", "evidence_bridge_bundle") or "evidence_bridge_bundle"),
        )
    except (TypeError, ValueError) as exc:
        raise EvidenceBridgeError(f"invalid {label} subject: {exc}", code="R_BUNDLE") from exc
    if not subject.source_repo or not subject.layout or not _HEX40.fullmatch(subject.source_commit):
        raise EvidenceBridgeError(f"{label} lacks pinned repository/commit/layout", code="R_BUNDLE")
    for key, actual in (
        ("subject_id", subject.subject_id),
        ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash),
    ):
        if str(raw.get(key, "") or "") != actual:
            raise EvidenceBridgeError(f"{label} {key} mismatch", code="R_BUNDLE")
    if raw.get("files", raw.get("subject_files")) != subject.manifest():
        raise EvidenceBridgeError(f"{label} manifest is not canonical and complete", code="R_BUNDLE")
    return subject


def subject_payload(subject: SubjectBundle) -> dict[str, Any]:
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


def _plain_ref(raw: Any) -> dict[str, str]:
    if not isinstance(raw, Mapping):
        return {"path": "", "sha256": ""}
    return {"path": str(raw.get("path", "") or ""), "sha256": str(raw.get("sha256", "") or "")}


def _assert_exact_subject(actual: SubjectBundle, expected: SubjectBundle, *, label: str) -> None:
    if actual.subject_id != expected.subject_id or actual.manifest() != expected.manifest():
        raise EvidenceBridgeError(f"{label} does not bind the complete source subject", code="R_SOURCE_AUTHORITY")


def _validate_kenneth_decision(
    decision: Mapping[str, Any], *, task_id: str, anchors: Mapping[str, Any],
    source: SubjectBundle, target: SubjectBundle,
) -> dict[str, Any]:
    if decision.get("schema") != KENNETH_DECISION_SCHEMA:
        raise EvidenceBridgeError("unsupported Kenneth author decision schema", code="R_KENNETH")
    if canonicalize_block_id(str(decision.get("task_id", "") or "")) != task_id:
        raise EvidenceBridgeError("Kenneth decision task mismatch", code="R_KENNETH")
    if decision.get("decision_kind") != "author_exact" or decision.get("complete_scope") is not True:
        raise EvidenceBridgeError("Kenneth decision is not complete author_exact", code="R_KENNETH")
    mode = str(decision.get("exactness_mode", "") or "")
    if mode not in _EXACTNESS_MODES:
        raise EvidenceBridgeError("unknown Kenneth exactness mode", code="R_KENNETH")
    kenneth_commit = str(anchors.get("kenneth_commit", "") or "")
    if str(decision.get("kenneth_commit", "") or "") != kenneth_commit or source.source_commit != kenneth_commit:
        raise EvidenceBridgeError("Kenneth decision commit mismatch", code="R_KENNETH")
    for key, actual in (
        ("source_subject_id", source.subject_id), ("source_bundle_hash", source.bundle_hash),
        ("target_subject_id", target.subject_id), ("target_bundle_hash", target.bundle_hash),
    ):
        if str(decision.get(key, "") or "") != actual:
            raise EvidenceBridgeError(f"Kenneth decision {key} mismatch", code="R_KENNETH")
    units = decision.get("matched_units")
    if not isinstance(units, list) or not units or any(not isinstance(item, Mapping) for item in units):
        raise EvidenceBridgeError("Kenneth decision lacks exact matched units", code="R_KENNETH")
    if mode == "complete_bundle_blob_exact":
        source_hashes = sorted(item.content_sha256 for item in source.files)
        target_hashes = sorted(item.content_sha256 for item in target.files)
        if source_hashes != target_hashes:
            raise EvidenceBridgeError("complete-bundle Kenneth blobs are not exact", code="R_KENNETH")
    for item in units:
        if item.get("status") != "exact" or item.get("source_hash") != item.get("target_hash"):
            raise EvidenceBridgeError("Kenneth matched unit is not exact", code="R_KENNETH")
    return {"schema": KENNETH_DECISION_SCHEMA, "decision_kind": "author_exact", "exactness_mode": mode}


def _validate_mat_apply(path: Path, payload: Mapping[str, Any], *, task_id: str) -> SubjectBundle:
    """Replay the existing MAT apply interpretation without writing state."""

    if payload.get("schema") != "mat.rubric78.review-apply-receipt.v1":
        raise EvidenceBridgeError("unsupported MAT review-apply schema", code="R_SOURCE_AUTHORITY")
    if (
        canonicalize_block_id(str(payload.get("task_id", "") or "")) != task_id
        or payload.get("authority_eligible") is not True
        or payload.get("clean_pass") is not True
        or payload.get("exact_bundle_covered") is not True
        or str(payload.get("verdict", "") or "").lower() != "pass"
        or str(payload.get("phase2_status", "") or "").lower() != "pass"
        or str(payload.get("invalidated_by", "") or "")
    ):
        raise EvidenceBridgeError("MAT apply is not an active exact clean PASS", code="R_SOURCE_AUTHORITY")
    # Reuse the migration reader that canonical MAT imports already use.  The
    # import is local to avoid a module cycle when state_migration imports us.
    from .state_migration import (  # pylint: disable=import-outside-toplevel
        _artifact_path_from_reference,
        _exact_subject_from_review_input,
        _int_or_none,
        _review_input_for_result,
    )

    result_path = _artifact_path_from_reference(
        path, payload.get("review_result_file", ""),
        fallback_names=(Path(str(payload.get("review_result_file", "") or "")).name,),
    )
    if result_path is None or sha256_file(result_path) != str(payload.get("review_result_hash", "") or ""):
        raise EvidenceBridgeError("MAT apply review-result reference mismatch", code="R_SOURCE_AUTHORITY")
    result = _read_json(result_path, label="MAT review result")
    prompt = _int_or_none(result.get("prompt_version")); rubric = _int_or_none(result.get("rubric_version"))
    independence = result.get("reviewer_independence")
    if (
        canonicalize_block_id(str(result.get("task_id", "") or "")) != task_id
        or str(result.get("verdict", "") or "").lower() != "pass"
        or str(result.get("phase2_status", "") or "").lower() != "pass"
        or prompt not in {9, 10, 11} or rubric != 9
        or not isinstance(independence, Mapping)
        or independence.get("read_only") is not True
        or independence.get("did_edit_candidate") is not False
    ):
        raise EvidenceBridgeError("MAT apply result is not an independent modern r9 PASS", code="R_SOURCE_AUTHORITY")
    input_path, input_payload, input_hash = _review_input_for_result(result_path, result)
    if input_path is None or input_payload is None or input_hash != str(payload.get("review_input_hash", "") or ""):
        raise EvidenceBridgeError("MAT apply input binding mismatch", code="R_SOURCE_AUTHORITY")
    subject = _exact_subject_from_review_input(task_id=task_id, input_payload=input_payload, created_at="")
    if subject is None:
        raise EvidenceBridgeError("MAT apply lacks a complete subject", code="R_SOURCE_AUTHORITY")
    for key, actual in (
        ("subject_id", subject.subject_id), ("bundle_hash", subject.bundle_hash),
        ("primary_hash", subject.primary_hash), ("commit", subject.source_commit),
    ):
        if str(payload.get(key, "") or "") != actual:
            raise EvidenceBridgeError(f"MAT apply {key} mismatch", code="R_SOURCE_AUTHORITY")
    return subject


def _validate_sync_decision(
    decision: Mapping[str, Any], *, task_id: str, anchors: Mapping[str, Any],
    source: SubjectBundle, target: SubjectBundle,
) -> dict[str, Any]:
    if decision.get("schema") != MAT_SYNC_DECISION_SCHEMA:
        raise EvidenceBridgeError("unsupported MAT sync decision schema", code="R_SYNC")
    if canonicalize_block_id(str(decision.get("task_id", "") or "")) != task_id:
        raise EvidenceBridgeError("MAT sync decision task mismatch", code="R_SYNC")
    if decision.get("decision_kind") != AUTHORITY_MAT_SYNC or decision.get("author_controlled") is not True:
        raise EvidenceBridgeError("MAT sync decision is not explicit author selection", code="R_SYNC")
    if decision.get("complete_scope") is not True or decision.get("no_later_conflict") is not True:
        raise EvidenceBridgeError("MAT sync selection lacks complete/conflict-free scope", code="R_SYNC")
    for key, actual in (
        ("source_subject_id", source.subject_id), ("source_bundle_hash", source.bundle_hash),
        ("target_subject_id", target.subject_id), ("target_bundle_hash", target.bundle_hash),
        ("target_commit", str(anchors.get("mat_commit", "") or "")),
    ):
        if str(decision.get(key, "") or "") != actual:
            raise EvidenceBridgeError(f"MAT sync decision {key} mismatch", code="R_SYNC")
    commits = decision.get("sync_commits")
    if not isinstance(commits, list) or not commits or any(not _HEX40.fullmatch(str(item)) for item in commits):
        raise EvidenceBridgeError("MAT sync decision lacks a pinned commit chain", code="R_SYNC")
    if commits[-1] != target.source_commit:
        raise EvidenceBridgeError("MAT sync chain does not end at target", code="R_SYNC")
    return {"schema": MAT_SYNC_DECISION_SCHEMA, "decision_kind": AUTHORITY_MAT_SYNC, "sync_commits": commits}


def _normalize_group_text(files: Mapping[str, str], paths: Sequence[str], rewrites: Mapping[str, str]) -> tuple[list[str], list[dict[str, str]]]:
    payloads: list[str] = []
    declarations: list[dict[str, str]] = []
    for path in paths:
        imports, payload = _imports_and_payload(files[path])
        _opened, payload = _open_namespaces_and_payload(payload)
        _sections, payload = _section_commands_and_payload(payload)
        # Imports remain part of dependency authority, but path/module rewrites
        # are the only accepted normalization.
        payloads.append(" ".join(rewrites.get(item, item) for item in imports) + "\n" + payload)
        declarations.extend(_declaration_signatures(payload, rewrites))
    joined = "\n".join(payloads)
    return _normalize_tokens(joined, rewrites), declarations


def _validate_comparison(
    raw: Any, *, task_id: str, source_files: Mapping[str, str], target_files: Mapping[str, str],
) -> dict[str, Any]:
    if not isinstance(raw, Mapping):
        raise EvidenceBridgeError("comparison is missing", code="R_BUNDLE")
    if raw.get("comparator") != "strict_ordered_lean_tokens_and_declarations.v1":
        raise EvidenceBridgeError("unknown or weak comparator", code="R_SEMANTIC_DELTA")
    if raw.get("status") != "pass" or raw.get("complete_scope") is not True:
        raise EvidenceBridgeError("comparison is not a complete PASS", code="R_BUNDLE")
    if raw.get("unmatched_source") != [] or raw.get("unmatched_target") != []:
        raise EvidenceBridgeError("comparison has unmatched payload", code="R_BUNDLE")
    rewrites_raw = raw.get("module_rewrites", [])
    if not isinstance(rewrites_raw, list):
        raise EvidenceBridgeError("module rewrites are malformed", code="R_SEMANTIC_DELTA")
    rewrites: dict[str, str] = {}
    for item in rewrites_raw:
        if not isinstance(item, Mapping):
            raise EvidenceBridgeError("module rewrite is malformed", code="R_SEMANTIC_DELTA")
        old, new = str(item.get("source", "") or ""), str(item.get("target", "") or "")
        if not old or not new or old == new or old in rewrites:
            raise EvidenceBridgeError("module rewrite is invalid or duplicate", code="R_SEMANTIC_DELTA")
        rewrites[old] = new
    groups = raw.get("reassembly_groups")
    if not isinstance(groups, list) or not groups:
        raise EvidenceBridgeError("reassembly groups are required", code="R_BUNDLE")
    source_seen: list[str] = []; target_seen: list[str] = []; rows: list[dict[str, Any]] = []
    declarations: list[dict[str, Any]] = []
    for index, group in enumerate(groups):
        if not isinstance(group, Mapping):
            raise EvidenceBridgeError("reassembly group is malformed", code="R_BUNDLE")
        source_paths = group.get("source_paths"); target_paths = group.get("target_paths")
        if (
            not isinstance(source_paths, list) or not source_paths
            or not isinstance(target_paths, list) or not target_paths
            or any(path not in source_files for path in source_paths)
            or any(path not in target_files for path in target_paths)
        ):
            raise EvidenceBridgeError("reassembly group names unknown/empty paths", code="R_BUNDLE")
        if any(path in source_seen for path in source_paths) or any(path in target_seen for path in target_paths):
            raise EvidenceBridgeError("reassembly groups overlap", code="R_BUNDLE")
        source_seen.extend(source_paths); target_seen.extend(target_paths)
        source_tokens, source_decls = _normalize_group_text(source_files, source_paths, rewrites)
        target_tokens, target_decls = _normalize_group_text(target_files, target_paths, {})
        if source_tokens != target_tokens:
            raise EvidenceBridgeError(f"ordered Lean payload delta in group {index}", code="R_SEMANTIC_DELTA")
        if source_decls != target_decls:
            raise EvidenceBridgeError(f"public declaration delta in group {index}", code="R_SEMANTIC_DELTA")
        digest = sha256_json(source_tokens)
        rows.append({
            "group_id": str(group.get("group_id", index)),
            "source_paths": list(source_paths), "target_paths": list(target_paths),
            "ordered_payload_sha256": digest,
        })
        declarations.extend(source_decls)
    if set(source_seen) != set(source_files) or len(source_seen) != len(source_files):
        raise EvidenceBridgeError("source scope is not covered exactly once", code="R_BUNDLE")
    if set(target_seen) != set(target_files) or len(target_seen) != len(target_files):
        raise EvidenceBridgeError("target scope is not covered exactly once", code="R_BUNDLE")
    return {
        "comparator": raw["comparator"], "status": "pass", "complete_scope": True,
        "module_rewrites": list(rewrites_raw), "reassembly_groups": rows,
        "unmatched_source": [], "unmatched_target": [],
        "public_declarations": declarations,
        "public_declarations_sha256": sha256_json(declarations),
    }


def _validate_proof_support(
    raw: Any, *, expected_declarations: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    if not isinstance(raw, Mapping) or raw.get("complete_scope") is not True:
        raise EvidenceBridgeError("proof/support manifest is incomplete", code="R_BUNDLE")
    if raw.get("ownership_partition") != "pass" or raw.get("carrier_closure") != "pass":
        raise EvidenceBridgeError("proof/support ownership or carrier closure failed", code="R_BUNDLE")
    result: dict[str, Any] = {
        "complete_scope": True, "ownership_partition": "pass", "carrier_closure": "pass"
    }
    for key in _PAIR_KINDS:
        pairs = raw.get(key, [])
        if not isinstance(pairs, list) or any(not isinstance(item, Mapping) for item in pairs):
            raise EvidenceBridgeError(f"{key} is malformed", code="R_BUNDLE")
        normalized = []
        for item in pairs:
            source_hash = str(item.get("source_hash", "") or "")
            target_hash = str(item.get("target_hash", "") or "")
            if not _HEX64.fullmatch(source_hash) or source_hash != target_hash:
                raise EvidenceBridgeError(f"{key} contains a semantic delta", code="R_SEMANTIC_DELTA")
            if not str(item.get("owner_task", "") or "") or not str(item.get("unit_id", "") or ""):
                raise EvidenceBridgeError(f"{key} lacks exact ownership", code="R_BUNDLE")
            normalized.append(dict(item))
        result[key] = normalized
    declaration_units = {
        str(item.get("name", "") or ""): str(item.get("signature_sha256", "") or "")
        for item in expected_declarations
    }
    declared_pairs = {str(item["unit_id"]): str(item["source_hash"]) for item in result["declaration_pairs"]}
    if declared_pairs != declaration_units:
        raise EvidenceBridgeError(
            "declaration-pair scope does not exactly cover computed declarations",
            code="R_BUNDLE",
        )
    proof_units = {
        str(item.get("name", "") or "")
        for item in expected_declarations
        if str(item.get("kind", "") or "") in {"theorem", "lemma"}
    }
    if {str(item["unit_id"]) for item in result["proof_pairs"]} != proof_units:
        raise EvidenceBridgeError(
            "proof-pair scope does not exactly cover computed theorem/lemma bodies",
            code="R_BUNDLE",
        )
    shims = raw.get("zero_payload_shims", [])
    if not isinstance(shims, list) or any(not isinstance(item, Mapping) or item.get("zero_payload") is not True for item in shims):
        raise EvidenceBridgeError("zero-payload shim declaration is malformed", code="R_BUNDLE")
    result["zero_payload_shims"] = [dict(item) for item in shims]
    result["manifest_sha256"] = sha256_json(result)
    return result


def build_evidence_bridge(
    input_manifest_path: Path, *, source_repos: Sequence[Path], target_repo: Path,
    kenneth_repo: Path, created_at: str | None = None,
    _captured_manifest: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any], SubjectBundle, SubjectBundle]:
    """Inspect an input manifest and build its canonical receipt in memory."""

    input_manifest_path = input_manifest_path.expanduser().resolve()
    manifest = dict(_captured_manifest) if _captured_manifest is not None else _read_json(
        input_manifest_path, label="evidence bridge input"
    )
    if manifest.get("schema") != EVIDENCE_BRIDGE_INPUT_SCHEMA:
        raise EvidenceBridgeError("unsupported evidence bridge input schema", code="R_ROUTE")
    task_id = canonicalize_block_id(str(manifest.get("task_id", "") or ""))
    if not task_id or not is_canonical_block_id(task_id):
        raise EvidenceBridgeError("invalid task id", code="R_ROUTE")
    route = str(manifest.get("bridge_route", "") or "")
    if route not in ROUTES:
        raise EvidenceBridgeError("route is not closed-set A/B; C cannot be bridged", code="R_ROUTE")
    if any(manifest.get(key) is not False for key in ("semantic_upgrade", "rubric_upgrade", "creates_review")):
        raise EvidenceBridgeError("bridge cannot upgrade semantics/rubric or create a review", code="R_ROUTE")
    anchors = manifest.get("anchors")
    if not isinstance(anchors, Mapping):
        raise EvidenceBridgeError("commit anchors are missing", code="R_FRESHNESS")
    mat_commit = str(anchors.get("mat_commit", "") or ""); kenneth_commit = str(anchors.get("kenneth_commit", "") or "")
    if not _HEX40.fullmatch(mat_commit) or not _HEX40.fullmatch(kenneth_commit):
        raise EvidenceBridgeError("MAT/Kenneth anchors must be full commits", code="R_FRESHNESS")
    source = _subject(manifest.get("source_subject"), task_id=task_id, label="source")
    target = _subject(manifest.get("target_subject"), task_id=task_id, label="target")
    if target.source_commit != mat_commit or target.source_repo.lower() != "mat":
        raise EvidenceBridgeError("target is not the pinned MAT bundle", code="R_BUNDLE")

    source_authority = manifest.get("source_authority")
    if not isinstance(source_authority, Mapping):
        raise EvidenceBridgeError("source authority is missing", code="R_SOURCE_AUTHORITY")
    authority_type = str(source_authority.get("type", "") or "")
    if authority_type not in AUTHORITY_TYPES:
        raise EvidenceBridgeError("unknown source authority type", code="R_SOURCE_AUTHORITY")
    if (route == ROUTE_A) != (authority_type == AUTHORITY_KENNETH):
        raise EvidenceBridgeError("route and source authority type disagree", code="R_ROUTE")
    authority_path, authority_payload = _resolve_ref(
        input_manifest_path.parent, source_authority.get("artifact"), label="source authority"
    )
    decision_path, decision = _resolve_ref(
        input_manifest_path.parent, source_authority.get("decision"), label="immutable decision"
    )
    review_identity: dict[str, str] = {}
    if route == ROUTE_A:
        if authority_path != decision_path or authority_payload != decision:
            raise EvidenceBridgeError("A authority must be its exact immutable Kenneth decision", code="R_KENNETH")
        decision_summary = _validate_kenneth_decision(
            decision, task_id=task_id, anchors=anchors, source=source, target=target,
        )
    elif authority_type == AUTHORITY_RECOVERY:
        try:
            recovery, recovered_source = validate_historical_review_apply_recovery(
                authority_path, receipt=authority_payload
            )
        except Exception as exc:
            raise EvidenceBridgeError(f"historical recovery validation failed: {exc}", code="R_SOURCE_AUTHORITY") from exc
        _assert_exact_subject(recovered_source, source, label="historical recovery")
        recovery_artifacts = recovery.get("artifacts")
        recovery_result = recovery_artifacts.get("result") if isinstance(recovery_artifacts, Mapping) else None
        if not isinstance(recovery_result, Mapping):
            raise EvidenceBridgeError("recovery lacks exact result identity", code="R_SOURCE_AUTHORITY")
        review_identity = {
            "review_id": str(recovery.get("review_id", "") or ""),
            "source_evidence_hash": str(recovery_result.get("sha256", "") or ""),
        }
        if authority_path == decision_path:
            decision_summary = {"schema": RECOVERY_SCHEMA, "review_id": recovery.get("review_id", "")}
        else:
            if decision.get("source_authority_sha256") != sha256_file(authority_path):
                raise EvidenceBridgeError("B decision does not bind recovery authority", code="R_SYNC")
            decision_summary = dict(decision)
    elif authority_type == AUTHORITY_MAT_APPLY:
        applied_source = _validate_mat_apply(authority_path, authority_payload, task_id=task_id)
        _assert_exact_subject(applied_source, source, label="MAT apply")
        review_identity = {
            "review_id": str(authority_payload.get("review_id", "") or ""),
            "source_evidence_hash": str(authority_payload.get("review_result_hash", "") or ""),
        }
        if decision.get("source_authority_sha256") != sha256_file(authority_path):
            raise EvidenceBridgeError("B decision does not bind MAT apply", code="R_SYNC")
        decision_summary = dict(decision)
    else:
        if authority_path != decision_path or authority_payload != decision:
            raise EvidenceBridgeError("sync-attested authority must be the exact decision", code="R_SYNC")
        decision_summary = _validate_sync_decision(
            decision, task_id=task_id, anchors=anchors, source=source, target=target,
        )

    try:
        source_roots = (
            [kenneth_repo.resolve()]
            if route == ROUTE_A
            else [Path(item).resolve() for item in source_repos]
        )
        source_files, source_provenance = _bundle_content(
            source_roots, source, label="evidence bridge source"
        )
        target_files, target_provenance = _bundle_content(
            [target_repo.resolve()], target, label="evidence bridge target"
        )
    except BoundaryDeltaReceiptError as exc:
        raise EvidenceBridgeError(str(exc), code="R_BUNDLE") from exc
    if route == ROUTE_A and source.source_commit != kenneth_commit:
        raise EvidenceBridgeError("A source is not pinned Kenneth content", code="R_KENNETH")
    if route == ROUTE_A and any(
        item.get("kind") != "git_commit_path"
        or item.get("commit") != kenneth_commit
        or item.get("raw_git_blob_sha") != item.get("canonical_git_blob_sha")
        for item in source_provenance
    ):
        raise EvidenceBridgeError(
            "A source must come from exact pinned Kenneth tree paths, not worktree/artifact fallback",
            code="R_KENNETH",
        )
    if any(
        item.get("kind") != "git_commit_path"
        or item.get("commit") != mat_commit
        or item.get("raw_git_blob_sha") != item.get("canonical_git_blob_sha")
        for item in target_provenance
    ):
        raise EvidenceBridgeError(
            "target must come from exact pinned MAT tree paths, not worktree/artifact fallback",
            code="R_BUNDLE",
        )

    comparison = _validate_comparison(
        manifest.get("comparison"), task_id=task_id,
        source_files=source_files, target_files=target_files,
    )
    proof_support = _validate_proof_support(
        manifest.get("proof_support_manifest"),
        expected_declarations=comparison["public_declarations"],
    )

    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, Mapping):
        raise EvidenceBridgeError("build/consumer artifacts are missing", code="R_BUILD_SCAN")
    target_build_path, _target_build_raw = _resolve_ref(
        input_manifest_path.parent, artifacts.get("target_build"), label="target exact build"
    )
    consumer_manifest_path, _consumer_manifest_raw = _resolve_ref(
        input_manifest_path.parent, artifacts.get("direct_consumer_manifest"), label="direct consumer manifest"
    )
    raw_consumer_refs = artifacts.get("consumer_builds")
    if not isinstance(raw_consumer_refs, list):
        raise EvidenceBridgeError("consumer build references are malformed", code="R_CONSUMER")
    consumer_build_paths = [
        _resolve_ref(input_manifest_path.parent, raw, label="consumer exact build")[0]
        for raw in raw_consumer_refs
    ]
    try:
        _target_payload, built_target = _target_build(target_build_path, task_id=task_id)
        _assert_exact_subject(built_target, target, label="target exact build")
        consumer_evidence = _consumer_evidence(
            consumer_manifest_path, consumer_build_paths, task_id=task_id,
            target=target, target_repo=target_repo.resolve(),
        )
    except (BoundaryDeltaReceiptError, EvidenceBridgeError) as exc:
        if isinstance(exc, EvidenceBridgeError):
            raise
        raise EvidenceBridgeError(str(exc), code="R_BUILD_SCAN") from exc
    freshness_refs = [
        (authority_path, str(source_authority["artifact"]["sha256"])),
        (decision_path, str(source_authority["decision"]["sha256"])),
        (target_build_path, str(artifacts["target_build"]["sha256"])),
        (
            consumer_manifest_path,
            str(artifacts["direct_consumer_manifest"]["sha256"]),
        ),
        *[
            (path, str(raw["sha256"]))
            for path, raw in zip(consumer_build_paths, raw_consumer_refs, strict=True)
            if isinstance(raw, Mapping)
        ],
    ]
    if any(sha256_file(path) != expected for path, expected in freshness_refs):
        raise EvidenceBridgeError(
            "bound authority/build/consumer evidence changed during validation",
            code="R_FRESHNESS",
        )

    checks = manifest.get("checks")
    if not isinstance(checks, Mapping) or set(checks) != _PASS_CHECKS or any(checks[key] != "pass" for key in _PASS_CHECKS):
        raise EvidenceBridgeError("required bridge checks are not exactly PASS", code="R_ROUTE")
    timestamp = created_at or str(manifest.get("created_at", "") or "") or datetime.now(timezone.utc).isoformat()
    receipt = {
        "schema": EVIDENCE_BRIDGE_SCHEMA,
        "task_id": task_id,
        "created_at": timestamp,
        "bridge_route": route,
        "authority_scope": CAPABILITY_BY_AUTHORITY[authority_type],
        "transformation_kind": TRANSFORMATION_KIND,
        "mechanical_status": "pass",
        "semantic_upgrade": False,
        "rubric_upgrade": False,
        "creates_review": False,
        "anchors": {"mat_commit": mat_commit, "kenneth_commit": kenneth_commit},
        "source_authority": {
            "type": authority_type, "capability": CAPABILITY_BY_AUTHORITY[authority_type],
            "artifact": _ref(authority_path), "decision": _ref(decision_path),
            **review_identity,
        },
        "source_subject": subject_payload(source),
        "target_subject": subject_payload(target),
        "decision": decision_summary,
        "scope": {
            "source_file_count": len(source.files), "target_file_count": len(target.files),
            "complete_source": True, "complete_target": True,
        },
        "comparison": comparison,
        "proof_support_manifest": proof_support,
        "dependencies": {
            "direct_consumer_manifest": _ref(consumer_manifest_path),
            "current_direct_consumer_count": len(consumer_evidence),
        },
        "artifacts": {
            "target_build": _ref(target_build_path),
            "consumer_builds": consumer_evidence,
        },
        "content_provenance": {"source": source_provenance, "target": target_provenance},
        "checks": dict(checks),
        "orchestration": {"input_manifest": _ref(input_manifest_path)},
    }
    return receipt, source, target


def inspect_evidence_bridge(
    input_manifest_path: Path, *, source_repos: Sequence[Path], target_repo: Path,
    kenneth_repo: Path,
) -> dict[str, Any]:
    receipt, source, target = build_evidence_bridge(
        input_manifest_path, source_repos=source_repos,
        target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    return {
        "status": "ready_for_receipt_emission",
        "task_id": receipt["task_id"],
        "bridge_route": receipt["bridge_route"],
        "authority_scope": receipt["authority_scope"],
        "source_subject_id": source.subject_id,
        "target_subject_id": target.subject_id,
        "receipt_sha256_if_emitted": sha256_json(receipt),
        "receipt": receipt,
    }


def validate_evidence_bridge_receipt(
    receipt_path: Path, *, source_repos: Sequence[Path], target_repo: Path,
    kenneth_repo: Path,
) -> tuple[dict[str, Any], SubjectBundle, SubjectBundle]:
    """Replay a future immutable receipt; validation never writes or emits."""

    receipt_path = receipt_path.expanduser().resolve()
    payload = _read_json(receipt_path, label="evidence bridge receipt")
    if payload.get("schema") != EVIDENCE_BRIDGE_SCHEMA:
        raise EvidenceBridgeError("unsupported evidence bridge receipt schema", code="R_ROUTE")
    orchestration = payload.get("orchestration")
    if not isinstance(orchestration, Mapping):
        raise EvidenceBridgeError("receipt lacks input orchestration", code="R_IMMUTABILITY")
    input_path, captured_manifest = _resolve_ref(
        receipt_path.parent, orchestration.get("input_manifest"), label="evidence bridge input"
    )
    rebuilt, source, target = build_evidence_bridge(
        input_path, source_repos=source_repos, target_repo=target_repo,
        kenneth_repo=kenneth_repo, created_at=str(payload.get("created_at", "") or ""),
        _captured_manifest=captured_manifest,
    )
    try:
        payload_for_match = _receipt_match_payload(payload)
        rebuilt_for_match = _receipt_match_payload(rebuilt)
    except BoundaryDeltaReceiptError as exc:
        raise EvidenceBridgeError(str(exc), code="R_IMMUTABILITY") from exc
    if sha256_json(payload_for_match) != sha256_json(rebuilt_for_match):
        raise EvidenceBridgeError("receipt differs from replayed strict evidence", code="R_IMMUTABILITY")
    return rebuilt, source, target


def _git_blob_at(repo: Path, commit: str, path: str, *, label: str) -> tuple[str, bytes]:
    try:
        blob = _run(repo, "git", "rev-parse", f"{commit}:{path}").decode("utf-8").strip()
        data = _run(repo, "git", "show", f"{commit}:{path}")
    except BoundaryDeltaReceiptError as exc:
        raise EvidenceBridgeError(f"{label}: {exc}", code="R_FRESHNESS") from exc
    if not _HEX40.fullmatch(blob):
        raise EvidenceBridgeError(f"{label}: missing full blob id", code="R_FRESHNESS")
    actual = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
    if actual != blob:
        raise EvidenceBridgeError(f"{label}: blob bytes/id mismatch", code="R_FRESHNESS")
    return blob, data


def _audit_strip_comments(text: str) -> str:
    """Historical audit tokenizer comment rule, frozen for exact replay."""

    out: list[str] = []
    index = 0
    depth = 0
    quoted = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1; index += 2; continue
            if text.startswith("-/", index):
                depth -= 1; index += 2; continue
            index += 1; continue
        if quoted:
            out.append(text[index])
            if text[index] == '"' and (index == 0 or text[index - 1] != "\\"):
                quoted = False
            index += 1; continue
        if text.startswith("/-", index):
            depth = 1; index += 2; continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
            continue
        out.append(text[index])
        if text[index] == '"':
            quoted = True
        index += 1
    if depth or quoted:
        raise EvidenceBridgeError("unterminated Lean comment or string", code="R_KENNETH")
    return "".join(out)


def _named_declaration_occurrences(raw: bytes, name: str) -> list[dict[str, Any]]:
    """Extract every exact top-level named declaration using the audit-v1 rule."""

    try:
        text = raw.decode("utf-8-sig", errors="strict").replace("\r\n", "\n")
    except UnicodeDecodeError as exc:
        raise EvidenceBridgeError(f"Lean source is not UTF-8: {exc}", code="R_KENNETH") from exc
    clean = _audit_strip_comments(text)
    selector = re.compile(_DECLARATION_SELECTOR_TEMPLATE.format(name=re.escape(name)))
    occurrences: list[dict[str, Any]] = []
    for match in selector.finditer(clean):
        following = _NEXT_FULL_DECLARATION.search(clean, match.end())
        end = following.start() if following else len(clean)
        fragment = clean[match.start():end]
        fragment = "\n".join(
            line for line in fragment.splitlines() if not line.lstrip().startswith("import ")
        )
        token_list = _AUDIT_TOKEN_RE.findall(fragment)
        occurrences.append({
            "kind": match.group("kind"),
            "name": name,
            "normalized_line": clean.count("\n", 0, match.start()) + 1,
            "token_count": len(token_list),
            "token_sha256": sha256_json(token_list),
        })
    return occurrences


def _tree_named_declarations(
    repo: Path, commit: str, name: str, *, label: str,
) -> list[dict[str, Any]]:
    """Return exact named declarations from every matching Lean blob at a tree."""

    try:
        raw_paths = _run(repo, "git", "grep", "-l", "-F", name, commit, "--", "*.lean")
    except BoundaryDeltaReceiptError as exc:
        raise EvidenceBridgeError(f"{label}: named declaration is absent: {exc}", code="R_KENNETH") from exc
    results: list[dict[str, Any]] = []
    candidate_paths = []
    for raw_path in raw_paths.decode("utf-8", errors="strict").splitlines():
        prefix = f"{commit}:"
        candidate_paths.append(raw_path[len(prefix):] if raw_path.startswith(prefix) else raw_path)
    for path in sorted(set(candidate_paths)):
        blob, data = _git_blob_at(repo, commit, path, label=f"{label} declaration candidate")
        for occurrence in _named_declaration_occurrences(data, name):
            results.append({"path": path, "git_blob_sha1": blob, **occurrence})
    return results


def _load_bridge_catalog(target_repo: Path, commit: str) -> TaskCatalog:
    runtime_root = Path(__file__).resolve().parents[2]
    try:
        catalog = load_catalog(
            workspace_root=runtime_root.parent,
            runtime_root=runtime_root,
            mat_root=target_repo.resolve(),
        )
    except CatalogError as exc:
        raise EvidenceBridgeError(f"cannot load catalog ownership: {exc}", code="R_BUNDLE") from exc
    try:
        validate_catalog_compatible_mat_commit(
            catalog, mat_root=target_repo.resolve(), commit=commit,
        )
    except CatalogError as exc:
        raise EvidenceBridgeError(
            f"catalog ownership is incompatible with MAT target: {exc}", code="R_BUNDLE"
        ) from exc
    return catalog


def _module_payload(catalog: TaskCatalog, path: str, *, label: str) -> dict[str, Any]:
    matches = [module for module in catalog.modules if module.path == path]
    if len(matches) != 1:
        raise EvidenceBridgeError(
            f"{label}: catalog path ownership count is {len(matches)}, expected 1",
            code="R_BUNDLE",
        )
    return matches[0].as_dict()


def _mechanical_carrier_selector(
    *, task_id: str, subject: SubjectBundle, mappings: Sequence[Mapping[str, Any]],
    target_repo: Path, mat_commit: str, kenneth_repo: Path, kenneth_commit: str,
    catalog: TaskCatalog,
) -> dict[str, Any]:
    """Close a carrier mapping solely from pinned trees and catalog ownership."""

    if len(mappings) != 1:
        raise EvidenceBridgeError(
            f"{task_id}: carrier selector requires exactly one mapping, got {len(mappings)}",
            code="R_KENNETH",
        )
    mapping = mappings[0]
    if mapping.get("relation") != "full_named_declaration_token_exact_including_body":
        raise EvidenceBridgeError(f"{task_id}: carrier relation is not declaration-exact", code="R_KENNETH")
    declared_count = int(mapping.get("token_count", -1))
    declared_hash = str(mapping.get("token_sha256", "") or "")
    if declared_count < 1 or not _HEX64.fullmatch(declared_hash):
        raise EvidenceBridgeError(f"{task_id}: declaration token identity is incomplete", code="R_KENNETH")

    kenneth_occurrences = _tree_named_declarations(
        kenneth_repo, kenneth_commit, task_id, label=f"{task_id} Kenneth tree",
    )
    mat_occurrences = _tree_named_declarations(
        target_repo, mat_commit, task_id, label=f"{task_id} MAT tree",
    )
    expected_kenneth_path = str(mapping.get("kenneth_path", "") or "")
    expected_mat_path = str(mapping.get("mat_path", "") or "")
    kenneth_selected_set = [item for item in kenneth_occurrences if item["path"] == expected_kenneth_path]
    mat_selected_set = [item for item in mat_occurrences if item["path"] == expected_mat_path]
    if len(kenneth_selected_set) != 1 or len(mat_selected_set) != 1:
        raise EvidenceBridgeError(
            f"{task_id}: declared carrier selector count differs from one "
            f"(Kenneth={len(kenneth_selected_set)}, MAT={len(mat_selected_set)})",
            code="R_KENNETH",
        )
    kenneth_selected = kenneth_selected_set[0]
    mat_selected = mat_selected_set[0]
    for selected in (*kenneth_occurrences, *mat_occurrences):
        if selected["token_count"] != declared_count or selected["token_sha256"] != declared_hash:
            raise EvidenceBridgeError(
                f"{task_id}: tree has a competing non-equivalent named declaration at {selected['path']}",
                code="R_KENNETH",
            )
    if kenneth_selected["kind"] != mat_selected["kind"]:
        raise EvidenceBridgeError(f"{task_id}: declaration kind differs across pinned trees", code="R_KENNETH")

    carrier_module = _module_payload(catalog, expected_mat_path, label=f"{task_id} carrier")
    current_modules = [
        _module_payload(catalog, item.path, label=f"{task_id} current bundle")
        for item in subject.files
    ]
    current_paths = {item.path for item in subject.files}
    if expected_mat_path in current_paths:
        carrier_reachability = "current_owned_bundle_member"
    else:
        carrier_module_name = str(carrier_module["module_name"])
        importing_paths: list[str] = []
        for item in subject.files:
            _blob, data = _git_blob_at(
                target_repo, mat_commit, item.path, label=f"{task_id} current shim",
            )
            imports = [
                match.group(1)
                for line in data.decode("utf-8-sig", errors="strict").replace("\r\n", "\n").splitlines()
                if (match := re.fullmatch(r"\s*import\s+([A-Za-z0-9_'.]+)\s*", line))
            ]
            if carrier_module_name in imports:
                importing_paths.append(item.path)
        if len(importing_paths) != 1:
            raise EvidenceBridgeError(
                f"{task_id}: carrier has {len(importing_paths)} direct current-bundle imports, expected 1",
                code="R_KENNETH",
            )
        carrier_reachability = f"direct_import_from:{importing_paths[0]}"

    return {
        "declaration_selector": {
            "schema": "toy-apollo.lean-named-declaration-selector.v1",
            "extractor_version": _CANONICAL_DECLARATION_EXTRACTOR,
            "name": task_id,
            "kind": mat_selected["kind"],
            "relation": "full_named_declaration_token_exact_including_body",
            "token_count": declared_count,
            "token_sha256": declared_hash,
            "kenneth": kenneth_selected,
            "mat": mat_selected,
            "kenneth_equivalent_tree_occurrences": kenneth_occurrences,
            "mat_equivalent_tree_occurrences": mat_occurrences,
        },
        "scope_closure": {
            "task_shim_no_competing_declaration": True,
            "kenneth_tree_named_declaration_count": len(kenneth_occurrences),
            "mat_tree_named_declaration_count": len(mat_occurrences),
            "kenneth_distinct_named_declaration_token_identities": 1,
            "mat_distinct_named_declaration_token_identities": 1,
            "carrier_reachability": carrier_reachability,
        },
        "carrier_owner_and_support_manifest": {
            "catalog_id": catalog.catalog_id,
            "catalog_mat_commit": catalog.mat_commit,
            "carrier": carrier_module,
            "current_bundle_modules": current_modules,
            "complete_current_bundle": True,
        },
    }


def inspect_kenneth_authority_manifest(
    manifest_path: Path, *, target_repo: Path, kenneth_repo: Path,
) -> dict[str, Any]:
    """Read-only adapter audit for the consolidated 61A authority manifest.

    The batch manifest is authority input, not a receipt.  Complete byte-exact
    bundles are direct.  Carrier-only claims are mechanically closed by replaying
    the historical audit-v1 named-declaration extractor over both pinned trees,
    proving tree uniqueness, and binding carrier/support ownership to the catalog.
    """

    manifest_path = manifest_path.expanduser().resolve()
    payload = _read_json(manifest_path, label="Kenneth author-exact batch authority")
    if payload.get("schema") != KENNETH_BATCH_AUTHORITY_SCHEMA:
        raise EvidenceBridgeError("unsupported Kenneth batch authority schema", code="R_ROUTE")
    anchors = payload.get("anchors")
    items = payload.get("items")
    counts = payload.get("counts")
    if not isinstance(anchors, Mapping) or not isinstance(items, list) or not isinstance(counts, Mapping):
        raise EvidenceBridgeError("Kenneth batch authority is incomplete", code="R_SOURCE_AUTHORITY")
    mat_commit = str(anchors.get("mat_commit", "") or "")
    kenneth_commit = str(anchors.get("kenneth_commit", "") or "")
    if not _HEX40.fullmatch(mat_commit) or not _HEX40.fullmatch(kenneth_commit):
        raise EvidenceBridgeError("batch authority commits are not pinned", code="R_FRESHNESS")
    try:
        mat_tree = _run(target_repo.resolve(), "git", "rev-parse", f"{mat_commit}^{{tree}}").decode().strip()
        kenneth_tree = _run(kenneth_repo.resolve(), "git", "rev-parse", f"{kenneth_commit}^{{tree}}").decode().strip()
    except BoundaryDeltaReceiptError as exc:
        raise EvidenceBridgeError(str(exc), code="R_FRESHNESS") from exc
    if mat_tree != str(anchors.get("mat_tree", "") or "") or kenneth_tree != str(anchors.get("kenneth_tree", "") or ""):
        raise EvidenceBridgeError("batch authority tree identity mismatch", code="R_FRESHNESS")
    if int(counts.get("total", 0) or 0) != len(items):
        raise EvidenceBridgeError("batch authority item count mismatch", code="R_SOURCE_AUTHORITY")
    final122 = payload.get("sources", {}).get("final122") if isinstance(payload.get("sources"), Mapping) else None
    if (
        not isinstance(final122, Mapping)
        or final122.get("sha256") != anchors.get("final122_manifest_sha256")
    ):
        raise EvidenceBridgeError("batch authority final122 binding mismatch", code="R_SOURCE_AUTHORITY")
    final_path = Path(str(final122.get("path", "") or "")).resolve()
    if not final_path.is_file() or sha256_file(final_path) != final122.get("sha256"):
        raise EvidenceBridgeError("batch authority final122 artifact mismatch", code="R_IMMUTABILITY")

    task_ids: list[str] = []
    build_task_ids: set[str] = set()
    for raw in items:
        if not isinstance(raw, Mapping):
            raise EvidenceBridgeError("batch item is not an object", code="R_SOURCE_AUTHORITY")
        task_id = canonicalize_block_id(str(raw.get("task_id", "") or ""))
        if not task_id or not is_canonical_block_id(task_id) or task_id in task_ids:
            raise EvidenceBridgeError("batch task id is invalid or duplicate", code="R_SOURCE_AUTHORITY")
        task_ids.append(task_id); build_task_ids.add(task_id)
        direct = raw.get("direct_consumers")
        if isinstance(direct, Mapping):
            for consumer in direct.get("consumer_tasks", []):
                if isinstance(consumer, Mapping):
                    consumer_id = canonicalize_block_id(str(consumer.get("task_id", "") or ""))
                    if consumer_id:
                        build_task_ids.add(consumer_id)
    context = _exact_catalog_context(
        target_repo=target_repo.resolve(), commit=mat_commit,
        task_ids=sorted(build_task_ids),
    )
    catalog = _load_bridge_catalog(target_repo.resolve(), mat_commit)

    results: list[dict[str, Any]] = []
    validated_receipt_paths: dict[Path, str] = {}
    for raw in items:
        task_id = canonicalize_block_id(str(raw.get("task_id", "") or ""))
        problems: list[dict[str, str]] = []
        current = raw.get("current")
        if not isinstance(current, Mapping):
            raise EvidenceBridgeError(f"{task_id}: current subject is missing", code="R_BUNDLE")
        subject = _subject(
            {
                "task_id": task_id, "subject_id": current.get("S"),
                "bundle_hash": current.get("B"), "primary_hash": current.get("P"),
                "primary_path": current.get("primary_path"), "files": current.get("files"),
                "source_repo": "mat", "source_commit": current.get("commit"),
                "layout": "mat", "subject_kind": "catalog_git_bundle",
            },
            task_id=task_id, label="batch current",
        )
        context_subject = context["subjects"].get(task_id)
        if not isinstance(context_subject, SubjectBundle) or context_subject.subject_id != subject.subject_id:
            raise EvidenceBridgeError(f"{task_id}: catalog/current subject mismatch", code="R_BUNDLE")
        try:
            _files, provenance = _bundle_content([target_repo.resolve()], subject, label=f"{task_id} current")
        except BoundaryDeltaReceiptError as exc:
            raise EvidenceBridgeError(str(exc), code="R_BUNDLE") from exc
        if any(
            item.get("kind") != "git_commit_path"
            or item.get("commit") != mat_commit
            or item.get("raw_git_blob_sha") != item.get("canonical_git_blob_sha")
            for item in provenance
        ):
            raise EvidenceBridgeError(f"{task_id}: current subject is not pinned MAT tree exact", code="R_BUNDLE")

        kenneth = raw.get("kenneth")
        if not isinstance(kenneth, Mapping) or kenneth.get("commit") != kenneth_commit:
            raise EvidenceBridgeError(f"{task_id}: Kenneth authority anchor mismatch", code="R_KENNETH")
        scope = kenneth.get("scope_closure")
        mappings = kenneth.get("mappings")
        if not isinstance(scope, Mapping) or scope.get("closed") is not True or not isinstance(mappings, list) or not mappings:
            raise EvidenceBridgeError(f"{task_id}: Kenneth scope is not closed", code="R_KENNETH")
        verified_mappings: list[dict[str, Any]] = []
        for mapping in mappings:
            if not isinstance(mapping, Mapping) or mapping.get("exact") is not True:
                raise EvidenceBridgeError(f"{task_id}: Kenneth mapping is malformed", code="R_KENNETH")
            kenneth_path = str(mapping.get("kenneth_path", "") or "")
            mat_path = str(mapping.get("mat_path", "") or "")
            kenneth_blob, kenneth_bytes = _git_blob_at(
                kenneth_repo.resolve(), kenneth_commit, kenneth_path,
                label=f"{task_id} Kenneth mapping",
            )
            mat_blob, mat_bytes = _git_blob_at(
                target_repo.resolve(), mat_commit, mat_path,
                label=f"{task_id} MAT mapping",
            )
            if kenneth_blob != mapping.get("kenneth_blob") or mat_blob != mapping.get("mat_blob"):
                raise EvidenceBridgeError(f"{task_id}: mapping blob declaration mismatch", code="R_KENNETH")
            relation = str(mapping.get("relation", "") or "")
            if relation in {"byte_exact_full_file", "git_blob_byte_exact"}:
                if kenneth_bytes != mat_bytes or kenneth_blob != mat_blob:
                    raise EvidenceBridgeError(f"{task_id}: declared byte-exact mapping differs", code="R_KENNETH")
                content_hash = str(mapping.get("content_sha256", "") or "")
                if content_hash and hashlib.sha256(kenneth_bytes).hexdigest() != content_hash:
                    raise EvidenceBridgeError(f"{task_id}: byte-exact content hash mismatch", code="R_KENNETH")
            elif relation != "full_named_declaration_token_exact_including_body":
                raise EvidenceBridgeError(f"{task_id}: unknown Kenneth mapping relation", code="R_KENNETH")
            verified_mappings.append({
                "kenneth_path": kenneth_path, "mat_path": mat_path,
                "kenneth_blob": kenneth_blob, "mat_blob": mat_blob,
                "relation": relation, "blob_bytes_equal": kenneth_bytes == mat_bytes,
            })

        current_by_path = {item.path: item for item in subject.files}
        mapped_by_path = {
            str(mapping.get("mat_path", "") or ""): mapping for mapping in mappings
        }
        full_bundle_blob_derivable = set(mapped_by_path) == set(current_by_path) and all(
            str(mapped_by_path[path].get("mat_blob", "") or "") == item.git_blob_sha
            and str(mapped_by_path[path].get("kenneth_blob", "") or "") == item.git_blob_sha
            for path, item in current_by_path.items()
        )
        mechanical_selector: dict[str, Any] | None = None
        if not full_bundle_blob_derivable:
            try:
                mechanical_selector = _mechanical_carrier_selector(
                    task_id=task_id, subject=subject, mappings=mappings,
                    target_repo=target_repo.resolve(), mat_commit=mat_commit,
                    kenneth_repo=kenneth_repo.resolve(), kenneth_commit=kenneth_commit,
                    catalog=catalog,
                )
            except EvidenceBridgeError as exc:
                problems.append({
                    "code": exc.code,
                    "field": "mechanical_carrier_selector",
                    "message": str(exc),
                })

        synchronization = raw.get("synchronization")
        if not isinstance(synchronization, Mapping) or synchronization.get("ancestor_of_target") is not True:
            raise EvidenceBridgeError(f"{task_id}: synchronization decision is incomplete", code="R_SYNC")
        sync_commit = str(synchronization.get("commit", "") or "")
        if not _HEX40.fullmatch(sync_commit):
            raise EvidenceBridgeError(f"{task_id}: synchronization commit is not pinned", code="R_SYNC")
        try:
            _run(target_repo.resolve(), "git", "merge-base", "--is-ancestor", sync_commit, mat_commit)
        except BoundaryDeltaReceiptError as exc:
            raise EvidenceBridgeError(f"{task_id}: sync commit is not an ancestor", code="R_SYNC") from exc
        for check in synchronization.get("path_blob_checks", []):
            if not isinstance(check, Mapping) or check.get("pass") is not True:
                raise EvidenceBridgeError(f"{task_id}: sync path/blob check failed", code="R_SYNC")
            path = str(check.get("path", "") or "")
            blob, _data = _git_blob_at(target_repo.resolve(), sync_commit, path, label=f"{task_id} sync path")
            if blob != check.get("current_blob"):
                raise EvidenceBridgeError(f"{task_id}: sync path blob mismatch", code="R_SYNC")
        historical = raw.get("historical_context")
        if not isinstance(historical, Mapping) or historical.get("integrity_pass") is not True:
            raise EvidenceBridgeError(f"{task_id}: historical context integrity failed", code="R_SOURCE_AUTHORITY")
        for ref in historical.get("refs", []):
            if not isinstance(ref, Mapping):
                raise EvidenceBridgeError(f"{task_id}: historical reference malformed", code="R_IMMUTABILITY")
            ref_path = Path(str(ref.get("path", "") or "")).resolve()
            if (
                ref.get("exists") is not True or ref.get("hash_exact") is not True
                or not ref_path.is_file() or sha256_file(ref_path) != ref.get("sha256")
                or ref.get("sha256") != ref.get("expected_sha256")
            ):
                raise EvidenceBridgeError(f"{task_id}: historical reference mismatch", code="R_IMMUTABILITY")

        build_errors: list[str] = []
        build_refs: list[tuple[str, Mapping[str, Any]]] = [(task_id, raw.get("exact_build"))]
        direct = raw.get("direct_consumers")
        if not isinstance(direct, Mapping) or direct.get("unowned_paths") is None:
            raise EvidenceBridgeError(f"{task_id}: direct-consumer scope is malformed", code="R_CONSUMER")
        for consumer in direct.get("consumer_tasks", []):
            if isinstance(consumer, Mapping):
                build_refs.append((str(consumer.get("task_id", "") or ""), consumer.get("exact_build_receipt")))
        for build_task, build_ref in build_refs:
            if not isinstance(build_ref, Mapping):
                build_errors.append(f"{build_task}:missing_reference"); continue
            build_path = Path(str(build_ref.get("path", "") or "")).resolve()
            expected_hash = str(build_ref.get("sha256", "") or "")
            if build_ref.get("exists") is not True or not build_path.is_file() or sha256_file(build_path) != expected_hash:
                build_errors.append(f"{build_task}:missing_or_hash_mismatch"); continue
            previous = validated_receipt_paths.get(build_path)
            if previous is not None and previous != expected_hash:
                raise EvidenceBridgeError("exact-build path has conflicting hashes", code="R_IMMUTABILITY")
            if previous is None:
                try:
                    _validate_context_exact_build(build_path, task_id=build_task, context=context)
                except BoundaryDeltaReceiptError as exc:
                    build_errors.append(f"{build_task}:{exc}"); continue
                validated_receipt_paths[build_path] = expected_hash
        if direct.get("unowned_paths"):
            build_errors.append("unowned_direct_consumer_module_evidence")
        declared_build_ready = raw.get("build_prerequisite_complete") is True
        actual_build_ready = not build_errors
        if declared_build_ready != actual_build_ready:
            raise EvidenceBridgeError(
                f"{task_id}: declared/actual build prerequisite status differs",
                code="R_BUILD_SCAN",
            )
        authority_ready = full_bundle_blob_derivable or mechanical_selector is not None
        results.append({
            "task_id": task_id,
            "declared_authority_eligible": raw.get("authority_eligible") is True,
            "framework_authority_ready": authority_ready,
            "framework_build_ready": actual_build_ready,
            "framework_receipt_ready": authority_ready and actual_build_ready,
            "normalized_exactness_mode": (
                "complete_bundle_blob_exact" if authority_ready
                and full_bundle_blob_derivable else
                "full_named_declaration_exact" if mechanical_selector is not None
                else "carrier_selector_ambiguous"
            ),
            "declared_kenneth_mode": kenneth.get("mode"),
            "verified_mappings": verified_mappings,
            "mechanical_carrier_evidence": mechanical_selector,
            "build_errors": build_errors,
            "incompatibilities": problems,
        })

    summary = {
        "items": len(results),
        "declared_authority_eligible": sum(item["declared_authority_eligible"] for item in results),
        "framework_authority_ready": sum(item["framework_authority_ready"] for item in results),
        "framework_authority_blocked_schema": sum(not item["framework_authority_ready"] for item in results),
        "framework_build_ready": sum(item["framework_build_ready"] for item in results),
        "framework_build_prerequisite_missing": sum(not item["framework_build_ready"] for item in results),
        "framework_receipt_ready": sum(item["framework_receipt_ready"] for item in results),
        "validated_unique_exact_build_receipts": len(validated_receipt_paths),
    }
    return {
        "schema": "toy-apollo.kenneth-authority-manifest-inspect.v1",
        "status": "inspect_only_no_receipt_emitted",
        "manifest": _ref(manifest_path),
        "anchors": {
            "mat_commit": mat_commit, "mat_tree": mat_tree,
            "kenneth_commit": kenneth_commit, "kenneth_tree": kenneth_tree,
        },
        "summary": summary,
        "batch_schema_compatibility": {
            "direct_per_item_input_compatible": False,
            "adapter": "inspect_kenneth_authority_manifest",
            "batch_decision_ref_required": True,
            "embedded_direct_consumer_scope_requires_batch_snapshot": True,
        },
        "items": results,
    }


def _read_jsonl(path: Path, *, expected_hash: str) -> list[Mapping[str, Any]]:
    path = _resolved_snapshot(path, expected_hash)
    try:
        data = path.read_bytes()
    except OSError as exc:
        raise EvidenceBridgeError(f"cannot read JSONL binding: {path}: {exc}", code="R_IMMUTABILITY") from exc
    if not _HEX64.fullmatch(expected_hash) or hashlib.sha256(data).hexdigest() != expected_hash:
        raise EvidenceBridgeError(f"JSONL binding mismatch: {path}", code="R_IMMUTABILITY")
    rows: list[Mapping[str, Any]] = []
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError as exc:
        raise EvidenceBridgeError(f"invalid JSONL encoding: {path}", code="R_IMMUTABILITY") from exc
    for number, line in enumerate(lines, 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise EvidenceBridgeError(f"invalid JSONL row {number}: {exc}", code="R_IMMUTABILITY") from exc
        if not isinstance(row, Mapping):
            raise EvidenceBridgeError(f"JSONL row {number} is not an object", code="R_IMMUTABILITY")
        rows.append(row)
    return rows


def _json_pointer(payload: Any, pointer: str) -> Any:
    if not pointer.startswith("/"):
        raise EvidenceBridgeError(f"invalid JSON pointer {pointer!r}", code="R_SOURCE_AUTHORITY")
    current = payload
    for raw in pointer[1:].split("/"):
        token = raw.replace("~1", "/").replace("~0", "~")
        if isinstance(current, list):
            try:
                current = current[int(token)]
            except (ValueError, IndexError) as exc:
                raise EvidenceBridgeError(f"JSON pointer misses list item {token!r}", code="R_SOURCE_AUTHORITY") from exc
        elif isinstance(current, Mapping) and token in current:
            current = current[token]
        else:
            raise EvidenceBridgeError(f"JSON pointer misses field {token!r}", code="R_SOURCE_AUTHORITY")
    return current


def _check_file_ref(raw: Any, *, label: str, base: Path | None = None) -> dict[str, str]:
    if not isinstance(raw, Mapping):
        raise EvidenceBridgeError(f"{label} reference is missing", code="R_IMMUTABILITY")
    path = Path(str(raw.get("path", raw.get("absolute_path", "")) or ""))
    if base is not None and not path.is_absolute():
        path = base / path
    original_path = path.resolve()
    digest = str(raw.get("sha256", "") or "")
    path = _resolved_snapshot(original_path, digest)
    try:
        data = path.read_bytes()
    except OSError as exc:
        raise EvidenceBridgeError(f"{label} path/hash mismatch: {path}: {exc}", code="R_IMMUTABILITY") from exc
    if not _HEX64.fullmatch(digest) or hashlib.sha256(data).hexdigest() != digest:
        raise EvidenceBridgeError(f"{label} path/hash mismatch: {path}", code="R_IMMUTABILITY")
    return {"path": str(path), "sha256": digest}


def _row_task(row: Mapping[str, Any]) -> str:
    return canonicalize_block_id(str(row.get("task_id", row.get("task", "")) or ""))


def _subject_triplet(row: Mapping[str, Any]) -> tuple[str, str, str]:
    return (
        str(row.get("S", row.get("subject_id", "")) or ""),
        str(row.get("B", row.get("bundle_hash", "")) or ""),
        str(row.get("P", row.get("primary_hash", row.get("primary_sha256", ""))) or ""),
    )


def _assert_triplet(raw: Mapping[str, Any], subject: SubjectBundle, *, label: str) -> None:
    if _subject_triplet(raw) != (subject.subject_id, subject.bundle_hash, subject.primary_hash):
        raise EvidenceBridgeError(f"{label} S/B/P mismatch", code="R_BUNDLE")


def _catalog_import_index(
    *, catalog: TaskCatalog, target_repo: Path, commit: str,
) -> tuple[dict[str, set[str]], dict[str, dict[str, Any]]]:
    imports: dict[str, set[str]] = {module.path: set() for module in catalog.modules}
    try:
        raw = _run(target_repo, "git", "grep", "-n", "-E", r"^import[[:space:]]+", commit, "--", "*.lean")
    except BoundaryDeltaReceiptError as exc:
        raise EvidenceBridgeError(f"cannot derive current direct consumers: {exc}", code="R_CONSUMER") from exc
    prefix = f"{commit}:"
    for line in raw.decode("utf-8", errors="strict").splitlines():
        if line.startswith(prefix):
            line = line[len(prefix):]
        parts = line.split(":", 2)
        if len(parts) != 3:
            raise EvidenceBridgeError("malformed pinned import scan output", code="R_CONSUMER")
        path, _line_no, source = parts
        match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_'.]+)\s*", source)
        if match and path in imports:
            imports[path].add(match.group(1))
    modules = {module.module_name: module.as_dict() for module in catalog.modules}
    return imports, modules


def _direct_consumer_closure(
    *, task_id: str, catalog: TaskCatalog, imports: Mapping[str, set[str]],
    modules_by_name: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    target_modules = {
        module.module_name for module in catalog.modules
        if module.owner_task_id == task_id and module.module_role in {"primary", "owned_support"}
    }
    consumers: set[str] = set(); unowned: set[str] = set()
    for module in catalog.modules:
        if not (imports.get(module.path, set()) & target_modules):
            continue
        if module.owner_task_id and module.owner_task_id != task_id:
            consumers.add(module.owner_task_id)
        elif not module.owner_task_id:
            unowned.add(module.module_name)
    unowned_coverage: dict[str, list[str]] = {}
    for shared in sorted(unowned):
        owners = sorted({
            module.owner_task_id for module in catalog.modules
            if module.owner_task_id and shared in imports.get(module.path, set())
        })
        if not owners:
            raise EvidenceBridgeError(
                f"{task_id}: unowned direct consumer {shared} lacks task-owned import coverage",
                code="R_CONSUMER",
            )
        unowned_coverage[shared] = owners
    return {
        "consumer_task_ids": sorted(consumers),
        "unowned_module_coverage": unowned_coverage,
        "target_module_names": sorted(target_modules),
    }


def _validate_b39_authority(row: Mapping[str, Any], *, task_id: str, target: SubjectBundle) -> dict[str, Any]:
    if _row_task(row) != task_id or row.get("bridge_class") != "B_REVIEWED_MAT_SYNCHRONIZATION_REASSEMBLY":
        raise EvidenceBridgeError(f"{task_id}: B39 pointer mismatch", code="R_SOURCE_AUTHORITY")
    _assert_triplet(row.get("target_subject", {}), target, label=f"{task_id} B39 current")
    authority = row.get("source_authority"); responsibility = row.get("responsibility"); delta = row.get("delta_manifest")
    if not isinstance(authority, Mapping) or authority.get("valid") is not True:
        raise EvidenceBridgeError(f"{task_id}: B39 source authority is not valid", code="R_SOURCE_AUTHORITY")
    if not isinstance(responsibility, Mapping) or responsibility.get("status") != "complete":
        raise EvidenceBridgeError(f"{task_id}: B39 responsibility decision is incomplete", code="R_SYNC")
    if not isinstance(delta, Mapping) or not str(delta.get("status", "")).startswith("complete_recorded"):
        raise EvidenceBridgeError(f"{task_id}: B39 reassembly record is incomplete", code="R_SYNC")
    for key in ("input", "result", "verify", "verify_apply", "matching_successful_review_apply", "recovery_receipt"):
        if isinstance(authority.get(key), Mapping):
            _check_file_ref(authority[key], label=f"{task_id} source {key}")
    for key in ("evidence",):
        if isinstance(delta.get(key), Mapping):
            _check_file_ref(delta[key], label=f"{task_id} delta evidence")
    for commit in responsibility.get("commits", []):
        if not isinstance(commit, Mapping) or commit.get("exists") is not True or commit.get("ancestor_of_target") is not True:
            raise EvidenceBridgeError(f"{task_id}: B39 sync commit is not admitted", code="R_SYNC")
    return {"source_schema": "B39", "authority_kind": authority.get("kind"), "decision_status": "pass"}


def _validate_c8_authority(
    row: Mapping[str, Any], *, task_id: str, route: str, target: SubjectBundle,
    target_repo: Path, kenneth_repo: Path, kenneth_commit: str,
) -> dict[str, Any]:
    expected = "A" if route == ROUTE_A else "B"
    if _row_task(row) != task_id or row.get("decision_class") != expected or row.get("decision_found") is not True:
        raise EvidenceBridgeError(f"{task_id}: C8 decision mismatch", code="R_SOURCE_AUTHORITY")
    _assert_triplet(row.get("current", {}), target, label=f"{task_id} C8 current")
    spec_ref = _check_file_ref(row.get("full_manifest_ref"), label=f"{task_id} C8 full manifest")
    spec = _read_json(Path(spec_ref["path"]), label=f"{task_id} C8 spec")
    mat_subject = spec.get("mat_subject")
    if isinstance(mat_subject, Mapping):
        _assert_triplet(mat_subject, target, label=f"{task_id} C8 spec current")
    for value in (row.get("historical_authority_context") or {}).values():
        if isinstance(value, Mapping):
            _check_file_ref(value, label=f"{task_id} C8 historical context")
    if route == ROUTE_A:
        blobs = []
        for item in target.files:
            blob, kenneth_bytes = _git_blob_at(kenneth_repo, kenneth_commit, item.path, label=f"{task_id} C8 Kenneth")
            mat_blob, mat_bytes = _git_blob_at(target_repo, target.source_commit, item.path, label=f"{task_id} C8 MAT")
            if blob != mat_blob or kenneth_bytes != mat_bytes:
                raise EvidenceBridgeError(f"{task_id}: C8 complete Kenneth bundle differs", code="R_KENNETH")
            blobs.append(blob)
        declared = sorted((row.get("existing_decision") or {}).get("git_blobs", []))
        if sorted(blobs) != declared:
            raise EvidenceBridgeError(f"{task_id}: C8 Kenneth blob set mismatch", code="R_KENNETH")
    elif not str(row.get("verifiable_bridge", "") or ""):
        raise EvidenceBridgeError(f"{task_id}: C8 B bridge decision is empty", code="R_SYNC")
    return {"source_schema": "C8", "authority_kind": (row.get("existing_decision") or {}).get("kind"), "decision_status": "pass"}


def _validate_ch12_authority(
    payload: Mapping[str, Any], row: Mapping[str, Any], *, task_id: str, target: SubjectBundle,
) -> dict[str, Any]:
    if _row_task(row) != task_id or "EXPLICIT_BRANCH_DECISION_FOUND" not in str(row.get("finding", "")):
        raise EvidenceBridgeError(f"{task_id}: Ch12 explicit branch decision is absent", code="R_SYNC")
    _assert_triplet(row.get("current_subject", {}), target, label=f"{task_id} Ch12 current")
    matched = (row.get("pr6_bundle_match") or {}).get("matched_files")
    if not isinstance(matched, list) or {
        (item.get("path"), item.get("sha256")) for item in matched if isinstance(item, Mapping)
    } != {(item.path, item.content_sha256) for item in target.files}:
        raise EvidenceBridgeError(f"{task_id}: Ch12 PR bundle is not current-exact", code="R_SYNC")
    common = payload.get("common_refs") or {}
    for ref in row.get("exact_refs", []):
        if isinstance(ref, Mapping):
            _check_file_ref(ref, label=f"{task_id} Ch12 exact decision")
        elif isinstance(ref, str) and ref.startswith("common_refs."):
            common_ref = common.get(ref.split(".", 1)[1])
            if isinstance(common_ref, Mapping) and (common_ref.get("path") or common_ref.get("absolute_path")):
                _check_file_ref(common_ref, label=f"{task_id} Ch12 common decision")
            elif isinstance(common_ref, Mapping):
                commits = [str(common_ref.get(key, "") or "") for key in ("base", "head", "merge")]
                if not all(_HEX40.fullmatch(commit) for commit in commits):
                    raise EvidenceBridgeError(f"{task_id}: Ch12 Git decision ref is incomplete", code="R_SYNC")
            else:
                raise EvidenceBridgeError(f"{task_id}: Ch12 common decision ref is missing", code="R_SYNC")
    return {"source_schema": "CH12", "authority_kind": "explicit_branch_decision", "decision_status": "pass"}


def _validate_scope3_authority(
    row: Mapping[str, Any], *, task_id: str, target: SubjectBundle, target_repo: Path,
) -> dict[str, Any]:
    if _row_task(row) != task_id or row.get("decision") != "CONSTRUCTIBLE":
        raise EvidenceBridgeError(f"{task_id}: source-scope selector is not constructible", code="R_SYNC")
    current = (row.get("current_final122") or {}).get("current_subject") or {}
    _assert_triplet(current, target, label=f"{task_id} scope3 current")
    validation = row.get("validation")
    if not isinstance(validation, Mapping) or validation.get("missing_required_fields") != [] or any(
        value is not True for key, value in validation.items()
        if key != "missing_required_fields" and not key.endswith("cardinality")
    ):
        raise EvidenceBridgeError(f"{task_id}: source-scope validation is incomplete", code="R_SYNC")
    selector = row.get("historical_atomic_selector") or {}
    commit = str(selector.get("commit", "") or "")
    if not _HEX40.fullmatch(commit):
        raise EvidenceBridgeError(f"{task_id}: atomic selector commit is absent", code="R_SYNC")
    _run(Path(str(selector.get("repository", ""))).resolve(), "git", "cat-file", "-e", f"{commit}^{{commit}}")
    spec = (row.get("current_final122") or {}).get("spec")
    _check_file_ref(spec, label=f"{task_id} scope3 current spec")
    return {"source_schema": "SCOPE3", "authority_kind": "mat_sync_author_attested_selection", "decision_status": "pass"}


def _validate_pr5_project_selection(
    row: Mapping[str, Any], *, task_id: str, target: SubjectBundle,
) -> dict[str, Any]:
    if _row_task(row) != task_id or row.get("decision") != "RESOLVED_BY_EXISTING_DECISION":
        raise EvidenceBridgeError(f"{task_id}: PR5 project selection is not resolved", code="R_SYNC")
    _assert_triplet(row.get("current_subject", {}), target, label=f"{task_id} PR5 current")
    review = row.get("historical_review") or {}
    if review.get("verdict") != "pass" or review.get("verify_apply_success") is not True:
        raise EvidenceBridgeError(f"{task_id}: PR5 source review/apply is not valid", code="R_SOURCE_AUTHORITY")
    for key in ("result", "input", "verify_apply", "source_authority"):
        _check_file_ref(review.get(key), label=f"{task_id} PR5 historical {key}")
    decisions = row.get("immutable_decisions_examined") or {}
    pr5 = decisions.get("pr5_coordinated_project_selection") or {}
    if pr5.get("merged_by") != "Kind-NK-Hill" or not pr5.get("explicit_scope"):
        raise EvidenceBridgeError(f"{task_id}: PR5 owner/full-scope selection is incomplete", code="R_SYNC")
    if not all(_HEX40.fullmatch(str(pr5.get(key, "") or "")) for key in ("head_commit", "merge_commit")):
        raise EvidenceBridgeError(f"{task_id}: PR5 commit identity is incomplete", code="R_SYNC")
    return {"source_schema": "CH13_PR5", "authority_kind": "project_owner_current_selection", "decision_status": "pass"}


def _validate_special_author_sync(
    row: Mapping[str, Any], *, task_id: str, target: SubjectBundle,
) -> dict[str, Any]:
    if (
        _row_task(row) != task_id or row.get("disposition") != "TYPED_AUTHOR_SYNC_BRIDGE_CONSTRUCTIBLE"
        or row.get("genuine_new_user_decision_required") is not False
    ):
        raise EvidenceBridgeError(f"{task_id}: special author/sync bridge is not constructible", code="R_SYNC")
    current = row.get("current_target") or {}
    if (
        current.get("commit") != target.source_commit
        or current.get("subject_id") != target.subject_id
        or current.get("bundle_manifest_sha256") != target.bundle_hash
        or current.get("provenance_manifest_sha256") != target.primary_hash
        or current.get("owned_file_count") != len(target.files)
    ):
        raise EvidenceBridgeError(f"{task_id}: special current target mismatch", code="R_BUNDLE")
    review_fields = [
        name for name in ("historical_review", "historical_review_apply", "historical_review_context")
        if isinstance(row.get(name), Mapping) and row.get(name)
    ]
    if len(review_fields) != 1:
        raise EvidenceBridgeError(f"{task_id}: special historical tuple is ambiguous", code="R_SOURCE_AUTHORITY")
    review = row[review_fields[0]]
    candidate = str(review.get("candidate_sha256", "") or "")
    if not _HEX64.fullmatch(candidate):
        raise EvidenceBridgeError(f"{task_id}: special historical candidate is unbound", code="R_SOURCE_AUTHORITY")
    for key in ("input", "result", "verify"):
        _check_file_ref(review.get(key), label=f"{task_id} special historical {key}")
    result = review.get("result") or {}; verify = review.get("verify") or {}
    if str(result.get("decision", "")).upper() != "PASS":
        raise EvidenceBridgeError(f"{task_id}: special historical decision is not PASS", code="R_SOURCE_AUTHORITY")
    if review_fields[0] == "historical_review_apply" and (
        verify.get("success") is not True or verify.get("candidate_sha256") != candidate
    ):
        raise EvidenceBridgeError(f"{task_id}: special review/apply tuple is not exact-successful", code="R_SOURCE_AUTHORITY")
    selection = row.get("immutable_author_selection")
    if not isinstance(selection, Mapping) or not selection:
        raise EvidenceBridgeError(f"{task_id}: immutable author selection is missing", code="R_SYNC")
    scope_selection = selection.get("full_scope_build_verified_snapshot_commit") or selection
    if not isinstance(scope_selection, Mapping):
        raise EvidenceBridgeError(f"{task_id}: immutable full-scope selection is missing", code="R_SYNC")
    if not all(_HEX40.fullmatch(str(scope_selection.get(key, "") or "")) for key in ("commit", "tree")):
        raise EvidenceBridgeError(f"{task_id}: immutable selector commit/tree is incomplete", code="R_SYNC")
    full_scope = scope_selection.get("full_scope")
    if not isinstance(full_scope, list) or len(full_scope) != len(target.files):
        raise EvidenceBridgeError(f"{task_id}: immutable selector full scope is incomplete", code="R_SYNC")
    scope_hashes: set[str] = set()
    for entry in full_scope:
        if (
            not isinstance(entry, Mapping) or not str(entry.get("path", "") or "")
            or not _HEX40.fullmatch(str(entry.get("git_blob", "") or ""))
            or not _HEX64.fullmatch(str(entry.get("sha256", "") or ""))
        ):
            raise EvidenceBridgeError(f"{task_id}: immutable selector file binding is incomplete", code="R_SYNC")
        scope_hashes.add(str(entry["sha256"]))
    if len(scope_hashes) != len(full_scope) or candidate not in scope_hashes:
        raise EvidenceBridgeError(f"{task_id}: reviewed candidate is not uniquely bound in author scope", code="R_SYNC")
    if not str(row.get("bridge_reason", "") or "") or not row.get("fail_closed_conditions"):
        raise EvidenceBridgeError(f"{task_id}: special bridge scope is incomplete", code="R_SYNC")
    return {"source_schema": "SPECIAL_U3", "authority_kind": str(row.get("route", "")), "decision_status": "pass"}


def inspect_final122_minimal_index(
    index_path: Path, *, target_repo: Path, kenneth_repo: Path,
) -> dict[str, Any]:
    """Replay the final A/B closed-set pointer index without emitting anything."""

    index_path = index_path.expanduser().resolve(); target_repo = target_repo.resolve(); kenneth_repo = kenneth_repo.resolve()
    index = _read_json(index_path, label="final122 minimal index")
    if index.get("schema") not in {FINAL122_MINIMAL_INDEX_SCHEMA, "mat.catalog.final122-evidence-bridge-minimal-index.v2"}:
        raise EvidenceBridgeError("unsupported final122 minimal index", code="R_ROUTE")
    commit = str(index.get("target_commit", "") or "")
    if not _HEX40.fullmatch(commit):
        raise EvidenceBridgeError("final122 target commit is not pinned", code="R_FRESHNESS")
    kenneth_commit = str((index.get("inputs") or {}).get("A61", {}).get("path", ""))
    # The Kenneth commit is authoritative in A61; resolve it below after the input hash is checked.
    inputs = index.get("inputs"); outputs = index.get("outputs"); counts = index.get("counts")
    if not all(isinstance(value, Mapping) for value in (inputs, outputs, counts)):
        raise EvidenceBridgeError("final122 index sections are incomplete", code="R_SOURCE_AUTHORITY")
    registered_refs: dict[Path, str] = {}
    source_docs: dict[Path, Mapping[str, Any]] = {}

    def register_inputs(raw_inputs: Mapping[str, Any], *, lineage: str) -> None:
        for name, ref in raw_inputs.items():
            checked = _check_file_ref(ref, label=f"{lineage} input {name}")
            path = Path(checked["path"]); digest = checked["sha256"]
            previous = registered_refs.get(path)
            if previous is not None and previous != digest:
                raise EvidenceBridgeError("transitive source registry has conflicting hashes", code="R_IMMUTABILITY")
            registered_refs[path] = digest
            if path.suffix.lower() != ".json":
                continue
            document = _read_json(path, label=f"{lineage} input {name}")
            source_docs[path] = document
            if document.get("schema") in {
                FINAL122_MINIMAL_INDEX_SCHEMA, "mat.catalog.final122-evidence-bridge-minimal-index.v2",
            }:
                nested = document.get("inputs")
                if not isinstance(nested, Mapping):
                    raise EvidenceBridgeError("nested final122 index inputs are missing", code="R_IMMUTABILITY")
                register_inputs(nested, lineage=f"{lineage}/{name}")

    register_inputs(inputs, lineage="final122")
    matched_names: dict[str, str] = {}
    for category, pattern in (("A", r"A\d+"), ("B", r"B\d+"), ("U", r"unresolved\d+")):
        names = [name for name in outputs if re.fullmatch(pattern, str(name))]
        if len(names) != 1:
            raise EvidenceBridgeError(f"final122 index must have one {category} output", code="R_ROUTE")
        matched_names[category] = names[0]
    sets: dict[str, list[Mapping[str, Any]]] = {}
    for category, name in matched_names.items():
        ref = outputs.get(name); checked = _check_file_ref(ref, label=f"final122 output {name}")
        sets[category] = _read_jsonl(Path(checked["path"]), expected_hash=checked["sha256"])
        declared = int(ref.get("count", -1))
        suffix = int(re.search(r"\d+$", name).group())
        if declared != len(sets[category]) or suffix != len(sets[category]):
            raise EvidenceBridgeError(f"final122 {name} count mismatch", code="R_SOURCE_AUTHORITY")
    id_sets = {name: {_row_task(row) for row in rows} for name, rows in sets.items()}
    if any(len(ids) != len(sets[name]) or "" in ids for name, ids in id_sets.items()):
        raise EvidenceBridgeError("final122 set has invalid or duplicate task ids", code="R_SOURCE_AUTHORITY")
    if (id_sets["A"] & id_sets["B"] or id_sets["A"] & id_sets["U"]
            or id_sets["B"] & id_sets["U"] or len(set().union(*id_sets.values())) != 122):
        raise EvidenceBridgeError("final122 A/B/U sets are not a disjoint 122 partition", code="R_ROUTE")

    authority_rows = sets["A"] + sets["B"]
    catalog = _load_bridge_catalog(target_repo, commit)
    imports, modules_by_name = _catalog_import_index(catalog=catalog, target_repo=target_repo, commit=commit)
    consumer_scope = {
        _row_task(row): _direct_consumer_closure(
            task_id=_row_task(row), catalog=catalog, imports=imports, modules_by_name=modules_by_name,
        ) for row in authority_rows
    }
    commit_roots = {Path(str(row["exact_build_receipt"]["path"])).resolve().parent.parent for row in authority_rows}
    if len(commit_roots) != 1:
        raise EvidenceBridgeError("minimal target builds do not share one central commit root", code="R_BUILD_SCAN")
    central_commit_root = next(iter(commit_roots))
    for scope in consumer_scope.values():
        coverage_tasks: set[str] = set()
        for shared, owners in scope["unowned_module_coverage"].items():
            available = sorted(
                owner for owner in owners
                if (central_commit_root / owner / "exact_mat_build_receipt_v1.json").is_file()
            )
            if not available:
                raise EvidenceBridgeError(
                    f"unowned direct consumer {shared} has no exact-built task-owned import coverage",
                    code="R_BUILD_SCAN",
                )
            scope["unowned_module_coverage"][shared] = available
            coverage_tasks.update(available)
        scope["unowned_coverage_task_ids"] = sorted(coverage_tasks)
    all_build_tasks = sorted({
        task for row in authority_rows
        for task in [
            _row_task(row), *consumer_scope[_row_task(row)]["consumer_task_ids"],
            *consumer_scope[_row_task(row)]["unowned_coverage_task_ids"],
        ]
    })
    context = _exact_catalog_context(target_repo=target_repo, commit=commit, task_ids=all_build_tasks)
    a61_matches = [
        (path, document) for path, document in source_docs.items()
        if document.get("schema") == KENNETH_BATCH_AUTHORITY_SCHEMA
    ]
    if len(a61_matches) != 1:
        raise EvidenceBridgeError("transitive registry must contain exactly one A61 authority manifest", code="R_ROUTE")
    a61_path, a61 = a61_matches[0]
    kenneth_commit = str((a61.get("anchors") or {}).get("kenneth_commit", "") or "")
    a61_inspect = inspect_kenneth_authority_manifest(
        a61_path, target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    a61_results = {item["task_id"]: item for item in a61_inspect["items"]}

    validated_builds: dict[Path, str] = {}
    item_results: list[dict[str, Any]] = []
    for minimal in authority_rows:
        task_id = _row_task(minimal); declared_route = str(minimal.get("route", "") or "")
        in_a = minimal in sets["A"]
        route = ROUTE_A if in_a else ROUTE_B
        allowed_routes = (
            {ROUTE_A, "kenneth_author_exact_existing_decision_bridge"}
            if in_a else
            {ROUTE_B, "existing_mat_sync_reassembly_decision_bridge",
             "immutable_full_source_scope_selection_bridge", "explicit_branch_decision_provenance_bridge"}
            | {"author_full_scope_build_verified_snapshot_selection_then_reviewed_sync_reassembly",
               "project_author_pr5_mat_only_full_scope_selection_bridge",
               "successful_review_apply_plus_author_full_scope_snapshot_then_reviewed_sync_reassembly",
               "project_author_pr5_proof_only_reassembly_selection_bridge",
               "author_atomic_full_scope_selection_then_reviewed_sync_reassembly"}
        )
        if declared_route not in allowed_routes:
            raise EvidenceBridgeError(f"{task_id}: minimal route/set mismatch", code="R_ROUTE")
        target = context["subjects"].get(task_id)
        if not isinstance(target, SubjectBundle):
            raise EvidenceBridgeError(f"{task_id}: current catalog subject is missing", code="R_BUNDLE")
        _assert_triplet(minimal.get("target", {}), target, label=f"{task_id} minimal target")
        source_ref = minimal.get("source_manifest")
        checked_source = _check_file_ref(source_ref, label=f"{task_id} source manifest")
        source_path = Path(checked_source["path"])
        if registered_refs.get(source_path) != checked_source["sha256"] or source_path not in source_docs:
            raise EvidenceBridgeError(f"{task_id}: source manifest is outside indexed registry", code="R_SOURCE_AUTHORITY")
        source_payload = source_docs[source_path]
        pointed = _json_pointer(source_payload, str(source_ref.get("item_pointer", "") or ""))
        if not isinstance(pointed, Mapping) or _row_task(pointed) != task_id:
            raise EvidenceBridgeError(f"{task_id}: source item pointer mismatch", code="R_SOURCE_AUTHORITY")
        schema = str(source_payload.get("schema", "") or "")
        if schema == KENNETH_BATCH_AUTHORITY_SCHEMA:
            result = a61_results.get(task_id)
            if not isinstance(result, Mapping) or result.get("framework_authority_ready") is not True:
                raise EvidenceBridgeError(f"{task_id}: A61 authority replay failed", code="R_KENNETH")
            _assert_triplet(pointed.get("current", {}), target, label=f"{task_id} A61 current")
            authority = {"source_schema": "A61", "authority_kind": result.get("normalized_exactness_mode"), "decision_status": "pass"}
        elif schema == "mat.catalog.reviewed-sync-reassembly-bridge-action-manifest.v1":
            authority = _validate_b39_authority(pointed, task_id=task_id, target=target)
        elif schema == "mat.current-c-existing-decision-deep-audit.v1":
            authority = _validate_c8_authority(
                pointed, task_id=task_id, route=route, target=target,
                target_repo=target_repo, kenneth_repo=kenneth_repo, kenneth_commit=kenneth_commit,
            )
        elif schema == "mat.ch12_14.current-decision-deep-audit.v1":
            authority = _validate_ch12_authority(source_payload, pointed, task_id=task_id, target=target)
        elif schema == "mat.catalog.source-scope-author-attested-selection-audit.v1":
            authority = _validate_scope3_authority(pointed, task_id=task_id, target=target, target_repo=target_repo)
        elif schema == "mat.catalog.existing-author-project-decision-deep-dive.v1":
            authority = _validate_pr5_project_selection(pointed, task_id=task_id, target=target)
        elif schema == "special_unresolved_immutable_decision_bridge_audit_v1":
            authority = _validate_special_author_sync(pointed, task_id=task_id, target=target)
        else:
            raise EvidenceBridgeError(f"{task_id}: source schema is not registered: {schema}", code="R_ROUTE")

        build_ref = minimal.get("exact_build_receipt")
        checked_build = _check_file_ref(build_ref, label=f"{task_id} target exact build")
        build_path = Path(checked_build["path"])
        _validate_context_exact_build(build_path, task_id=task_id, context=context)
        if hashlib.sha256(build_path.read_bytes()).hexdigest() != checked_build["sha256"]:
            raise EvidenceBridgeError(f"{task_id}: target build snapshot changed during replay", code="R_IMMUTABILITY")
        validated_builds[build_path] = checked_build["sha256"]
        commit_root = central_commit_root
        consumer_builds: list[dict[str, str]] = []
        required_consumers = sorted(set(
            consumer_scope[task_id]["consumer_task_ids"]
            + consumer_scope[task_id]["unowned_coverage_task_ids"]
        ))
        for consumer in required_consumers:
            path = commit_root / consumer / "exact_mat_build_receipt_v1.json"
            if not path.is_file():
                raise EvidenceBridgeError(f"{task_id}: consumer {consumer} exact build is missing", code="R_BUILD_SCAN")
            digest = sha256_file(path)
            _validate_context_exact_build(path, task_id=consumer, context=context)
            if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise EvidenceBridgeError(f"{consumer}: consumer build snapshot changed during replay", code="R_IMMUTABILITY")
            previous = validated_builds.get(path)
            if previous is not None and previous != digest:
                raise EvidenceBridgeError("central exact-build path has conflicting bytes", code="R_IMMUTABILITY")
            validated_builds[path] = digest
            consumer_builds.append({"task_id": consumer, "path": str(path), "sha256": digest})
        item_results.append({
            "task_id": task_id, "route": route, "declared_route": declared_route,
            "status": "ready_for_receipt_emission",
            "target": subject_payload(target), "source_manifest": {**checked_source, "item_pointer": source_ref["item_pointer"]},
            "source_authority": authority, "target_exact_build": checked_build,
            "direct_consumers": consumer_scope[task_id], "consumer_exact_builds": consumer_builds,
        })

    rejected: list[dict[str, Any]] = []
    for minimal in sets["U"]:
        task_id = _row_task(minimal)
        if minimal.get("authority_status") != "UNRESOLVED" or minimal.get("semantic_status") != "NOT_ADJUDICATED":
            raise EvidenceBridgeError(f"{task_id}: unresolved row does not fail closed", code="R_ROUTE")
        ref = minimal.get("source_manifest"); checked = _check_file_ref(ref, label=f"{task_id} unresolved source")
        source = source_docs.get(Path(checked["path"]))
        pointed = _json_pointer(source, str(ref.get("item_pointer", "") or "")) if source else None
        missing = minimal.get("precise_missing_decision") or {}
        if (
            not isinstance(pointed, Mapping) or _row_task(pointed) != task_id
            or str(pointed.get("finding", "")) != str(missing.get("finding", ""))
            or not str(missing.get("gap", "") or "")
            or "EXPLICIT_BRANCH_DECISION_FOUND" in str(pointed.get("finding", ""))
        ):
            raise EvidenceBridgeError(f"{task_id}: unresolved evidence pointer is not fail-closed", code="R_ROUTE")
        rejected.append({"task_id": task_id, "status": "rejected_closed_set_C", "reason": minimal.get("precise_missing_decision")})

    return {
        "schema": "toy-apollo.final122-evidence-bridge-inspect.v1",
        "status": "inspect_only_no_receipt_emitted", "index": _ref(index_path),
        "target_commit": commit,
        "repositories": {
            "target": {
                "path": str(target_repo), "commit": commit,
                "tree": str(a61_inspect["anchors"]["mat_tree"]),
            },
            "kenneth": {
                "path": str(kenneth_repo), "commit": kenneth_commit,
                "tree": str(a61_inspect["anchors"]["kenneth_tree"]),
            },
        },
        "summary": {"authority_ready": len(item_results), "A_ready": len(sets["A"]), "B_ready": len(sets["B"]),
                    "closed_set_rejected": len(rejected), "unique_exact_build_receipts": len(validated_builds)},
        "items": sorted(item_results, key=lambda item: item["task_id"]),
        "rejected": sorted(rejected, key=lambda item: item["task_id"]),
    }


def build_final122_bridge_batch_receipt(
    index_path: Path, *, target_repo: Path, kenneth_repo: Path, created_at: str,
) -> dict[str, Any]:
    inspected = inspect_final122_minimal_index(index_path, target_repo=target_repo, kenneth_repo=kenneth_repo)
    item_receipts = []
    for item in inspected["items"]:
        target = item["target"]
        authority_type = AUTHORITY_KENNETH if item["route"] == ROUTE_A else AUTHORITY_MAT_SYNC
        item_receipts.append({
            "schema": EVIDENCE_BRIDGE_SCHEMA, "task_id": item["task_id"], "created_at": created_at,
            "bridge_route": item["route"], "transformation_kind": TRANSFORMATION_KIND,
            "authority_scope": "final122_existing_decision_evidence_bridge",
            "mechanical_status": "pass", "semantic_upgrade": False, "rubric_upgrade": False, "creates_review": False,
            "source_authority": {"type": authority_type, "capability": CAPABILITY_BY_AUTHORITY[authority_type],
                                 "decision": item["source_manifest"], "source_evidence_hash": item["source_manifest"]["sha256"]},
            "source_subject": target, "target_subject": target,
            "decision": item["source_authority"],
            "scope": {"source_file_count": len(target["files"]), "target_file_count": len(target["files"]),
                      "complete_source": True, "complete_target": True, "identity_authority_attachment": True},
            "comparison": {"status": "pass", "mode": "pointer_replayed_existing_decision"},
            "proof_support_manifest": {"complete_scope": True, "ownership_partition": "pass", "carrier_closure": "pass"},
            "dependencies": {"direct_consumers": item["direct_consumers"]},
            "artifacts": {"target_build": item["target_exact_build"], "consumer_builds": item["consumer_exact_builds"]},
            "checks": {key: "pass" for key in _PASS_CHECKS},
            "orchestration": {"final122_minimal_index": inspected["index"], "source_manifest": item["source_manifest"]},
        })
    return {"schema": FINAL122_BATCH_RECEIPT_SCHEMA, "created_at": created_at,
            "target_commit": inspected["target_commit"], "index": inspected["index"],
            "repositories": inspected["repositories"],
            "count": len(item_receipts), "items": item_receipts}


def capture_final122_evidence_snapshot_graph(
    index_path: Path, *, snapshot_root: Path,
    additional_refs: Sequence[Mapping[str, Any]] = (),
) -> list[dict[str, dict[str, str]]]:
    """Capture the complete path/hash JSON graph from one read per source."""

    captured: dict[str, dict[str, dict[str, str]]] = {}

    def capture(path: Path, expected: str, *, supplied: bytes | None = None) -> None:
        original = path.expanduser().resolve()
        try:
            data = supplied if supplied is not None else original.read_bytes()
        except OSError as exc:
            raise EvidenceBridgeError(f"cannot capture evidence {original}: {exc}", code="R_IMMUTABILITY") from exc
        digest = hashlib.sha256(data).hexdigest()
        if not _HEX64.fullmatch(expected) or digest != expected:
            raise EvidenceBridgeError(f"snapshot source hash mismatch: {original}", code="R_IMMUTABILITY")
        key = str(original)
        previous = captured.get(key)
        if previous is not None:
            if previous["original"]["sha256"] != digest:
                raise EvidenceBridgeError("snapshot graph path has conflicting bytes", code="R_IMMUTABILITY")
            return
        suffix = original.suffix.lower() if original.suffix.lower() in {".json", ".jsonl"} else ".bin"
        snapshot = (snapshot_root.resolve() / "objects" / f"{digest}{suffix}").resolve()
        if snapshot.is_file():
            if snapshot.read_bytes() != data:
                raise EvidenceBridgeError("content-addressed snapshot collision mismatch", code="R_IMMUTABILITY")
        else:
            try:
                _atomic_publish_no_replace(snapshot, data, label="evidence bridge content-addressed snapshot")
            except BoundaryDeltaReceiptError as exc:
                if not snapshot.is_file() or snapshot.read_bytes() != data:
                    raise EvidenceBridgeError(str(exc), code="R_IMMUTABILITY") from exc
        entry = {
            "original": {"path": key, "sha256": digest},
            "snapshot": {"path": str(snapshot), "sha256": digest},
        }
        captured[key] = entry
        decoded: Any
        try:
            if suffix == ".jsonl":
                decoded = [json.loads(line) for line in data.decode("utf-8").splitlines() if line.strip()]
            elif suffix == ".json":
                decoded = json.loads(data.decode("utf-8"))
            else:
                return
        except (UnicodeDecodeError, json.JSONDecodeError):
            # Some hash-only provenance files use .json/.jsonl suffixes without
            # being authority documents. Preserve their exact bytes but do not
            # recursively interpret them; any consumed authority document is
            # still parsed strictly by its route-specific loader.
            return

        def walk(value: Any) -> None:
            if isinstance(value, Mapping):
                raw_path = value.get("path", value.get("absolute_path"))
                raw_hash = value.get("sha256")
                if isinstance(raw_path, str) and isinstance(raw_hash, str) and _HEX64.fullmatch(raw_hash):
                    child = Path(raw_path)
                    child = child if child.is_absolute() else original.parent / child
                    if child.is_file():
                        try:
                            child_bytes = child.read_bytes()
                        except OSError:
                            child_bytes = b""
                        if hashlib.sha256(child_bytes).hexdigest() == raw_hash:
                            capture(child, raw_hash, supplied=child_bytes)
                for nested in value.values():
                    walk(nested)
            elif isinstance(value, list):
                for nested in value:
                    walk(nested)

        walk(decoded)

    index_path = index_path.expanduser().resolve()
    try:
        index_bytes = index_path.read_bytes()
    except OSError as exc:
        raise EvidenceBridgeError(f"cannot capture final122 index: {exc}", code="R_IMMUTABILITY") from exc
    capture(index_path, hashlib.sha256(index_bytes).hexdigest(), supplied=index_bytes)
    for ref in additional_refs:
        raw_path = ref.get("path"); digest = str(ref.get("sha256", "") or "")
        if not isinstance(raw_path, str) or not _HEX64.fullmatch(digest):
            raise EvidenceBridgeError("additional snapshot reference is malformed", code="R_IMMUTABILITY")
        capture(Path(raw_path), digest)
    return [captured[key] for key in sorted(captured, key=str.lower)]


def validate_final122_bridge_batch_payload(
    payload: Mapping[str, Any], *, target_repo: Path, kenneth_repo: Path,
) -> dict[str, Any]:
    """Strictly replay an in-memory batch payload without publishing any artifact."""

    if payload.get("schema") != FINAL122_BATCH_RECEIPT_SCHEMA:
        raise EvidenceBridgeError("unsupported final122 bridge batch receipt", code="R_ROUTE")
    repositories = payload.get("repositories")
    if not isinstance(repositories, Mapping):
        raise EvidenceBridgeError("final122 repository anchors are missing", code="R_FRESHNESS")
    for name, supplied in (("target", target_repo.resolve()), ("kenneth", kenneth_repo.resolve())):
        anchor = repositories.get(name)
        if (
            not isinstance(anchor, Mapping)
            or Path(str(anchor.get("path", "") or "")).resolve() != supplied
            or not _HEX40.fullmatch(str(anchor.get("commit", "") or ""))
            or not _HEX40.fullmatch(str(anchor.get("tree", "") or ""))
        ):
            raise EvidenceBridgeError(f"final122 {name} repository root/anchor mismatch", code="R_FRESHNESS")
        actual_tree = _run(supplied, "git", "rev-parse", f"{anchor['commit']}^{{tree}}").decode().strip()
        if actual_tree != anchor["tree"]:
            raise EvidenceBridgeError(f"final122 {name} repository tree mismatch", code="R_FRESHNESS")
    graph = payload.get("evidence_snapshot_graph")
    entries = graph if isinstance(graph, list) else []
    snapshot_root_raw = payload.get("evidence_snapshot_root")
    snapshot_root = Path(str(snapshot_root_raw)).resolve() if entries and snapshot_root_raw else None
    if entries and snapshot_root is None:
        raise EvidenceBridgeError("formal snapshot root is missing", code="R_IMMUTABILITY")
    with _snapshot_resolution(entries, expected_root=snapshot_root):
        checked_index = _check_file_ref(payload.get("index"), label="final122 minimal index")
        rebuilt = build_final122_bridge_batch_receipt(
            Path(checked_index["path"]), target_repo=target_repo, kenneth_repo=kenneth_repo,
            created_at=str(payload.get("created_at", "") or ""),
        )
    if entries:
        rebuilt["evidence_snapshot_graph"] = entries
        rebuilt["evidence_snapshot_root"] = str(snapshot_root)
    if sha256_json(payload) != sha256_json(rebuilt):
        raise EvidenceBridgeError("final122 bridge batch receipt differs from strict replay", code="R_IMMUTABILITY")
    return rebuilt


def load_validated_final122_bridge_batch_receipt(
    receipt_path: Path, *, target_repo: Path, kenneth_repo: Path,
) -> tuple[dict[str, Any], str]:
    receipt_path = receipt_path.resolve()
    try:
        receipt_bytes = receipt_path.read_bytes()
        payload = json.loads(receipt_bytes.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceBridgeError(f"cannot read final122 batch receipt: {exc}", code="R_IMMUTABILITY") from exc
    if not isinstance(payload, Mapping) or not isinstance(payload.get("evidence_snapshot_graph"), list):
        raise EvidenceBridgeError("formal final122 batch lacks snapshot graph", code="R_IMMUTABILITY")
    rebuilt = validate_final122_bridge_batch_payload(
        payload, target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    return rebuilt, hashlib.sha256(receipt_bytes).hexdigest()


def validate_final122_bridge_batch_receipt(
    receipt_path: Path, *, target_repo: Path, kenneth_repo: Path,
) -> dict[str, Any]:
    payload, _digest = load_validated_final122_bridge_batch_receipt(
        receipt_path, target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    return payload


def emit_final122_bridge_batch_receipt(
    index_path: Path, output_path: Path, *, target_repo: Path, kenneth_repo: Path, created_at: str,
) -> dict[str, Any]:
    output_path = output_path.resolve()
    preflight_payload = build_final122_bridge_batch_receipt(
        index_path, target_repo=target_repo, kenneth_repo=kenneth_repo, created_at=created_at,
    )
    additional_refs = [
        ref
        for item in preflight_payload["items"]
        for ref in [
            item["source_authority"]["decision"],
            item["artifacts"]["target_build"],
            *item["artifacts"]["consumer_builds"],
        ]
    ]
    graph = capture_final122_evidence_snapshot_graph(
        index_path, snapshot_root=output_path.parent / "_evidence",
        additional_refs=additional_refs,
    )
    snapshot_root = output_path.parent / "_evidence"
    with _snapshot_resolution(graph, expected_root=snapshot_root):
        payload = build_final122_bridge_batch_receipt(
            index_path, target_repo=target_repo, kenneth_repo=kenneth_repo, created_at=created_at,
        )
    payload["evidence_snapshot_graph"] = graph
    payload["evidence_snapshot_root"] = str(snapshot_root.resolve())
    validate_final122_bridge_batch_payload(
        payload, target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    raw = (json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")
    # Complete snapshot replay immediately precedes immutable publication.
    validate_final122_bridge_batch_payload(
        payload, target_repo=target_repo, kenneth_repo=kenneth_repo,
    )
    published = _atomic_publish_no_replace(output_path, raw, label="final122 evidence bridge batch receipt")
    return {"status": "emitted" if published.get("published") else "already_existing",
            "path": str(output_path), "sha256": hashlib.sha256(raw).hexdigest(), "count": payload["count"]}
