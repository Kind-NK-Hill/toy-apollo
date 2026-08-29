"""Fail-closed recovery of an exact review invalidated by a repaired dependency.

This is deliberately narrower than review-apply: it never creates a semantic
verdict.  It only connects an existing p9/10/11+r9 clean PASS to the *current*
MAT subject when the old apply receipt was rejected solely by ``invalidated_by``
and fresh, hash-addressed build evidence proves the invalidator and every
current direct consumer are now healthy.
"""

from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.block_id_naming import canonicalize_block_id, is_canonical_block_id

from .phase2_review_decision import evaluate_semantic_review_result
from .phase2_semantic_review import _validate_review_input_internal_binding
from .state_store import SubjectBundle, sha256_file, sha256_json


RESOLVED_INVALIDATION_SCHEMA = "toy-apollo.resolved-invalidation-current-exact-recovery.v1"
RESOLVED_INVALIDATION_AUTHORITY_SCOPE = "resolved_invalidation_current_exact_recovery"
_HEX = re.compile(r"[0-9a-f]{64}")


class ResolvedInvalidationRecoveryError(ValueError):
    pass


def _read(path: Path) -> Mapping[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ResolvedInvalidationRecoveryError(f"cannot read JSON evidence {path}: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ResolvedInvalidationRecoveryError(f"JSON evidence is not an object: {path}")
    return value


def _reference(path: Path) -> dict[str, str]:
    return {"path": str(path.resolve()), "sha256": sha256_file(path)}


def _path(owner: Path, raw: Mapping[str, Any] | str, label: str) -> Path:
    raw_path = raw.get("path", "") if isinstance(raw, Mapping) else raw
    candidate = Path(str(raw_path or "")).expanduser()
    if not candidate.is_absolute():
        candidate = owner.parent / candidate
    candidate = candidate.resolve()
    if not candidate.is_file():
        raise ResolvedInvalidationRecoveryError(f"{label} is missing: {candidate}")
    if isinstance(raw, Mapping):
        expected = str(raw.get("sha256", "") or "")
        if not _HEX.fullmatch(expected) or sha256_file(candidate) != expected:
            raise ResolvedInvalidationRecoveryError(f"{label} hash mismatch")
    return candidate


def _subject(raw: Any, *, task_id: str, label: str) -> SubjectBundle:
    if not isinstance(raw, Mapping):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: {label} subject is missing")
    try:
        subject = SubjectBundle.from_manifest(
            task_id=task_id,
            files=raw.get("files", raw.get("subject_files", [])),
            primary_path=str(raw.get("primary_path", "") or ""),
            source_repo=str(raw.get("source_repo", "mat") or "mat"),
            source_commit=str(raw.get("source_commit", raw.get("commit", "")) or ""),
            layout=str(raw.get("layout", "mat") or "mat"),
            subject_kind=str(raw.get("subject_kind", "catalog_git_bundle") or "catalog_git_bundle"),
        )
    except (TypeError, ValueError) as exc:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: invalid {label} subject: {exc}") from exc
    for key, actual in (("subject_id", subject.subject_id), ("bundle_hash", subject.bundle_hash), ("primary_hash", subject.primary_hash)):
        declared = str(raw.get(key, "") or "")
        if declared and declared != actual:
            raise ResolvedInvalidationRecoveryError(f"{task_id}: {label} {key} mismatch")
    return subject


def _input_and_result(pack: Path, stale: Mapping[str, Any]) -> tuple[Path, Mapping[str, Any], Path, Mapping[str, Any], SubjectBundle]:
    task_id = canonicalize_block_id(str(stale.get("task_id", "") or ""))
    result_path = _path(pack / "receipt.json", str(stale.get("review_result_file", "") or ""), "review result")
    result = _read(result_path)
    if canonicalize_block_id(str(result.get("task_id", "") or "")) != task_id:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: review result task mismatch")
    if sha256_file(result_path) != str(stale.get("review_result_hash", "") or ""):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: stale receipt review result hash mismatch")
    input_path = _path(result_path, str(result.get("review_input_file", "") or ""), "review input")
    review_input = _read(input_path)
    input_hash = sha256_json(review_input)
    if input_hash != str(result.get("review_input_hash", "") or "") or input_hash != str(stale.get("review_input_hash", "") or ""):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: review input hash mismatch")
    if _validate_review_input_internal_binding(dict(review_input)):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: review input binding is invalid")
    if int(result.get("prompt_version", 0) or 0) not in {9, 10, 11} or int(result.get("rubric_version", 0) or 0) != 9:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: review is not modern compatible")
    if str(result.get("verdict", "") or "").lower() != "pass" or str(result.get("phase2_status", "") or "").lower() != "pass":
        raise ResolvedInvalidationRecoveryError(f"{task_id}: review is not a clean PASS")
    decision = evaluate_semantic_review_result(dict(result), review_input=dict(review_input), runner_metadata={"status": "resolved-invalidation-validation"})
    if not decision.is_semantic_verdict or not decision.is_clean_pass or decision.task_status_projection is None:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: semantic result does not project a clean PASS")
    raw_subject = review_input.get("subject_bundle")
    source = _subject(raw_subject, task_id=task_id, label="review input")
    if str(result.get("candidate_hash", "") or "") != source.primary_hash:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: candidate hash mismatch")
    version_match = re.fullmatch(r"semantic_review_result_v(\d+)\.json", result_path.name, re.IGNORECASE)
    if version_match is None:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: review result is not an immutable versioned artifact")
    current_version = int(version_match.group(1))
    # A later result is allowed only when it is the same clean semantic PASS;
    # any changed candidate/input or later non-pass is a semantic conflict and
    # must go through an independent new review rather than this recovery.
    for later_path in sorted(result_path.parent.glob("semantic_review_result_v*.json")):
        match = re.fullmatch(r"semantic_review_result_v(\d+)\.json", later_path.name, re.IGNORECASE)
        if match is None or int(match.group(1)) <= current_version:
            continue
        later = _read(later_path)
        if (
            str(later.get("verdict", "") or "").lower() != "pass"
            or str(later.get("phase2_status", "") or "").lower() != "pass"
            or str(later.get("review_input_hash", "") or "") != input_hash
            or str(later.get("candidate_hash", "") or "") != source.primary_hash
        ):
            raise ResolvedInvalidationRecoveryError(
                f"{task_id}: later semantic evidence conflicts with the stale receipt"
            )
    return result_path, result, input_path, review_input, source


def _exact_build(path: Path, *, task_id: str, expected: SubjectBundle | None, commit: str) -> tuple[Mapping[str, Any], SubjectBundle]:
    payload = _read(path)
    if payload.get("schema") != "mat.catalog.exact-build.v1" or payload.get("success") is not True or payload.get("exit_code") != 0:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: build evidence is not a successful exact-MAT build")
    if str(payload.get("task_id", "") or "") != task_id:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: build evidence task mismatch")
    forbidden = payload.get("forbidden_token_scan")
    if not isinstance(forbidden, Mapping) or forbidden.get("exit_code") != 0 or forbidden.get("findings") not in ({}, []):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: forbidden-token scan is not clean")
    subject = _subject({
        "subject_id": payload.get("subject_id"), "bundle_hash": payload.get("bundle_hash"),
        "primary_hash": payload.get("primary_hash"), "primary_path": payload.get("primary_path"),
        "files": payload.get("subject_files"), "source_repo": "mat", "source_commit": payload.get("commit"),
        "layout": "mat", "subject_kind": "catalog_git_bundle",
    }, task_id=task_id, label="build")
    if subject.source_commit != commit:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: build evidence is not bound to the target commit")
    if expected is not None and (subject.subject_id != expected.subject_id or subject.bundle_hash != expected.bundle_hash):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: build subject does not match the declared current target")
    tree = payload.get("lean_tree_equivalence")
    if not isinstance(tree, Mapping) or tree.get("target_commit") != commit or tree.get("build_checkout_clean") is not True or tree.get("changed_lean_files") != []:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: exact build lacks clean full-Lean-tree equivalence")
    return payload, subject


def _consumer_manifest(path: Path, *, task_id: str, target: SubjectBundle) -> tuple[Mapping[str, Any], list[str]]:
    payload = _read(path)
    if payload.get("schema") != "mat.catalog.direct-consumer-manifest.v1":
        raise ResolvedInvalidationRecoveryError(f"{task_id}: unsupported direct-consumer manifest")
    expected = {"task_id": task_id, "commit": target.source_commit, "subject_id": target.subject_id, "bundle_hash": target.bundle_hash}
    if any(str(payload.get(key, "") or "") != value for key, value in expected.items()):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: direct-consumer manifest target mismatch")
    consumers = payload.get("consumers")
    if not isinstance(consumers, list):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: direct-consumer manifest is malformed")
    ids: list[str] = []
    for entry in consumers:
        if not isinstance(entry, Mapping):
            raise ResolvedInvalidationRecoveryError(f"{task_id}: malformed direct consumer")
        consumer = canonicalize_block_id(str(entry.get("task_id", "") or ""))
        if not consumer or not is_canonical_block_id(consumer):
            raise ResolvedInvalidationRecoveryError(f"{task_id}: consumer lacks canonical task id")
        ids.append(consumer)
    if len(ids) != len(set(ids)):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: duplicate direct consumer")
    return payload, sorted(ids)


def build_resolved_invalidation_recovery(*, stale_receipt_path: Path, target_build_path: Path, invalidator_build_paths: Sequence[Path], consumer_manifest_path: Path, consumer_build_paths: Sequence[Path], created_at: str | None = None) -> dict[str, Any]:
    stale_receipt_path = stale_receipt_path.resolve()
    stale = _read(stale_receipt_path)
    task_id = canonicalize_block_id(str(stale.get("task_id", "") or ""))
    if not task_id or not is_canonical_block_id(task_id) or stale.get("schema") != "mat.rubric78.review-apply-receipt.v1":
        raise ResolvedInvalidationRecoveryError("stale receipt is not a canonical MAT review-apply receipt")
    invalidator = canonicalize_block_id(str(stale.get("invalidated_by", "") or ""))
    if not invalidator or not is_canonical_block_id(invalidator):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: stale receipt has no canonical invalidated_by target")
    if stale.get("clean_pass") is not True or stale.get("exact_bundle_covered") is not True or str(stale.get("verdict", "") or "").lower() != "pass":
        raise ResolvedInvalidationRecoveryError(f"{task_id}: stale receipt was not an exact clean PASS")
    result_path, result, input_path, review_input, source = _input_and_result(stale_receipt_path.parent, stale)
    if source.bundle_hash != str(stale.get("bundle_hash", "") or "") or source.primary_hash != str(stale.get("primary_hash", "") or ""):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: stale receipt does not bind its reviewed subject")
    target_build, target = _exact_build(target_build_path.resolve(), task_id=task_id, expected=None, commit=str(_read(target_build_path.resolve()).get("commit", "") or ""))
    if target.bundle_hash != source.bundle_hash or target.primary_hash != source.primary_hash:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: current target content differs from the reviewed exact bundle")
    if target.source_repo != "mat" or not re.fullmatch(r"[0-9a-f]{40}", target.source_commit):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: target is not a pinned MAT commit")
    if not invalidator_build_paths:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: invalidator build evidence is required")
    resolved_invalidators: list[dict[str, str]] = []
    seen_invalidators: set[str] = set()
    for item in invalidator_build_paths:
        payload = _read(item.resolve())
        item_id = canonicalize_block_id(str(payload.get("task_id", "") or ""))
        if not item_id:
            raise ResolvedInvalidationRecoveryError(f"{task_id}: invalidator build has no task id")
        _exact_build(item.resolve(), task_id=item_id, expected=None, commit=target.source_commit)
        resolved_invalidators.append({"task_id": item_id, **_reference(item.resolve())})
        seen_invalidators.add(item_id)
    if seen_invalidators != {invalidator}:
        raise ResolvedInvalidationRecoveryError(f"{task_id}: invalidator evidence must cover exactly {invalidator}")
    manifest, consumer_ids = _consumer_manifest(consumer_manifest_path.resolve(), task_id=task_id, target=target)
    builds: dict[str, dict[str, str]] = {}
    for item in consumer_build_paths:
        payload = _read(item.resolve())
        item_id = canonicalize_block_id(str(payload.get("task_id", "") or ""))
        if not item_id or item_id in builds:
            raise ResolvedInvalidationRecoveryError(f"{task_id}: duplicate or invalid consumer build")
        _exact_build(item.resolve(), task_id=item_id, expected=None, commit=target.source_commit)
        builds[item_id] = {"task_id": item_id, **_reference(item.resolve())}
    if set(consumer_ids) != set(builds):
        raise ResolvedInvalidationRecoveryError(f"{task_id}: every and only current direct consumer needs focused build evidence")
    timestamp = created_at or datetime.now(timezone.utc).isoformat()
    return {
        "schema": RESOLVED_INVALIDATION_SCHEMA, "task_id": task_id, "created_at": timestamp,
        "recovery_kind": "resolved_dependency_invalidation_current_exact", "semantic_upgrade": False,
        "authority_scope": RESOLVED_INVALIDATION_AUTHORITY_SCOPE,
        "source_review": {"review_id": str(stale.get("review_id", "") or ""), "result_hash": sha256_file(result_path), "review_input_hash": sha256_json(review_input), "prompt_version": int(result.get("prompt_version", 0) or 0), "rubric_version": int(result.get("rubric_version", 0) or 0), "proof_class": str(result.get("proof_class", "") or ""), "completion_class": str(result.get("completion_class", "") or ""), "reviewer_independence": result.get("reviewer_independence", {}), "reviewer_backend_id": str(result.get("reviewer_backend_id", "") or "")},
        "source_subject": {"task_id": source.task_id, "subject_id": source.subject_id, "subject_kind": source.subject_kind, "source_repo": source.source_repo, "source_commit": source.source_commit, "layout": source.layout, "bundle_hash": source.bundle_hash, "primary_hash": source.primary_hash, "primary_path": source.primary_path, "files": source.manifest()},
        "target_subject": {"task_id": target.task_id, "subject_id": target.subject_id, "subject_kind": target.subject_kind, "source_repo": target.source_repo, "source_commit": target.source_commit, "layout": target.layout, "bundle_hash": target.bundle_hash, "primary_hash": target.primary_hash, "primary_path": target.primary_path, "files": target.manifest()},
        "artifacts": {"stale_receipt": _reference(stale_receipt_path), "result": _reference(result_path), "input": _reference(input_path), "target_build": _reference(target_build_path.resolve()), "consumer_manifest": _reference(consumer_manifest_path.resolve())},
        "resolution": {"invalidated_by": invalidator, "invalidator_builds": sorted(resolved_invalidators, key=lambda x: x["task_id"]), "consumer_builds": [builds[key] for key in sorted(builds)]},
        "checks": {"existing_modern_clean_pass": "pass", "source_target_content_exact": "pass", "current_target_build_and_forbidden_scan": "pass", "invalidator_repaired_build_and_forbidden_scan": "pass", "direct_consumers_built_and_scanned": "pass", "no_new_semantic_verdict": "pass", "target_build_schema": target_build.get("schema"), "consumer_manifest_schema": manifest.get("schema")},
    }


def validate_resolved_invalidation_recovery(receipt_path: Path, receipt: Mapping[str, Any] | None = None) -> tuple[dict[str, Any], SubjectBundle, Path, Path]:
    receipt_path = receipt_path.resolve()
    payload = dict(receipt or _read(receipt_path))
    if payload.get("schema") != RESOLVED_INVALIDATION_SCHEMA:
        raise ResolvedInvalidationRecoveryError("unsupported resolved-invalidation recovery schema")
    artifacts = payload.get("artifacts")
    resolution = payload.get("resolution")
    if not isinstance(artifacts, Mapping) or not isinstance(resolution, Mapping):
        raise ResolvedInvalidationRecoveryError("resolved-invalidation receipt is incomplete")
    stale_path = _path(receipt_path, artifacts.get("stale_receipt", {}), "stale receipt")
    target_build = _path(receipt_path, artifacts.get("target_build", {}), "target build")
    manifest = _path(receipt_path, artifacts.get("consumer_manifest", {}), "consumer manifest")
    invalidator_paths = [_path(receipt_path, item, "invalidator build") for item in resolution.get("invalidator_builds", []) if isinstance(item, Mapping)]
    consumer_paths = [_path(receipt_path, item, "consumer build") for item in resolution.get("consumer_builds", []) if isinstance(item, Mapping)]
    rebuilt = build_resolved_invalidation_recovery(stale_receipt_path=stale_path, target_build_path=target_build, invalidator_build_paths=invalidator_paths, consumer_manifest_path=manifest, consumer_build_paths=consumer_paths, created_at=str(payload.get("created_at", "") or ""))
    if sha256_json(payload) != sha256_json(rebuilt):
        raise ResolvedInvalidationRecoveryError("resolved-invalidation receipt does not match validated evidence")
    target = _subject(rebuilt["target_subject"], task_id=str(rebuilt["task_id"]), label="target")
    return rebuilt, target, _path(receipt_path, rebuilt["artifacts"]["result"], "result"), _path(receipt_path, rebuilt["artifacts"]["input"], "input")
