"""Fail-closed evidence for non-semantic Lean bundle boundary changes.

This channel is intentionally narrower than a semantic review.  It can carry
an already-applied p9/10/11+r9 PASS across path, import-module, namespace-doc,
or whole-file reassembly changes only when the Lean payload and public
declaration signatures are byte-token invariant after an explicit module
rewrite map.  It never upgrades the source rubric and never writes state.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import uuid
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.block_id_naming import canonicalize_block_id, is_canonical_block_id

from .state_review_apply_recovery import (
    RECOVERY_SCHEMA,
    validate_historical_review_apply_recovery,
)
from .state_exact_build_batch import (
    ExactBuildBatchError,
    catalog_owned_build_modules,
    validate_current_exact_build_receipt,
)
from .state_reconcile import ReconciliationError, discover_catalog_git_subjects
from .state_store import (
    SubjectBundle,
    canonical_subject_bytes,
    filesystem_path,
    git_blob_sha,
    sha256_file,
    sha256_json,
)
from .task_catalog import (
    CatalogError,
    load_catalog,
    validate_catalog_compatible_mat_commit,
)


BOUNDARY_DELTA_SCHEMA = "toy-apollo.validated-boundary-delta-receipt.v1"
BOUNDARY_INPUT_MANIFEST_SCHEMA = "toy-apollo.boundary-delta-input-manifest.v1"
BATCH_AUTHORITY_MANIFEST_SCHEMA = "mat.catalog.boundary97-policy-preflight-manifest.v1"
POLICY_SCHEMA = "toy-apollo.boundary-delta-policy.v1"
AUTHOR_DECISION_SCHEMA = "toy-apollo.boundary-delta-author-decision.v1"
TRANSFORMATION_KIND = "verified_boundary_delta"
_HEX40 = re.compile(r"[0-9a-f]{40}")
_HEX64 = re.compile(r"[0-9a-f]{64}")
_DECLARATION = re.compile(
    r"(?m)^\s*(?:(?:protected|private|noncomputable|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
_FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*(?:private\s+)?axiom\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
}


class BoundaryDeltaReceiptError(ValueError):
    pass


def _read(path: Path) -> Mapping[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise BoundaryDeltaReceiptError(f"cannot read JSON evidence {path}: {exc}") from exc
    if not isinstance(payload, Mapping):
        raise BoundaryDeltaReceiptError(f"JSON evidence is not an object: {path}")
    return payload


def _read_sha256_bound_json(
    path: Path, expected_sha256: str, *, label: str,
    capture: list[bytes] | None = None,
) -> Mapping[str, Any]:
    """Hash and parse one immutable byte snapshot, avoiding check/read races."""

    try:
        data = path.read_bytes()
        if not _HEX64.fullmatch(expected_sha256) or hashlib.sha256(data).hexdigest() != expected_sha256:
            raise BoundaryDeltaReceiptError(f"{label} hash mismatch")
        payload = json.loads(data.decode("utf-8"))
    except BoundaryDeltaReceiptError:
        raise
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BoundaryDeltaReceiptError(f"cannot read bound JSON evidence {path}: {exc}") from exc
    if not isinstance(payload, Mapping):
        raise BoundaryDeltaReceiptError(f"bound JSON evidence is not an object: {path}")
    if capture is not None:
        capture.append(data)
    return payload


def _ref(path: Path) -> dict[str, str]:
    return {"path": str(path.resolve()), "sha256": sha256_file(path)}


def _atomic_publish_no_replace(path: Path, payload: bytes, *, label: str) -> dict[str, Any]:
    """Durably stage bytes and atomically publish without replacing a peer."""

    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{uuid.uuid4().hex}.tmp")
    io_path = filesystem_path(path)
    io_temporary = filesystem_path(temporary)
    published = False
    cleanup_complete = True
    try:
        with io_temporary.open("xb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        # Same-directory hard links are atomic no-replace publication on
        # Windows and POSIX; rename/replace primitives may overwrite on POSIX.
        os.link(io_temporary, io_path)
        published = True
    except FileExistsError as exc:
        raise BoundaryDeltaReceiptError(f"{label}: immutable output appeared during publish") from exc
    except OSError as exc:
        raise BoundaryDeltaReceiptError(f"{label}: atomic publication failed: {exc}") from exc
    finally:
        for _attempt in range(3):
            try:
                io_temporary.unlink()
                break
            except FileNotFoundError:
                break
            except OSError:
                cleanup_complete = False
        cleanup_complete = not io_temporary.exists()
    if not io_path.is_file() or io_path.read_bytes() != payload:
        raise BoundaryDeltaReceiptError(
            f"{label}: output was published but final byte revalidation failed"
        )
    return {
        "path": str(path), "published": True,
        "temporary_cleanup": "complete" if cleanup_complete else "deferred",
        "final_sha256": hashlib.sha256(payload).hexdigest(),
    }


def _ensure_content_addressed_json_snapshot(
    root: Path, *, kind: str, expected_sha256: str, payload: bytes,
) -> tuple[dict[str, str], dict[str, Any]]:
    if not _HEX64.fullmatch(expected_sha256) or hashlib.sha256(payload).hexdigest() != expected_sha256:
        raise BoundaryDeltaReceiptError(f"{kind} snapshot source bytes/hash mismatch")
    try:
        decoded = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BoundaryDeltaReceiptError(f"{kind} snapshot source is not valid JSON") from exc
    if not isinstance(decoded, Mapping):
        raise BoundaryDeltaReceiptError(f"{kind} snapshot source is not a JSON object")
    path = (root.resolve() / kind / f"{expected_sha256}.json").resolve()
    if path.is_file():
        if path.read_bytes() != payload:
            raise BoundaryDeltaReceiptError(f"{kind} content-addressed snapshot collision mismatch")
        return {"path": str(path), "sha256": expected_sha256}, {
            "path": str(path), "published": False, "temporary_cleanup": "not_needed",
            "final_sha256": expected_sha256,
        }
    try:
        publication = _atomic_publish_no_replace(
            path, payload, label=f"{kind} content-addressed snapshot",
        )
    except BoundaryDeltaReceiptError:
        if not path.is_file() or path.read_bytes() != payload:
            raise
        publication = {
            "path": str(path), "published": False,
            "temporary_cleanup": "peer_published_exact", "final_sha256": expected_sha256,
        }
    if path.read_bytes() != payload:
        raise BoundaryDeltaReceiptError(f"{kind} snapshot final bytes mismatch")
    return {"path": str(path), "sha256": expected_sha256}, publication


def _run(repo: Path, *args: str) -> bytes:
    try:
        result = subprocess.run(
            list(args), cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False, timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise BoundaryDeltaReceiptError(f"cannot run {' '.join(args)} in {repo}: {exc}") from exc
    if result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise BoundaryDeltaReceiptError(f"command failed in {repo}: {' '.join(args)}: {detail}")
    return result.stdout


def _git_common_dir(repo: Path, *, label: str) -> Path:
    repo = repo.expanduser().resolve()
    raw = _run(repo, "git", "rev-parse", "--git-common-dir").decode("utf-8").strip()
    path = Path(raw)
    return (path if path.is_absolute() else repo / path).resolve()


def _receipt_match_payload(raw: Mapping[str, Any]) -> dict[str, Any]:
    """Canonicalize location-only Git worktree provenance for replay matching.

    A receipt may be emitted from a clean detached worktree and later replayed
    by the state importer through the repository's main worktree.  Those paths
    name the same immutable Git object database, commit, and blobs.  Preserve
    every recorded path in the receipt itself, but compare Git-backed content
    provenance by the shared ``--git-common-dir`` identity so a sibling
    worktree does not create a false evidence mismatch.
    """

    normalized = json.loads(json.dumps(raw, ensure_ascii=False))
    content = normalized.get("content_provenance")
    if not isinstance(content, Mapping):
        raise BoundaryDeltaReceiptError("boundary-delta content provenance is missing")
    for side in ("source", "target"):
        entries = content.get(side)
        if not isinstance(entries, list) or any(not isinstance(item, Mapping) for item in entries):
            raise BoundaryDeltaReceiptError(f"boundary-delta {side} content provenance is malformed")
        for index, item in enumerate(entries):
            repository = item.get("repository")
            if repository is None:
                continue
            if item.get("kind") not in {"git_commit_path", "git_blob"}:
                raise BoundaryDeltaReceiptError(
                    f"boundary-delta {side} content provenance {index} has unexpected repository"
                )
            item["repository"] = str(
                _git_common_dir(
                    Path(str(repository)),
                    label=f"boundary-delta {side} content provenance {index}",
                )
            )
    return normalized


def _subject(raw: Any, *, task_id: str, label: str) -> SubjectBundle:
    if not isinstance(raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: {label} subject is missing")
    try:
        subject = SubjectBundle.from_manifest(
            task_id=task_id,
            files=raw.get("files", raw.get("subject_files", [])),
            primary_path=str(raw.get("primary_path", "") or ""),
            source_repo=str(raw.get("source_repo", "") or ""),
            source_commit=str(raw.get("source_commit", raw.get("commit", "")) or ""),
            layout=str(raw.get("layout", "") or ""),
            subject_kind=str(raw.get("subject_kind", "workspace_review_binding") or "workspace_review_binding"),
        )
    except (TypeError, ValueError) as exc:
        raise BoundaryDeltaReceiptError(f"{task_id}: invalid {label} subject: {exc}") from exc
    for key, actual in (("subject_id", subject.subject_id), ("bundle_hash", subject.bundle_hash), ("primary_hash", subject.primary_hash)):
        declared = str(raw.get(key, "") or "")
        if declared and declared != actual:
            raise BoundaryDeltaReceiptError(f"{task_id}: {label} {key} mismatch")
    return subject


def _subject_payload(subject: SubjectBundle) -> dict[str, Any]:
    return {
        "task_id": subject.task_id, "subject_id": subject.subject_id,
        "subject_kind": subject.subject_kind, "source_repo": subject.source_repo,
        "source_commit": subject.source_commit, "layout": subject.layout,
        "bundle_hash": subject.bundle_hash, "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path, "files": subject.manifest(),
    }


def _git_blob(repo: Path, sha: str, *, label: str) -> bytes:
    if not _HEX40.fullmatch(sha):
        raise BoundaryDeltaReceiptError(f"{label}: missing full git blob identity")
    data = _run(repo, "git", "cat-file", "blob", sha)
    actual = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
    if actual != sha:
        raise BoundaryDeltaReceiptError(f"{label}: git blob identity mismatch")
    return data


def _bundle_content(
    roots: Sequence[Path], subject: SubjectBundle, *, label: str,
) -> tuple[dict[str, str], list[dict[str, Any]]]:
    resolved_roots = list(dict.fromkeys(path.resolve() for path in roots))
    result: dict[str, str] = {}; provenance: list[dict[str, Any]] = []
    for item in subject.files:
        candidates: list[tuple[bytes, dict[str, Any]]] = []
        for root in resolved_roots:
            if (root / ".git").exists():
                if _HEX40.fullmatch(subject.source_commit):
                    try:
                        data = _run(root, "git", "show", f"{subject.source_commit}:{item.path}")
                        raw_blob = _run(root, "git", "rev-parse", f"{subject.source_commit}:{item.path}").decode().strip()
                        candidates.append((data, {"kind": "git_commit_path", "repository": str(root), "commit": subject.source_commit, "path": item.path, "raw_git_blob_sha": raw_blob}))
                    except BoundaryDeltaReceiptError:
                        pass
                if _HEX40.fullmatch(item.git_blob_sha):
                    try:
                        data = _git_blob(root, item.git_blob_sha, label=f"{label} {item.path}")
                        candidates.append((data, {"kind": "git_blob", "repository": str(root), "path": item.path, "raw_git_blob_sha": item.git_blob_sha}))
                    except BoundaryDeltaReceiptError:
                        pass
            file_path = Path(item.path)
            file_path = file_path if file_path.is_absolute() else root / file_path
            if file_path.is_file():
                data = file_path.read_bytes()
                candidates.append((data, {"kind": "artifact_file", "path": str(file_path.resolve()), "raw_sha256": hashlib.sha256(data).hexdigest()}))
        selected: tuple[bytes, dict[str, Any]] | None = None
        for raw_data, raw_provenance in candidates:
            canonical = canonical_subject_bytes(item.path, raw_data)
            if (
                len(canonical) == item.size
                and hashlib.sha256(canonical).hexdigest() == item.content_sha256
                and git_blob_sha(canonical) == item.git_blob_sha
            ):
                selected = (canonical, raw_provenance); break
        if selected is None:
            raise BoundaryDeltaReceiptError(f"{label} {item.path}: no repository/artifact candidate exactly reconstructs the canonical manifest")
        data, raw_provenance = selected
        try:
            result[item.path] = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise BoundaryDeltaReceiptError(f"{label} {item.path}: Lean source is not UTF-8") from exc
        provenance.append({**raw_provenance, "canonical_content_sha256": item.content_sha256, "canonical_git_blob_sha": item.git_blob_sha, "canonical_size": item.size})
    return result, provenance


def _workspace_review_binding_scope(
    payload: Mapping[str, Any], *, task_id: str, authority: Mapping[str, Any]
) -> SubjectBundle:
    if payload.get("schema_version") != "toy-apollo.workspace-review-binding.v1":
        raise BoundaryDeltaReceiptError("unsupported workspace review-binding scope schema")
    tasks = payload.get("tasks")
    if not isinstance(tasks, list):
        raise BoundaryDeltaReceiptError("source scope evidence lacks task bindings")
    entries = [entry for entry in tasks if isinstance(entry, Mapping) and canonicalize_block_id(str(entry.get("task_id", "") or "")) == task_id]
    if len(entries) != 1:
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope evidence must contain exactly one binding")
    entry = entries[0]
    if entry.get("binding_kind") != "legacy_primary_scope_rebind":
        raise BoundaryDeltaReceiptError(f"{task_id}: unsupported source scope binding kind")
    checks = entry.get("checks")
    required = ("build_status", "forbidden_scan_status", "support_scope_status", "mat_relocation_status")
    if not isinstance(checks, Mapping) or any(checks.get(key) != "pass" for key in required):
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope binding checks are not all PASS")
    basis = entry.get("basis_review")
    artifacts = authority.get("artifacts")
    if not isinstance(basis, Mapping) or not isinstance(artifacts, Mapping) or not isinstance(artifacts.get("result"), Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: source authority/scope result binding is missing")
    result_hash = str(artifacts["result"].get("sha256", "") or "")
    if str(basis.get("evidence_hash", "") or "") != result_hash:
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope is not bound to the authority result")
    subjects = entry.get("subjects")
    if not isinstance(subjects, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope lacks complete subjects")
    source_rows = [row for row in subjects if isinstance(row, Mapping) and row.get("role") == "toy_current"]
    if len(source_rows) != 1:
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope must identify one complete toy_current bundle")
    source = _subject(source_rows[0], task_id=task_id, label="source scope")
    if source.primary_hash != str(basis.get("primary_hash", "") or ""):
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope primary is not the reviewed primary")
    return source


def _recovery_subject_exact_scope(
    payload: Mapping[str, Any], *, task_id: str, authority: Mapping[str, Any]
) -> SubjectBundle:
    """Use an explicit complete review-input bundle from the same recovery.

    This is not a primary-only compatibility fallback.  Legacy/synthetic
    subjects and manifests without content-addressed Git blobs are rejected.
    """
    if payload.get("schema") != RECOVERY_SCHEMA or sha256_json(payload) != sha256_json(authority):
        raise BoundaryDeltaReceiptError(
            f"{task_id}: recovery exact scope must be the same validated authority receipt"
        )
    raw = payload.get("source_subject")
    if not isinstance(raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: recovery exact scope lacks source_subject")
    if str(raw.get("subject_kind", "") or "") != "review_input_bundle":
        raise BoundaryDeltaReceiptError(
            f"{task_id}: recovery exact scope requires a non-legacy review_input_bundle"
        )
    files = raw.get("files")
    if not isinstance(files, list) or not files:
        raise BoundaryDeltaReceiptError(f"{task_id}: recovery exact scope lacks explicit files")
    for item in files:
        if (
            not isinstance(item, Mapping)
            or not str(item.get("path", "") or "")
            or not _HEX64.fullmatch(str(item.get("content_sha256", "") or ""))
            or not _HEX40.fullmatch(str(item.get("git_blob_sha", "") or ""))
            or int(item.get("size", 0) or 0) <= 0
        ):
            raise BoundaryDeltaReceiptError(
                f"{task_id}: recovery exact scope file manifest is not fully content-addressed"
            )
    return _subject(raw, task_id=task_id, label="recovery exact source scope")


def _source_scope(path: Path, *, task_id: str, authority: Mapping[str, Any]) -> SubjectBundle:
    """Dispatch only to explicitly registered, full-bundle scope validators.

    New historical layouts must add a validator here.  Unknown schemas never
    fall back to guessing a subject from similarly named fields.
    """
    payload = _read(path)
    schema = str(payload.get("schema_version", payload.get("schema", "")) or "")
    validators = {
        "toy-apollo.workspace-review-binding.v1": _workspace_review_binding_scope,
        RECOVERY_SCHEMA: _recovery_subject_exact_scope,
    }
    validator = validators.get(schema)
    if validator is None:
        raise BoundaryDeltaReceiptError(
            f"{task_id}: unsupported full-bundle source-scope schema {schema!r}"
        )
    return validator(payload, task_id=task_id, authority=authority)


def _legacy_embedded_single_file_scope(
    path: Path, payload: Mapping[str, Any], *, task_id: str,
    authority: Mapping[str, Any], reviewed_subject: SubjectBundle,
) -> tuple[SubjectBundle, dict[str, str], list[dict[str, Any]]]:
    if payload.get("schema") != RECOVERY_SCHEMA or sha256_json(payload) != sha256_json(authority):
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded scope must be the same validated recovery")
    if reviewed_subject.subject_kind != "legacy_bound" or len(reviewed_subject.files) != 1:
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded scope requires exactly one legacy source file")
    artifacts = payload.get("artifacts")
    if not isinstance(artifacts, Mapping) or not isinstance(artifacts.get("input"), Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded scope lacks input evidence")
    input_ref = artifacts["input"]
    input_path = path.parent / str(input_ref.get("path", "") or "")
    if not input_path.is_file() or sha256_file(input_path) != str(input_ref.get("sha256", "") or ""):
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded input artifact mismatch")
    review_input = _read(input_path); candidate = review_input.get("candidate")
    if not isinstance(candidate, Mapping) or not isinstance(candidate.get("lean"), str):
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded candidate Lean is missing")
    lean = str(candidate["lean"]); digest = hashlib.sha256(lean.encode("utf-8")).hexdigest()
    hashes = {
        digest,
        str(candidate.get("hash", "") or ""),
        str(review_input.get("review_subject_hash", "") or ""),
        reviewed_subject.primary_hash,
    }
    if len(hashes) != 1 or not _HEX64.fullmatch(digest):
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded candidate four-way hash mismatch")
    return reviewed_subject, {reviewed_subject.primary_path: lean}, [{
        "kind": "validated_recovery_embedded_candidate", "path": str(input_path.resolve()),
        "artifact_sha256": sha256_file(input_path), "canonical_content_sha256": digest,
    }]


def _target_build(path: Path, *, task_id: str) -> tuple[Mapping[str, Any], SubjectBundle]:
    payload = _read(path)
    if payload.get("schema") != "mat.catalog.exact-build.v1" or payload.get("success") is not True or payload.get("exit_code") != 0:
        raise BoundaryDeltaReceiptError(f"{task_id}: target is not a successful exact-MAT build")
    if canonicalize_block_id(str(payload.get("task_id", "") or "")) != task_id:
        raise BoundaryDeltaReceiptError(f"{task_id}: target build task mismatch")
    commit = str(payload.get("commit", "") or "")
    if not _HEX40.fullmatch(commit):
        raise BoundaryDeltaReceiptError(f"{task_id}: target build lacks a pinned commit")
    scan = payload.get("forbidden_token_scan")
    if not isinstance(scan, Mapping) or scan.get("exit_code") != 0 or scan.get("findings") not in ({}, []):
        raise BoundaryDeltaReceiptError(f"{task_id}: target forbidden scan is not clean")
    tree = payload.get("lean_tree_equivalence")
    if not isinstance(tree, Mapping) or tree.get("target_commit") != commit or tree.get("build_checkout_clean") is not True or tree.get("changed_lean_files") != []:
        raise BoundaryDeltaReceiptError(f"{task_id}: target build is not clean-tree equivalent")
    subject = _subject({
        "subject_id": payload.get("subject_id"), "bundle_hash": payload.get("bundle_hash"),
        "primary_hash": payload.get("primary_hash"), "primary_path": payload.get("primary_path"),
        "files": payload.get("subject_files"), "source_repo": "mat", "source_commit": commit,
        "layout": "mat", "subject_kind": "catalog_git_bundle",
    }, task_id=task_id, label="target build")
    return payload, subject


def _strip_comments(text: str) -> str:
    """Remove nested Lean comments while preserving strings and newlines."""
    out: list[str] = []
    index = 0
    depth = 0
    quoted = False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1; out.extend("  "); index += 2; continue
            if pair == "-/":
                depth -= 1; out.extend("  "); index += 2; continue
            out.append("\n" if char == "\n" else " "); index += 1; continue
        if not quoted and pair == "/-":
            depth = 1; out.extend("  "); index += 2; continue
        if not quoted and pair == "--":
            end = text.find("\n", index)
            if end < 0:
                out.extend(" " * (len(text) - index)); break
            out.extend(" " * (end - index)); index = end; continue
        out.append(char)
        if char == '"' and (index == 0 or text[index - 1] != "\\"):
            quoted = not quoted
        index += 1
    if depth or quoted:
        raise BoundaryDeltaReceiptError("unterminated Lean comment or string")
    return "".join(out)


def _imports_and_payload(text: str) -> tuple[list[str], str]:
    clean = _strip_comments(text)
    imports: list[str] = []
    payload_lines: list[str] = []
    for line in clean.splitlines():
        match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_'.]+)\s*", line)
        if match:
            imports.append(match.group(1))
        else:
            payload_lines.append(line)
    return imports, "\n".join(payload_lines)


def _open_namespaces_and_payload(text: str) -> tuple[list[str], str]:
    opened: list[str] = []
    payload: list[str] = []
    for line in text.splitlines():
        match = re.fullmatch(r"\s*open\s+(.+?)\s*", line)
        if match and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", item) for item in match.group(1).split()):
            opened.extend(match.group(1).split())
        else:
            payload.append(line)
    return opened, "\n".join(payload)


def _section_commands_and_payload(text: str) -> tuple[list[str], str]:
    commands: list[str] = []
    payload: list[str] = []
    for line in text.splitlines():
        match = re.fullmatch(r"\s*(section\s+[A-Za-z_][A-Za-z0-9_']*|end\s+[A-Za-z_][A-Za-z0-9_']*)\s*", line)
        if match:
            commands.append(match.group(1))
        else:
            payload.append(line)
    return commands, "\n".join(payload)


def _normalize_tokens(text: str, rewrites: Mapping[str, str]) -> list[str]:
    # Longest first prevents an allowed parent module from partially rewriting
    # a more specific module token.
    for source in sorted(rewrites, key=len, reverse=True):
        text = re.sub(rf"(?<![A-Za-z0-9_']){re.escape(source)}(?![A-Za-z0-9_'])", rewrites[source], text)
    return re.findall(r"[A-Za-z_][A-Za-z0-9_']*|\d+|:=|=>|->|<-|≤|≥|≠|[^\s]", text)


def _declaration_signatures(text: str, rewrites: Mapping[str, str]) -> list[dict[str, str]]:
    clean = _strip_comments(text)
    found = list(_DECLARATION.finditer(clean))
    result: list[dict[str, str]] = []
    for index, match in enumerate(found):
        fragment = clean[match.start():(found[index + 1].start() if index + 1 < len(found) else len(clean))]
        # A public contract is the declaration prefix.  If no explicit body
        # delimiter is found, retaining the whole fragment is the conservative
        # fail-closed choice.
        boundary = re.search(r"(?m)(?<!:)\s(:=|\bwhere\b|\bby\b)", fragment)
        header = fragment[:boundary.start()] if boundary else fragment
        tokens = _normalize_tokens(header, rewrites)
        result.append({
            "kind": match.group(1), "name": match.group(2),
            "signature_sha256": sha256_json(tokens),
        })
    return result


def _rewrite_map(policy: Mapping[str, Any], *, task_id: str, commit: str) -> dict[str, str]:
    if policy.get("schema") != POLICY_SCHEMA or canonicalize_block_id(str(policy.get("task_id", "") or "")) != task_id:
        raise BoundaryDeltaReceiptError(f"{task_id}: unsupported boundary-delta policy")
    if str(policy.get("target_commit", "") or "") != commit:
        raise BoundaryDeltaReceiptError(f"{task_id}: policy target commit mismatch")
    rewrites: dict[str, str] = {}
    raw = policy.get("module_rewrites", [])
    if not isinstance(raw, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: module rewrites are malformed")
    for item in raw:
        if not isinstance(item, Mapping):
            raise BoundaryDeltaReceiptError(f"{task_id}: module rewrite is malformed")
        source, target = str(item.get("source", "") or ""), str(item.get("target", "") or "")
        if not source or not target or source == target or source in rewrites:
            raise BoundaryDeltaReceiptError(f"{task_id}: invalid or duplicate module rewrite")
        rewrites[source] = target
    return rewrites


def _compare_files(
    source_files: Mapping[str, str], target_files: Mapping[str, str],
    policy: Mapping[str, Any], rewrites: Mapping[str, str], *, task_id: str,
) -> tuple[list[dict[str, Any]], list[str], list[str], list[dict[str, str]]]:
    pairs = policy.get("file_pairs")
    if not isinstance(pairs, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: file_pairs are required")
    source_seen: set[str] = set(); target_seen: set[str] = set(); rows: list[dict[str, Any]] = []
    raw_context = policy.get("open_namespace_changes", [])
    if not isinstance(raw_context, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: open_namespace_changes is malformed")
    context_changes = {
        (str(item.get("source_path", "")), str(item.get("target_path", ""))): item
        for item in raw_context if isinstance(item, Mapping)
    }
    if len(context_changes) != len(raw_context):
        raise BoundaryDeltaReceiptError(f"{task_id}: duplicate or malformed open namespace change")
    raw_import_changes = policy.get("import_changes", [])
    if not isinstance(raw_import_changes, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: import_changes is malformed")
    import_changes = {
        (str(item.get("source_path", "")), str(item.get("target_path", ""))): item
        for item in raw_import_changes if isinstance(item, Mapping)
    }
    if len(import_changes) != len(raw_import_changes):
        raise BoundaryDeltaReceiptError(f"{task_id}: duplicate or malformed import change")
    raw_section_changes = policy.get("section_changes", [])
    if not isinstance(raw_section_changes, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: section_changes is malformed")
    section_changes = {
        (str(item.get("source_path", "")), str(item.get("target_path", ""))): item
        for item in raw_section_changes if isinstance(item, Mapping)
    }
    if len(section_changes) != len(raw_section_changes):
        raise BoundaryDeltaReceiptError(f"{task_id}: duplicate or malformed section change")
    source_imports: list[str] = []; target_imports: list[str] = []
    source_decls: list[dict[str, str]] = []; target_decls: list[dict[str, str]] = []
    for raw in pairs:
        if not isinstance(raw, Mapping):
            raise BoundaryDeltaReceiptError(f"{task_id}: malformed file pair")
        source_path, target_path = str(raw.get("source", "") or ""), str(raw.get("target", "") or "")
        if source_path not in source_files or target_path not in target_files or source_path in source_seen or target_path in target_seen:
            raise BoundaryDeltaReceiptError(f"{task_id}: file pair does not bijectively cover the bundles")
        source_seen.add(source_path); target_seen.add(target_path)
        s_imports, s_payload = _imports_and_payload(source_files[source_path])
        t_imports, t_payload = _imports_and_payload(target_files[target_path])
        s_open, s_payload = _open_namespaces_and_payload(s_payload)
        t_open, t_payload = _open_namespaces_and_payload(t_payload)
        s_sections, s_payload = _section_commands_and_payload(s_payload)
        t_sections, t_payload = _section_commands_and_payload(t_payload)
        declared_context = context_changes.pop((source_path, target_path), None)
        if s_open != t_open:
            if (
                not isinstance(declared_context, Mapping)
                or declared_context.get("source_open") != s_open
                or declared_context.get("target_open") != t_open
            ):
                raise BoundaryDeltaReceiptError(f"{task_id}: undeclared open namespace context delta in {source_path} -> {target_path}")
        elif declared_context is not None:
            raise BoundaryDeltaReceiptError(f"{task_id}: redundant open namespace change declaration")
        declared_sections = section_changes.pop((source_path, target_path), None)
        if s_sections != t_sections:
            if (
                not isinstance(declared_sections, Mapping)
                or declared_sections.get("source_sections") != s_sections
                or declared_sections.get("target_sections") != t_sections
            ):
                raise BoundaryDeltaReceiptError(f"{task_id}: undeclared section reassembly in {source_path} -> {target_path}")
        elif declared_sections is not None:
            raise BoundaryDeltaReceiptError(f"{task_id}: redundant section change declaration")
        s_tokens = _normalize_tokens(s_payload, rewrites)
        t_tokens = _normalize_tokens(t_payload, {})
        if s_tokens != t_tokens:
            raise BoundaryDeltaReceiptError(f"{task_id}: Lean payload delta in {source_path} -> {target_path}")
        normalized_source_imports = [rewrites.get(item, item) for item in s_imports]
        declared_imports = import_changes.pop((source_path, target_path), None)
        if normalized_source_imports != t_imports:
            if (
                not isinstance(declared_imports, Mapping)
                or declared_imports.get("source_imports") != s_imports
                or declared_imports.get("normalized_source_imports") != normalized_source_imports
                or declared_imports.get("target_imports") != t_imports
            ):
                raise BoundaryDeltaReceiptError(f"{task_id}: undeclared dependency/import delta in {source_path} -> {target_path}")
        elif declared_imports is not None:
            raise BoundaryDeltaReceiptError(f"{task_id}: redundant import change declaration")
        s_decl = _declaration_signatures(s_payload, rewrites)
        t_decl = _declaration_signatures(t_payload, {})
        if s_decl != t_decl:
            raise BoundaryDeltaReceiptError(f"{task_id}: public declaration contract delta in {source_path} -> {target_path}")
        source_imports.extend(normalized_source_imports); target_imports.extend(t_imports)
        source_decls.extend(s_decl); target_decls.extend(t_decl)
        if source_files[source_path].encode() == target_files[target_path].encode():
            classification = "path_relocation" if source_path != target_path else "byte_exact"
        elif s_imports != t_imports:
            classification = "import_namespace_docs"
        elif source_path != target_path:
            classification = "whole_file_reassembly"
        else:
            classification = "documentation_or_whitespace"
        rows.append({
            "source_path": source_path, "target_path": target_path,
            "classification": classification,
            "source_sha256": hashlib.sha256(source_files[source_path].encode()).hexdigest(),
            "target_sha256": hashlib.sha256(target_files[target_path].encode()).hexdigest(),
            "normalized_payload_sha256": sha256_json(s_tokens),
            "public_declaration_count": len(s_decl),
        })
    if source_seen != set(source_files) or target_seen != set(target_files):
        raise BoundaryDeltaReceiptError(f"{task_id}: file pairs do not cover the complete source and target bundles")
    if source_decls != target_decls:
        raise BoundaryDeltaReceiptError(f"{task_id}: bundle public declaration manifest differs")
    if context_changes:
        raise BoundaryDeltaReceiptError(f"{task_id}: open namespace policy names unknown file pairs")
    if import_changes:
        raise BoundaryDeltaReceiptError(f"{task_id}: import policy names unknown file pairs")
    if section_changes:
        raise BoundaryDeltaReceiptError(f"{task_id}: section policy names unknown file pairs")
    return rows, source_imports, target_imports, source_decls


def _consumer_evidence(
    manifest_path: Path, build_paths: Sequence[Path], *, task_id: str,
    target: SubjectBundle, target_repo: Path,
    exact_context: Mapping[str, Any] | None = None,
) -> list[dict[str, str]]:
    manifest = _read(manifest_path)
    expected = {"task_id": task_id, "commit": target.source_commit, "subject_id": target.subject_id, "bundle_hash": target.bundle_hash}
    if manifest.get("schema") != "mat.catalog.direct-consumer-manifest.v1" or any(str(manifest.get(key, "") or "") != value for key, value in expected.items()):
        raise BoundaryDeltaReceiptError(f"{task_id}: direct-consumer manifest target mismatch")
    consumers = manifest.get("consumers")
    if not isinstance(consumers, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: direct-consumer manifest is malformed")
    expected_ids: set[str] = set()
    expected_paths: dict[str, set[str]] = {}
    for entry in consumers:
        consumer = canonicalize_block_id(str(entry.get("task_id", "") or "")) if isinstance(entry, Mapping) else ""
        if not consumer or not is_canonical_block_id(consumer) or consumer in expected_ids:
            raise BoundaryDeltaReceiptError(f"{task_id}: malformed or duplicate direct consumer")
        raw_paths = entry.get("paths") if isinstance(entry, Mapping) else None
        if (
            not isinstance(raw_paths, list) or not raw_paths
            or any(not isinstance(path, str) or not path.strip() for path in raw_paths)
        ):
            raise BoundaryDeltaReceiptError(f"{task_id}: direct consumer {consumer} lacks explicit paths")
        expected_ids.add(consumer)
        expected_paths[consumer] = {path.replace("\\", "/") for path in raw_paths}
    current_subjects: Mapping[str, SubjectBundle] = {}
    primary_modules: Mapping[str, str] = {}
    owned_modules: Mapping[str, tuple[str, ...]] = {}
    if expected_ids and exact_context is not None:
        raw_subjects = exact_context.get("subjects")
        raw_primary = exact_context.get("primary_modules")
        raw_owned = exact_context.get("owned_modules")
        if not isinstance(raw_subjects, Mapping) or not isinstance(raw_primary, Mapping) or not isinstance(raw_owned, Mapping):
            raise BoundaryDeltaReceiptError(f"{task_id}: exact-build catalog context is malformed")
        current_subjects = raw_subjects
        primary_modules = raw_primary
        owned_modules = raw_owned
        if str(exact_context.get("commit", "") or "") != target.source_commit:
            raise BoundaryDeltaReceiptError(f"{task_id}: exact-build catalog context commit mismatch")
    elif expected_ids:
        runtime_root = Path(__file__).resolve().parents[2]
        try:
            catalog = load_catalog(
                workspace_root=runtime_root.parent, runtime_root=runtime_root,
                mat_root=target_repo.resolve(),
            )
            validate_catalog_compatible_mat_commit(
                catalog, mat_root=target_repo.resolve(), commit=target.source_commit,
            )
            current_subjects = discover_catalog_git_subjects(
                target_repo.resolve(), ref=target.source_commit, catalog=catalog,
                source_repo="mat", layout="mat", task_ids=expected_ids,
            )
            primary_modules, owned_modules = catalog_owned_build_modules(catalog, expected_ids)
        except (CatalogError, ReconciliationError, ExactBuildBatchError) as exc:
            raise BoundaryDeltaReceiptError(f"{task_id}: cannot reconstruct current consumer subjects: {exc}") from exc
        if set(current_subjects) != expected_ids:
            raise BoundaryDeltaReceiptError(f"{task_id}: current catalog does not cover every direct consumer")
    actual: dict[str, dict[str, str]] = {}
    for path in build_paths:
        payload = _read(path)
        consumer = canonicalize_block_id(str(payload.get("task_id", "") or ""))
        if not consumer or consumer in actual:
            raise BoundaryDeltaReceiptError(f"{task_id}: duplicate or invalid consumer build")
        subject = current_subjects.get(consumer)
        if subject is None:
            raise BoundaryDeltaReceiptError(f"{task_id}: build supplied for a non-consumer {consumer}")
        if not expected_paths[consumer].issubset({item.path for item in subject.files}):
            raise BoundaryDeltaReceiptError(f"{task_id}: direct-consumer paths are outside {consumer}'s current bundle")
        focused = payload.get("focused_build")
        cwd = Path(str(focused.get("cwd", "") or "")) if isinstance(focused, Mapping) else Path("")
        try:
            validate_current_exact_build_receipt(
                path, subject=subject, primary_module=primary_modules[consumer],
                task_modules=owned_modules[consumer], commit=target.source_commit,
                checkout=cwd,
            )
        except (ExactBuildBatchError, KeyError) as exc:
            raise BoundaryDeltaReceiptError(f"{task_id}: consumer {consumer} exact-build validation failed: {exc}") from exc
        actual[consumer] = {"task_id": consumer, **_ref(path)}
    if set(actual) != expected_ids:
        raise BoundaryDeltaReceiptError(f"{task_id}: every and only direct consumer needs exact build evidence")
    return [actual[key] for key in sorted(actual)]


def _author_provenance(
    *, task_id: str, kenneth_repo: Path, kenneth_commit: str,
    author_decision_path: Path | None, target_files: Mapping[str, str],
) -> dict[str, Any]:
    if not _HEX40.fullmatch(kenneth_commit):
        raise BoundaryDeltaReceiptError(f"{task_id}: Kenneth provenance needs a pinned commit")
    _run(kenneth_repo, "git", "cat-file", "-e", f"{kenneth_commit}^{{commit}}")
    tree = _run(kenneth_repo, "git", "ls-tree", "-r", "--name-only", kenneth_commit).decode("utf-8").splitlines()
    needle = task_id.lower()
    target_basenames = {Path(path).name.lower() for path in target_files}
    matches = sorted(
        path for path in tree
        if path.lower().endswith(".lean")
        and (
            Path(path).stem.lower() == needle
            or (
                Path(path).stem.lower().startswith(needle + "_")
                and Path(path).name.lower() in target_basenames
            )
        )
    )
    kenneth_files: list[dict[str, Any]] = []
    kenneth_bytes: dict[str, bytes] = {}
    for path in matches:
        blob = _run(kenneth_repo, "git", "rev-parse", f"{kenneth_commit}:{path}").decode().strip()
        data = _git_blob(kenneth_repo, blob, label=f"Kenneth {path}")
        kenneth_bytes[path] = data
        kenneth_files.append({
            "path": path, "git_blob_sha": blob,
            "content_sha256": hashlib.sha256(data).hexdigest(), "size": len(data),
        })
    if not matches:
        if author_decision_path is not None:
            raise BoundaryDeltaReceiptError(f"{task_id}: author decision supplied although Kenneth has no matching artifact")
        return {"applicability": "not_applicable", "repository": "kenneth", "commit": kenneth_commit, "matched_files": [], "files": [], "decision": "not_applicable_no_task_artifact"}
    if author_decision_path is None:
        raise BoundaryDeltaReceiptError(f"{task_id}: Kenneth has matching files; explicit author decision is required")
    decision = _read(author_decision_path)
    allowed = {"author_exact", "mat_retained_reviewed", "explicit_author_decision"}
    if decision.get("schema") != AUTHOR_DECISION_SCHEMA or canonicalize_block_id(str(decision.get("task_id", "") or "")) != task_id or decision.get("commit") != kenneth_commit or decision.get("decision") not in allowed:
        raise BoundaryDeltaReceiptError(f"{task_id}: invalid Kenneth author decision")
    if sorted(decision.get("matched_files", [])) != matches:
        raise BoundaryDeltaReceiptError(f"{task_id}: Kenneth author decision file scope mismatch")
    decision_kind = str(decision.get("decision", "") or "")
    result: dict[str, Any] = {
        "applicability": "applicable", "repository": "kenneth",
        "commit": kenneth_commit, "matched_files": matches,
        "files": kenneth_files, "decision": decision_kind,
        "artifact": _ref(author_decision_path),
    }
    if decision_kind == "author_exact":
        raw_pairs = decision.get("target_pairs")
        if not isinstance(raw_pairs, list):
            raise BoundaryDeltaReceiptError(f"{task_id}: author_exact requires Kenneth→target file pairs")
        seen_kenneth: set[str] = set(); seen_target: set[str] = set(); pairs: list[dict[str, str]] = []
        for raw in raw_pairs:
            if not isinstance(raw, Mapping):
                raise BoundaryDeltaReceiptError(f"{task_id}: malformed author_exact file pair")
            source_path = str(raw.get("kenneth_path", "") or "")
            target_path = str(raw.get("target_path", "") or "")
            if source_path not in kenneth_bytes or target_path not in target_files or source_path in seen_kenneth or target_path in seen_target:
                raise BoundaryDeltaReceiptError(f"{task_id}: author_exact file pairs do not bind real source/target files")
            target_data = target_files[target_path].encode("utf-8")
            if kenneth_bytes[source_path] != target_data:
                raise BoundaryDeltaReceiptError(f"{task_id}: author_exact Kenneth/target bytes differ")
            seen_kenneth.add(source_path); seen_target.add(target_path)
            pairs.append({
                "kenneth_path": source_path, "target_path": target_path,
                "content_sha256": hashlib.sha256(target_data).hexdigest(),
                "kenneth_git_blob_sha": next(item["git_blob_sha"] for item in kenneth_files if item["path"] == source_path),
            })
        if seen_kenneth != set(matches):
            raise BoundaryDeltaReceiptError(f"{task_id}: author_exact must cover every matching Kenneth file")
        result["target_byte_bindings"] = pairs
        result["authority_evidence"] = []
        return result

    raw_evidence = decision.get("authority_evidence")
    if not isinstance(raw_evidence, list) or not raw_evidence:
        raise BoundaryDeltaReceiptError(
            f"{task_id}: {decision_kind} requires immutable historical/Gate2/chat authority evidence"
        )
    evidence_rows: list[dict[str, str]] = []
    for raw in raw_evidence:
        if not isinstance(raw, Mapping):
            raise BoundaryDeltaReceiptError(f"{task_id}: malformed author authority evidence")
        kind = str(raw.get("kind", "") or "")
        evidence_path = Path(str(raw.get("path", "") or "")).expanduser().resolve()
        expected_hash = str(raw.get("sha256", "") or "")
        normalized = evidence_path.as_posix().lower()
        kind_matches_path = (
            (kind == "gate2" and "/gate2/" in normalized)
            or (kind == "chat_history" and "chat history" in normalized)
            or (
                kind == "historical_review_apply"
                and evidence_path.name.lower().startswith(
                    ("semantic_review_result", "verify_result", "review_apply_receipt", "historical_review_apply_recovery_receipt")
                )
            )
        )
        if not kind_matches_path or not evidence_path.is_file() or not _HEX64.fullmatch(expected_hash) or sha256_file(evidence_path) != expected_hash:
            raise BoundaryDeltaReceiptError(f"{task_id}: author authority evidence is not a real immutable {kind!r} artifact")
        evidence_rows.append({"kind": kind, "path": str(evidence_path), "sha256": expected_hash})
    result["authority_evidence"] = evidence_rows
    return result


def _normalize_declared_kenneth_provenance(
    declared: Mapping[str, Any], *, actual: Mapping[str, Any], task_id: str,
    kenneth_commit: str, target_files: Mapping[str, str],
) -> dict[str, Any]:
    """Normalize only registered legacy absence summaries after a pinned tree scan."""

    actual_dict = dict(actual)
    if actual_dict.get("applicability") != "not_applicable":
        if dict(declared) != actual_dict:
            raise BoundaryDeltaReceiptError(
                f"{task_id}: declared Kenneth provenance differs from pinned tree evidence"
            )
        return actual_dict
    canonical = {
        "applicability": "not_applicable", "repository": "kenneth",
        "commit": kenneth_commit, "matched_files": [], "files": [],
        "decision": "not_applicable_no_task_artifact",
    }
    if actual_dict != canonical:
        raise BoundaryDeltaReceiptError(f"{task_id}: pinned Kenneth absence evidence is malformed")
    raw = dict(declared)
    source_action = raw.pop("source_action_evidence", None)
    if raw != canonical:
        raise BoundaryDeltaReceiptError(f"{task_id}: declared Kenneth absence is not canonical")
    if source_action is None:
        return canonical
    if not isinstance(source_action, Mapping) or source_action.get("commit") != kenneth_commit:
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy Kenneth absence summary is malformed")
    shape = set(source_action)
    if shape == {
        "commit", "kenneth_to_mat_primary_byte_exact",
        "kenneth_to_mat_task_declaration_tokens_exact", "primary", "task_declaration",
    }:
        if (
            source_action.get("kenneth_to_mat_primary_byte_exact") is not False
            or source_action.get("kenneth_to_mat_task_declaration_tokens_exact") is not False
            or source_action.get("primary") is not None
            or source_action.get("task_declaration") is not None
        ):
            raise BoundaryDeltaReceiptError(f"{task_id}: legacy Kenneth comparison is not an absence")
        return canonical
    if shape == {"commit", "mat_target_content_sha256", "path", "relationship_to_mat_target", "status"}:
        path = str(source_action.get("path", "") or "")
        target = target_files.get(path)
        if (
            target is None
            or source_action.get("mat_target_content_sha256") != hashlib.sha256(target.encode("utf-8")).hexdigest()
            or source_action.get("relationship_to_mat_target") != "no_same_path_blob_available"
            or source_action.get("status") != "absent_at_kenneth_commit"
        ):
            raise BoundaryDeltaReceiptError(f"{task_id}: legacy Kenneth path absence summary mismatches target")
        return canonical
    raise BoundaryDeltaReceiptError(f"{task_id}: unknown legacy Kenneth absence summary structure")


def build_verified_boundary_delta(
    *, source_authority_path: Path, source_scope_path: Path, source_repos: Sequence[Path],
    target_build_path: Path, target_repo: Path, policy_path: Path,
    consumer_manifest_path: Path, consumer_build_paths: Sequence[Path],
    kenneth_repo: Path, kenneth_commit: str,
    author_decision_path: Path | None = None, created_at: str | None = None,
    input_manifest_path: Path | None = None,
    exact_context: Mapping[str, Any] | None = None,
    orchestration_provenance: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    source_authority_path = source_authority_path.resolve()
    authority_payload = _read(source_authority_path)
    if authority_payload.get("schema") != RECOVERY_SCHEMA:
        raise BoundaryDeltaReceiptError("source authority must be a validated historical review-apply recovery")
    try:
        authority, reviewed_subject = validate_historical_review_apply_recovery(source_authority_path, authority_payload)
    except ValueError as exc:
        raise BoundaryDeltaReceiptError(f"source authority failed validation: {exc}") from exc
    task_id = canonicalize_block_id(str(authority.get("task_id", "") or ""))
    review = authority.get("source_review")
    if not isinstance(review, Mapping) or int(review.get("prompt_version", 0) or 0) not in {9, 10, 11} or int(review.get("rubric_version", 0) or 0) != 9 or review.get("verdict") != "pass" or review.get("phase2_status") != "pass":
        raise BoundaryDeltaReceiptError(f"{task_id}: source is not an applied p9/10/11+r9 PASS")
    source_scope_path = source_scope_path.resolve()
    source_scope_payload = _read(source_scope_path)
    if (
        source_scope_payload.get("schema") == RECOVERY_SCHEMA
        and reviewed_subject.subject_kind == "legacy_bound"
    ):
        source, source_files, source_content_provenance = _legacy_embedded_single_file_scope(
            source_scope_path, source_scope_payload, task_id=task_id,
            authority=authority, reviewed_subject=reviewed_subject,
        )
        legacy_embedded = True
    else:
        source = _source_scope(source_scope_path, task_id=task_id, authority=authority)
        source_files, source_content_provenance = _bundle_content(
            [source_scope_path.parent, *source_repos], source, label="source"
        )
        legacy_embedded = False
    if source.primary_hash != reviewed_subject.primary_hash:
        raise BoundaryDeltaReceiptError(f"{task_id}: full source bundle primary differs from reviewed authority")
    target_build_path = target_build_path.resolve()
    target_build, target = _target_build(target_build_path, task_id=task_id)
    if exact_context is not None:
        _strict_payload, strict_target = _validate_context_exact_build(
            target_build_path, task_id=task_id, context=exact_context,
        )
        if strict_target.subject_id != target.subject_id:
            raise BoundaryDeltaReceiptError(f"{task_id}: strict target subject mismatch")
    target_repo = target_repo.resolve()
    # The object database may later be checked out at another commit.  The
    # exact-build artifact proves the clean checkout; validation only needs the
    # pinned commit and blobs to remain available here.
    _run(target_repo, "git", "cat-file", "-e", f"{target.source_commit}^{{commit}}")
    target_files, target_content_provenance = _bundle_content([target_repo], target, label="target")
    if legacy_embedded and (len(source.files) != 1 or len(target.files) != 1):
        raise BoundaryDeltaReceiptError(f"{task_id}: legacy embedded scope is single-file only")
    for path, text in target_files.items():
        findings = [name for name, pattern in _FORBIDDEN.items() if pattern.search(_strip_comments(text))]
        if findings:
            raise BoundaryDeltaReceiptError(f"{task_id}: target {path} has forbidden tokens {findings}")
    policy_path = policy_path.resolve(); policy = _read(policy_path)
    rewrites = _rewrite_map(policy, task_id=task_id, commit=target.source_commit)
    file_diffs, source_imports, target_imports, declarations = _compare_files(source_files, target_files, policy, rewrites, task_id=task_id)
    consumer_manifest_path = consumer_manifest_path.resolve()
    consumer_builds = _consumer_evidence(
        consumer_manifest_path, [path.resolve() for path in consumer_build_paths],
        task_id=task_id, target=target, target_repo=target_repo,
        exact_context=exact_context,
    )
    provenance = _author_provenance(
        task_id=task_id, kenneth_repo=kenneth_repo.resolve(),
        kenneth_commit=kenneth_commit,
        author_decision_path=author_decision_path.resolve() if author_decision_path else None,
        target_files=target_files,
    )
    timestamp = created_at or datetime.now(timezone.utc).isoformat()
    receipt = {
        "schema": BOUNDARY_DELTA_SCHEMA, "task_id": task_id, "created_at": timestamp,
        "transformation_kind": TRANSFORMATION_KIND, "semantic_upgrade": False,
        "source_authority": {
            "schema": RECOVERY_SCHEMA, "review_id": str(review.get("review_id", "") or ""),
            "prompt_version": int(review["prompt_version"]), "rubric_version": int(review["rubric_version"]),
            "artifact": _ref(source_authority_path),
            "result_evidence_hash": str(authority.get("artifacts", {}).get("result", {}).get("sha256", "")),
        },
        "source_subject": _subject_payload(source), "target_subject": _subject_payload(target),
        "target_commit": target.source_commit,
        "diff": {
            "allowed_classes": ["byte_exact", "path_relocation", "import_namespace_docs", "documentation_or_whitespace", "whole_file_reassembly"],
            "module_rewrites": [{"source": key, "target": rewrites[key]} for key in sorted(rewrites)],
            "open_namespace_changes": policy.get("open_namespace_changes", []),
            "import_changes": policy.get("import_changes", []),
            "section_changes": policy.get("section_changes", []),
            "files": file_diffs,
        },
        "public_declarations": {
            "status": "unchanged", "count": len(declarations),
            "manifest": declarations, "manifest_sha256": sha256_json(declarations),
        },
        "dependencies": {
            "status": "exact_declared_import_boundary",
            "normalized_source_direct_imports": source_imports,
            "target_direct_imports": target_imports,
            "source_manifest_sha256": sha256_json(source_imports),
            "target_manifest_sha256": sha256_json(target_imports),
        },
        "author_provenance": provenance,
        "content_provenance": {
            "source": source_content_provenance,
            "target": target_content_provenance,
        },
        "artifacts": {
            "source_scope": {
                **_ref(source_scope_path),
                "schema": str(source_scope_payload.get("schema_version", source_scope_payload.get("schema", "")) or ""),
            },
            "policy": _ref(policy_path),
            "target_build": _ref(target_build_path), "consumer_manifest": _ref(consumer_manifest_path),
            "consumer_builds": consumer_builds,
        },
        "checks": {
            "source_applied_modern_r9_pass": "pass", "source_complete_bundle": "pass",
            "target_complete_bundle_at_pinned_commit": "pass", "per_file_diff_classified": "pass",
            "lean_payload_token_invariant": "pass", "public_declaration_signatures_unchanged": "pass",
            "import_boundary_exactly_declared": "pass", "target_build_and_forbidden_scan": "pass",
            "direct_consumers_built_and_scanned": "pass", "kenneth_provenance_or_author_decision": "pass",
            "no_semantic_or_rubric_upgrade": "pass", "target_build_schema": target_build.get("schema"),
        },
    }
    if input_manifest_path is not None:
        input_manifest_path = input_manifest_path.resolve()
        receipt["orchestration"] = {
            "input_manifest": _ref(input_manifest_path),
            **dict(orchestration_provenance or {}),
        }
    return receipt


def validate_verified_boundary_delta(
    receipt_path: Path, receipt: Mapping[str, Any] | None = None, *,
    source_repos: Sequence[Path], target_repo: Path, kenneth_repo: Path,
) -> tuple[dict[str, Any], SubjectBundle, SubjectBundle]:
    receipt_path = receipt_path.resolve(); payload = dict(receipt or _read(receipt_path))
    if payload.get("schema") != BOUNDARY_DELTA_SCHEMA:
        raise BoundaryDeltaReceiptError("unsupported boundary-delta receipt schema")
    artifacts = payload.get("artifacts"); authority = payload.get("source_authority"); provenance = payload.get("author_provenance")
    if not isinstance(artifacts, Mapping) or not isinstance(authority, Mapping) or not isinstance(provenance, Mapping):
        raise BoundaryDeltaReceiptError("boundary-delta receipt is incomplete")
    def resolve(raw: Any, label: str) -> Path:
        if not isinstance(raw, Mapping):
            raise BoundaryDeltaReceiptError(f"{label} artifact reference is missing")
        path = Path(str(raw.get("path", "") or "")); path = path if path.is_absolute() else receipt_path.parent / path; path = path.resolve()
        if not path.is_file() or not _HEX64.fullmatch(str(raw.get("sha256", "") or "")) or sha256_file(path) != raw.get("sha256"):
            raise BoundaryDeltaReceiptError(f"{label} artifact reference mismatch")
        return path
    source_authority = resolve(authority.get("artifact"), "source authority")
    source_scope = resolve(artifacts.get("source_scope"), "source scope")
    policy = resolve(artifacts.get("policy"), "policy")
    target_build = resolve(artifacts.get("target_build"), "target build")
    consumer_manifest = resolve(artifacts.get("consumer_manifest"), "consumer manifest")
    raw_consumer_builds = artifacts.get("consumer_builds")
    if not isinstance(raw_consumer_builds, list) or any(
        not isinstance(item, Mapping) for item in raw_consumer_builds
    ):
        raise BoundaryDeltaReceiptError("consumer build artifact references are malformed")
    consumer_builds = [resolve(item, "consumer build") for item in raw_consumer_builds]
    decision = provenance.get("artifact")
    decision_path = resolve(decision, "author decision") if isinstance(decision, Mapping) else None
    orchestration = payload.get("orchestration")
    input_manifest_path = None
    exact_context = None
    if orchestration is not None:
        if not isinstance(orchestration, Mapping):
            raise BoundaryDeltaReceiptError("boundary-delta orchestration evidence is malformed")
        input_manifest_path = resolve(orchestration.get("input_manifest"), "input manifest")
        authority_snapshot_raw = orchestration.get("batch_authority_manifest")
        if authority_snapshot_raw is not None:
            authority_snapshot = resolve(authority_snapshot_raw, "batch authority snapshot")
            task_id = canonicalize_block_id(str(payload.get("task_id", "") or ""))
            if (
                not isinstance(authority_snapshot_raw, Mapping)
                or authority_snapshot.stem != str(authority_snapshot_raw.get("sha256", "") or "")
                or authority_snapshot.parent.name != "authority"
                or input_manifest_path.stem != str(orchestration["input_manifest"].get("sha256", "") or "")
                or input_manifest_path.parent.name != "input"
                or authority_snapshot.parent.parent != input_manifest_path.parent.parent
            ):
                raise BoundaryDeltaReceiptError("boundary content-addressed snapshot path/schema mismatch")
            original_authority = orchestration.get("batch_authority_original")
            original_input = orchestration.get("batch_authority_input_original")
            if (
                not isinstance(original_authority, Mapping)
                or set(original_authority) != {"path", "sha256"}
                or not isinstance(original_input, Mapping)
                or set(original_input) != {"declared", "resolved"}
                or not isinstance(original_input.get("declared"), Mapping)
                or set(original_input["declared"]) != {"path", "sha256"}
                or not isinstance(original_input.get("resolved"), Mapping)
                or set(original_input["resolved"]) != {"path", "sha256"}
            ):
                raise BoundaryDeltaReceiptError("boundary snapshot original provenance is malformed")
            snapshot_payload = _read(authority_snapshot)
            items = snapshot_payload.get("items")
            matching = [
                item for item in items
                if isinstance(item, Mapping) and item.get("task_id") == task_id
            ] if isinstance(items, list) else []
            if (
                len(matching) != 1
                or snapshot_payload.get("schema") != BATCH_AUTHORITY_MANIFEST_SCHEMA
                or original_authority.get("sha256") != authority_snapshot_raw.get("sha256")
                or matching[0].get("input_manifest") != original_input["declared"]
                or original_input["resolved"].get("sha256") != original_input["declared"].get("sha256")
                or orchestration["input_manifest"].get("sha256") != original_input["declared"].get("sha256")
                or _read(input_manifest_path).get("task_id") != task_id
            ):
                raise BoundaryDeltaReceiptError("boundary snapshots do not replay original authority binding")
        if isinstance(orchestration.get("central_exact_build_override"), Mapping):
            target_raw = payload.get("target_subject")
            task_id = canonicalize_block_id(str(payload.get("task_id", "") or ""))
            commit = str(target_raw.get("source_commit", "") or "") if isinstance(target_raw, Mapping) else ""
            consumer_ids = []
            for item in raw_consumer_builds:
                path = resolve(item, "consumer build")
                consumer_ids.append(canonicalize_block_id(str(_read(path).get("task_id", "") or "")))
            exact_context = _exact_catalog_context(
                target_repo=target_repo, commit=commit,
                task_ids=[task_id, *consumer_ids],
            )
    rebuilt = build_verified_boundary_delta(
        source_authority_path=source_authority, source_scope_path=source_scope,
        source_repos=source_repos, target_build_path=target_build, target_repo=target_repo,
        policy_path=policy, consumer_manifest_path=consumer_manifest,
        consumer_build_paths=consumer_builds, kenneth_repo=kenneth_repo,
        kenneth_commit=str(provenance.get("commit", "") or ""), author_decision_path=decision_path,
        created_at=str(payload.get("created_at", "") or ""),
        input_manifest_path=input_manifest_path,
        exact_context=exact_context,
        orchestration_provenance=(
            {key: value for key, value in orchestration.items() if key != "input_manifest"}
            if isinstance(orchestration, Mapping) else None
        ),
    )
    if sha256_json(_receipt_match_payload(payload)) != sha256_json(
        _receipt_match_payload(rebuilt)
    ):
        raise BoundaryDeltaReceiptError("boundary-delta receipt does not match validated evidence")
    return rebuilt, _subject(rebuilt["source_subject"], task_id=rebuilt["task_id"], label="source"), _subject(rebuilt["target_subject"], task_id=rebuilt["task_id"], label="target")


def _resolve_input_ref(manifest_path: Path, raw: Any, *, label: str) -> Path:
    if not isinstance(raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{label} reference is missing")
    value = str(raw.get("path", "") or "")
    expected = str(raw.get("sha256", "") or "")
    path = Path(value)
    path = path if path.is_absolute() else manifest_path.parent / path
    path = path.resolve()
    if not path.is_file() or not _HEX64.fullmatch(expected) or sha256_file(path) != expected:
        raise BoundaryDeltaReceiptError(f"{label} reference mismatch")
    return path


def _resolve_workspace_ref(
    raw: Any, *, workspace_root: Path, label: str,
) -> Path:
    """Resolve one explicitly named authority/input artifact from a fixed root."""

    if not isinstance(raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{label} reference is missing")
    value = str(raw.get("path", "") or "")
    expected = str(raw.get("sha256", "") or "")
    if not value or not _HEX64.fullmatch(expected):
        raise BoundaryDeltaReceiptError(f"{label} reference is malformed")
    declared = Path(value).expanduser()
    path = declared if declared.is_absolute() else workspace_root.resolve() / declared
    path = path.resolve()
    if not declared.is_absolute():
        try:
            path.relative_to(workspace_root.resolve())
        except ValueError as exc:
            raise BoundaryDeltaReceiptError(f"{label} escapes the explicit workspace root") from exc
    if not path.is_file() or sha256_file(path) != expected:
        raise BoundaryDeltaReceiptError(f"{label} reference mismatch")
    return path


def _resolve_registered_source_scope(
    raw: Any, *, source_authority_path: Path, workspace_root: Path | None,
    manifest_path: Path, task_id: str,
) -> Path:
    """Resolve only registered source-scope evidence shapes; never infer by name."""

    if isinstance(raw, Mapping) and "path" in raw and "sha256" in raw:
        if "schema" not in raw and workspace_root is None:
            return _resolve_input_ref(manifest_path, raw, label=f"{task_id}: source scope")
        if workspace_root is not None:
            resolved = _resolve_workspace_ref(
                raw, workspace_root=workspace_root, label=f"{task_id}: source scope",
            )
        else:
            resolved = _resolve_input_ref(manifest_path, raw, label=f"{task_id}: source scope")
        payload = _read(resolved)
        schema = str(payload.get("schema_version", payload.get("schema", "")) or "")
        if raw.get("schema") != schema:
            raise BoundaryDeltaReceiptError(f"{task_id}: source scope declared schema mismatch")
        authority = _read(source_authority_path)
        if schema == "toy-apollo.workspace-review-binding.v1":
            if (
                set(raw) != {"bundle_hash", "files", "path", "schema", "scope_kind", "sha256", "subject_id", "validation"}
                or raw.get("scope_kind") != "workspace_review_binding"
                or raw.get("validation") != "pass"
            ):
                raise BoundaryDeltaReceiptError(f"{task_id}: unsupported workspace-binding scope structure")
            source = _source_scope(resolved, task_id=task_id, authority=authority)
            if (
                raw.get("subject_id") != source.subject_id
                or raw.get("bundle_hash") != source.bundle_hash
                or raw.get("files") != source.manifest()
            ):
                raise BoundaryDeltaReceiptError(f"{task_id}: workspace-binding scope identity mismatch")
            return resolved
        if schema != RECOVERY_SCHEMA or resolved != source_authority_path.resolve():
            raise BoundaryDeltaReceiptError(f"{task_id}: unsupported source-scope artifact schema")
        try:
            validated_authority, reviewed = validate_historical_review_apply_recovery(
                source_authority_path, authority,
            )
        except ValueError as exc:
            raise BoundaryDeltaReceiptError(f"{task_id}: source-scope recovery failed validation: {exc}") from exc
        if reviewed.subject_kind == "legacy_bound":
            if (
                set(raw) != {"error", "legacy_embedded_single_file_evidence", "path", "schema", "scope_kind", "sha256", "subject", "validation"}
                or raw.get("scope_kind") != "legacy_embedded_single_file_scope"
                or raw.get("validation") != "pending_framework_test"
                or raw.get("subject") is not None
                or not isinstance(raw.get("legacy_embedded_single_file_evidence"), Mapping)
            ):
                raise BoundaryDeltaReceiptError(f"{task_id}: unsupported legacy embedded source-scope structure")
            _legacy_embedded_single_file_scope(
                resolved, validated_authority, task_id=task_id,
                authority=validated_authority, reviewed_subject=reviewed,
            )
            return resolved
        if (
            set(raw) != {"error", "legacy_embedded_single_file_evidence", "path", "schema", "scope_kind", "sha256", "subject", "validation"}
            or raw.get("scope_kind") != "review_input_bundle"
            or raw.get("validation") != "pass"
            or raw.get("error") is not None
            or raw.get("legacy_embedded_single_file_evidence") is not None
        ):
            raise BoundaryDeltaReceiptError(f"{task_id}: unsupported recovery exact-scope structure")
        source = _source_scope(resolved, task_id=task_id, authority=validated_authority)
        expected_subject = {
            "subject_id": source.subject_id, "bundle_hash": source.bundle_hash,
            "primary_hash": source.primary_hash, "primary_path": source.primary_path,
            "files": source.manifest(),
        }
        if raw.get("subject") != expected_subject:
            raise BoundaryDeltaReceiptError(f"{task_id}: recovery exact-scope identity mismatch")
        return resolved
    if not isinstance(raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: source scope reference is missing")
    if (
        set(raw) != {
            "bundle_hash", "content_resolution", "files", "primary_hash", "primary_path",
            "scope_kind", "subject_id", "validation", "validator",
        }
        or
        raw.get("scope_kind") != "review_input_bundle"
        or raw.get("validator") != "src.toy_apollo.state_boundary_delta_receipt._source_scope"
        or raw.get("validation") != "pass"
        or not isinstance(raw.get("files"), list)
        or not raw.get("files")
    ):
        raise BoundaryDeltaReceiptError(f"{task_id}: unsupported embedded source-scope structure")
    authority = _read(source_authority_path)
    if authority.get("schema") != RECOVERY_SCHEMA:
        raise BoundaryDeltaReceiptError(
            f"{task_id}: embedded review-input scope requires registered recovery authority"
        )
    source = _source_scope(source_authority_path, task_id=task_id, authority=authority)
    declared = {
        "subject_id": str(raw.get("subject_id", "") or ""),
        "bundle_hash": str(raw.get("bundle_hash", "") or ""),
        "primary_hash": str(raw.get("primary_hash", "") or ""),
        "primary_path": str(raw.get("primary_path", "") or ""),
        "files": raw.get("files"),
    }
    expected = {
        "subject_id": source.subject_id, "bundle_hash": source.bundle_hash,
        "primary_hash": source.primary_hash, "primary_path": source.primary_path,
        "files": source.manifest(),
    }
    if declared != expected:
        raise BoundaryDeltaReceiptError(
            f"{task_id}: embedded source scope differs from registered recovery exact bundle"
        )
    return source_authority_path.resolve()


def load_boundary_batch_authority_manifest(
    path: Path, *, workspace_root: Path, expected_sha256: str,
    expected_target_commit: str, expected_kenneth_commit: str,
    verified_bytes: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, tuple[Path, dict[str, Any]]]]:
    """Validate the immutable batch authority and its exact input-manifest refs."""

    path = path.expanduser().resolve()
    authority_capture: list[bytes] = []
    payload = dict(_read_sha256_bound_json(
        path, expected_sha256, label="batch authority manifest", capture=authority_capture,
    ))
    if verified_bytes is not None:
        verified_bytes["authority"] = authority_capture[0]
        verified_bytes["inputs"] = {}
    if payload.get("schema") != BATCH_AUTHORITY_MANIFEST_SCHEMA:
        raise BoundaryDeltaReceiptError("unsupported boundary batch authority manifest")
    if payload.get("target_commit") != expected_target_commit:
        raise BoundaryDeltaReceiptError("batch authority target commit mismatch")
    if payload.get("kenneth_commit") != expected_kenneth_commit:
        raise BoundaryDeltaReceiptError("batch authority Kenneth commit mismatch")
    items = payload.get("items")
    closure = payload.get("unique_planned_exact_build_tasks")
    counts = payload.get("counts")
    if not isinstance(items, list) or not isinstance(closure, list) or not isinstance(counts, Mapping):
        raise BoundaryDeltaReceiptError("boundary batch authority is incomplete")
    if counts.get("boundary_targets") != len(items) or counts.get("unique_exact_build_closure_tasks") != len(closure):
        raise BoundaryDeltaReceiptError("boundary batch authority declared counts mismatch")
    if (
        any(not isinstance(task, str) or canonicalize_block_id(task) != task or not is_canonical_block_id(task) for task in closure)
        or len(set(closure)) != len(closure)
    ):
        raise BoundaryDeltaReceiptError("boundary batch authority build closure is invalid")
    entries: dict[str, tuple[Path, dict[str, Any]]] = {}
    derived_closure: set[str] = set()
    for index, raw in enumerate(items):
        if not isinstance(raw, Mapping):
            raise BoundaryDeltaReceiptError(f"boundary batch authority item {index} is malformed")
        item = dict(raw)
        task_id = canonicalize_block_id(str(item.get("task_id", "") or ""))
        if not task_id or task_id != item.get("task_id") or not is_canonical_block_id(task_id) or task_id in entries:
            raise BoundaryDeltaReceiptError(f"boundary batch authority item {index} has an invalid task")
        if (
            item.get("pure_comparator") != "pass"
            or item.get("overall_status") != "ready_for_exact_build_evidence"
            or item.get("build_run") is not False
            or item.get("final_receipt_emitted") is not False
        ):
            raise BoundaryDeltaReceiptError(f"{task_id}: batch authority is not a dry comparator PASS")
        input_path = _resolve_workspace_ref(
            item.get("input_manifest"), workspace_root=workspace_root,
            label=f"{task_id}: authoritative input manifest",
        )
        if not isinstance(item.get("input_manifest"), Mapping) or set(item["input_manifest"]) != {"path", "sha256"}:
            raise BoundaryDeltaReceiptError(f"{task_id}: authority input reference is not exact path+sha256")
        input_capture: list[bytes] = []
        input_payload = _read_sha256_bound_json(
            input_path, str(item["input_manifest"].get("sha256", "") or ""),
            label=f"{task_id}: authoritative input manifest",
            capture=input_capture,
        )
        if verified_bytes is not None:
            verified_bytes["inputs"][task_id] = input_capture[0]
        if input_payload.get("schema") != BOUNDARY_INPUT_MANIFEST_SCHEMA or input_payload.get("task_id") != task_id:
            raise BoundaryDeltaReceiptError(f"{task_id}: authoritative input manifest identity mismatch")
        consumer_ids = item.get("direct_consumer_ids")
        if (
            not isinstance(consumer_ids, list)
            or len(consumer_ids) != item.get("direct_consumer_count")
            or any(not isinstance(consumer, str) or canonicalize_block_id(consumer) != consumer for consumer in consumer_ids)
            or len(set(consumer_ids)) != len(consumer_ids)
        ):
            raise BoundaryDeltaReceiptError(f"{task_id}: authority direct-consumer set is invalid")
        derived_closure.add(task_id)
        derived_closure.update(consumer_ids)
        entries[task_id] = (input_path, item)
    if set(closure) != derived_closure:
        raise BoundaryDeltaReceiptError("boundary batch authority build closure does not match target+consumer union")
    return payload, entries


def _assert_batch_authority_fresh(
    *, authority_manifest_path: Path, authority_manifest_sha256: str,
    authority_item: Mapping[str, Any], authority_input_ref: Mapping[str, Any],
    input_manifest_path: Path, input_snapshot_ref: Mapping[str, Any],
    task_id: str, stage: str,
) -> None:
    """Re-read immutable batch bindings at every material TOCTOU boundary."""

    authority_path = authority_manifest_path.expanduser().resolve()
    if not authority_path.is_file():
        raise BoundaryDeltaReceiptError(f"{task_id}: batch authority changed at {stage}")
    expected_ref = dict(authority_input_ref)
    if set(expected_ref) != {"path", "sha256"} or authority_item.get("input_manifest") != expected_ref:
        raise BoundaryDeltaReceiptError(f"{task_id}: in-memory authority input binding changed at {stage}")
    try:
        payload = _read_sha256_bound_json(
            authority_path, authority_manifest_sha256,
            label=f"{task_id}: batch authority at {stage}",
        )
    except BoundaryDeltaReceiptError as exc:
        raise BoundaryDeltaReceiptError(f"{task_id}: batch authority changed at {stage}: {exc}") from exc
    items = payload.get("items")
    matching = [
        item for item in items
        if isinstance(item, Mapping) and item.get("task_id") == task_id
    ] if isinstance(items, list) else []
    if len(matching) != 1 or matching[0].get("input_manifest") != expected_ref:
        raise BoundaryDeltaReceiptError(f"{task_id}: authority input path/hash changed at {stage}")
    expected_snapshot = dict(input_snapshot_ref)
    if (
        set(expected_snapshot) != {"path", "sha256"}
        or expected_snapshot.get("path") != str(input_manifest_path.resolve())
        or expected_snapshot.get("sha256") != expected_ref.get("sha256")
    ):
        raise BoundaryDeltaReceiptError(f"{task_id}: input snapshot binding changed at {stage}")
    _read_sha256_bound_json(
        input_manifest_path, str(expected_snapshot["sha256"]),
        label=f"{task_id}: input snapshot at {stage}",
    )


def _exact_catalog_context(
    *, target_repo: Path, commit: str, task_ids: Sequence[str],
) -> dict[str, Any]:
    runtime_root = Path(__file__).resolve().parents[2]
    try:
        catalog = load_catalog(
            workspace_root=runtime_root.parent, runtime_root=runtime_root,
            mat_root=target_repo.resolve(),
        )
        validate_catalog_compatible_mat_commit(
            catalog, mat_root=target_repo.resolve(), commit=commit,
        )
        subjects = discover_catalog_git_subjects(
            target_repo.resolve(), ref=commit, catalog=catalog,
            source_repo="mat", layout="mat", task_ids=task_ids,
        )
        primary, owned = catalog_owned_build_modules(catalog, task_ids)
    except (CatalogError, ReconciliationError, ExactBuildBatchError) as exc:
        raise BoundaryDeltaReceiptError(f"cannot reconstruct exact-build catalog context: {exc}") from exc
    if set(subjects) != set(task_ids):
        raise BoundaryDeltaReceiptError("catalog context does not cover the exact build closure")
    return {"commit": commit, "subjects": subjects, "primary_modules": primary, "owned_modules": owned}


def _validate_context_exact_build(
    path: Path, *, task_id: str, context: Mapping[str, Any],
) -> tuple[Mapping[str, Any], SubjectBundle]:
    subjects = context.get("subjects")
    primary = context.get("primary_modules")
    owned = context.get("owned_modules")
    if not isinstance(subjects, Mapping) or not isinstance(primary, Mapping) or not isinstance(owned, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: exact-build catalog context is malformed")
    subject = subjects.get(task_id)
    if not isinstance(subject, SubjectBundle):
        raise BoundaryDeltaReceiptError(f"{task_id}: current catalog subject is missing")
    payload = _read(path)
    focused = payload.get("focused_build")
    if not isinstance(focused, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: exact-build focused evidence is missing")
    checkout = Path(str(focused.get("cwd", "") or "")).expanduser()
    try:
        validate_current_exact_build_receipt(
            path, subject=subject, primary_module=str(primary[task_id]),
            task_modules=owned[task_id], commit=str(context.get("commit", "") or ""),
            checkout=checkout,
        )
    except (ExactBuildBatchError, KeyError) as exc:
        raise BoundaryDeltaReceiptError(f"{task_id}: exact-build validation failed: {exc}") from exc
    return payload, subject


def _planned_build_path(
    manifest_path: Path, raw: Any, *, task_id: str, exact_build_root: Path,
) -> Path:
    if not isinstance(raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: planned exact-build entry is missing")
    declared_task = canonicalize_block_id(str(raw.get("task_id", "") or ""))
    if declared_task != task_id:
        raise BoundaryDeltaReceiptError(f"{task_id}: planned exact-build task mismatch")
    value = str(raw.get("receipt_path", raw.get("path", "")) or "")
    if value:
        path = Path(value)
        path = path if path.is_absolute() else manifest_path.parent / path
    else:
        path = exact_build_root / task_id / "exact_mat_build_receipt_v1.json"
    path = path.resolve()
    if not path.is_file():
        raise BoundaryDeltaReceiptError(f"{task_id}: exact-build receipt is missing: {path}")
    expected_hash = str(raw.get("sha256", "") or "")
    if expected_hash and (not _HEX64.fullmatch(expected_hash) or sha256_file(path) != expected_hash):
        raise BoundaryDeltaReceiptError(f"{task_id}: exact-build receipt hash mismatch")
    return path


def _prepare_boundary_batch_task(
    task_dir: Path, *, source_repos: Sequence[Path], target_repo: Path,
    kenneth_repo: Path, expected_target_commit: str, expected_kenneth_commit: str,
    input_manifest_path: Path | None = None,
    workspace_root: Path | None = None,
    exact_build_root: Path | None = None,
    exact_context: Mapping[str, Any] | None = None,
    authority_manifest_path: Path | None = None,
    authority_manifest_sha256: str = "",
    authority_item: Mapping[str, Any] | None = None,
    authority_input_ref: Mapping[str, Any] | None = None,
    input_snapshot_ref: Mapping[str, Any] | None = None,
    original_authority_ref: Mapping[str, Any] | None = None,
    original_input_ref: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any], Path, dict[str, Any]]:
    task_dir = task_dir.resolve()
    manifest_path = (
        input_manifest_path.expanduser().resolve()
        if input_manifest_path is not None
        else task_dir / "boundary_input_manifest.json"
    )
    authority_guard: dict[str, Any] | None = None
    if authority_manifest_path is not None:
        if authority_item is None or authority_input_ref is None or input_snapshot_ref is None:
            raise BoundaryDeltaReceiptError("batch authority freshness guard is incomplete")
        authority_guard = {
            "authority_manifest_path": authority_manifest_path.resolve(),
            "authority_manifest_sha256": authority_manifest_sha256,
            "authority_item": authority_item,
            "authority_input_ref": dict(authority_input_ref),
            "input_manifest_path": manifest_path,
            "input_snapshot_ref": dict(input_snapshot_ref),
            "task_id": task_dir.name,
        }
        _assert_batch_authority_fresh(**authority_guard, stage="prepare-before-read")
    if not manifest_path.is_file():
        raise BoundaryDeltaReceiptError(f"missing boundary input manifest: {manifest_path}")
    if authority_manifest_path is None and manifest_path.parent != task_dir:
        raise BoundaryDeltaReceiptError(f"boundary input manifest is not task-local: {manifest_path}")
    manifest = (
        _read_sha256_bound_json(
            manifest_path, str(input_snapshot_ref.get("sha256", "") or ""),
            label=f"{task_dir.name}: authoritative input manifest during prepare",
        )
        if authority_input_ref is not None else _read(manifest_path)
    )
    if manifest.get("schema") != BOUNDARY_INPUT_MANIFEST_SCHEMA:
        raise BoundaryDeltaReceiptError(f"unsupported boundary input manifest schema: {manifest_path}")
    task_id = canonicalize_block_id(str(manifest.get("task_id", "") or ""))
    if not task_id or not is_canonical_block_id(task_id) or task_dir.name != task_id:
        raise BoundaryDeltaReceiptError(f"boundary input task/directory mismatch: {task_dir}")
    if not _HEX40.fullmatch(expected_target_commit) or not _HEX40.fullmatch(expected_kenneth_commit):
        raise BoundaryDeltaReceiptError(f"{task_id}: expected commits must be full Git commit ids")

    def resolve_input(raw: Any, *, label: str) -> Path:
        if workspace_root is not None:
            return _resolve_workspace_ref(raw, workspace_root=workspace_root, label=label)
        return _resolve_input_ref(manifest_path, raw, label=label)

    policy_path = resolve_input(manifest.get("policy"), label=f"{task_id}: policy")
    if policy_path != (task_dir / "boundary_policy.json").resolve():
        raise BoundaryDeltaReceiptError(f"{task_id}: policy must be task-local boundary_policy.json")
    source_authority = resolve_input(
        manifest.get("source_authority"), label=f"{task_id}: source authority",
    )
    source_scope = _resolve_registered_source_scope(
        manifest.get("source_scope"), source_authority_path=source_authority,
        workspace_root=workspace_root, manifest_path=manifest_path, task_id=task_id,
    )
    consumer_manifest = resolve_input(
        manifest.get("direct_consumer_manifest"), label=f"{task_id}: direct-consumer manifest",
    )

    target_raw = manifest.get("target_repository")
    if not isinstance(target_raw, Mapping) or str(target_raw.get("commit", "") or "") != expected_target_commit:
        raise BoundaryDeltaReceiptError(f"{task_id}: input target commit mismatch")
    declared_target_repo = Path(str(target_raw.get("path", "") or ""))
    if declared_target_repo and declared_target_repo.resolve() != target_repo.resolve():
        if workspace_root is None or _git_common_dir(
            declared_target_repo, label=f"{task_id}: declared target repository",
        ) != _git_common_dir(target_repo, label=f"{task_id}: build target repository"):
            raise BoundaryDeltaReceiptError(f"{task_id}: input target repository mismatch")
    declared_absent = manifest.get("kenneth_absent_provenance")
    kenneth_raw = manifest.get("kenneth_provenance")
    if kenneth_raw is None:
        kenneth_raw = declared_absent
    if not isinstance(kenneth_raw, Mapping) or str(kenneth_raw.get("commit", "") or "") != expected_kenneth_commit:
        raise BoundaryDeltaReceiptError(f"{task_id}: input Kenneth commit mismatch")
    if declared_absent is not None and manifest.get("kenneth_provenance") is not None:
        raise BoundaryDeltaReceiptError(f"{task_id}: input declares conflicting Kenneth provenance")

    planned = manifest.get("planned_exact_build_receipts")
    if not isinstance(planned, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: planned exact-build evidence is missing")
    planned_target = planned.get("target")
    if not isinstance(planned_target, Mapping) or canonicalize_block_id(str(planned_target.get("task_id", "") or "")) != task_id:
        raise BoundaryDeltaReceiptError(f"{task_id}: planned target exact-build task mismatch")
    resolved_build_root = (
        exact_build_root.expanduser().resolve()
        if exact_build_root is not None else task_dir.parent / "exact_builds"
    )
    target_build = (
        (resolved_build_root / task_id / "exact_mat_build_receipt_v1.json").resolve()
        if exact_build_root is not None
        else _planned_build_path(
            manifest_path, planned_target, task_id=task_id,
            exact_build_root=resolved_build_root,
        )
    )
    if not target_build.is_file():
        raise BoundaryDeltaReceiptError(f"{task_id}: exact-build receipt is missing: {target_build}")
    target_build_payload, target_subject = _target_build(target_build, task_id=task_id)
    if exact_context is not None:
        _strict_payload, strict_subject = _validate_context_exact_build(
            target_build, task_id=task_id, context=exact_context,
        )
        if strict_subject.subject_id != target_subject.subject_id:
            raise BoundaryDeltaReceiptError(f"{task_id}: strict target subject mismatch")
    if target_subject.source_commit != expected_target_commit:
        raise BoundaryDeltaReceiptError(f"{task_id}: target exact-build commit mismatch")
    for key, actual in (
        ("subject_id", target_subject.subject_id), ("bundle_hash", target_subject.bundle_hash),
        ("primary_hash", target_subject.primary_hash),
    ):
        declared = str(target_raw.get(key, "") or "")
        if declared != actual:
            raise BoundaryDeltaReceiptError(f"{task_id}: input target {key} mismatch")
    declared_files = target_raw.get("files")
    if declared_files != target_subject.manifest():
        raise BoundaryDeltaReceiptError(f"{task_id}: input target file manifest mismatch")

    consumer_payload = _read(consumer_manifest)
    consumer_rows = consumer_payload.get("consumers")
    if not isinstance(consumer_rows, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: direct-consumer manifest is malformed")
    consumer_ids = []
    for row in consumer_rows:
        consumer_id = canonicalize_block_id(str(row.get("task_id", "") or "")) if isinstance(row, Mapping) else ""
        if not consumer_id or not is_canonical_block_id(consumer_id) or consumer_id in consumer_ids:
            raise BoundaryDeltaReceiptError(f"{task_id}: malformed or duplicate direct consumer")
        consumer_ids.append(consumer_id)
    planned_consumers = planned.get("consumers")
    if not isinstance(planned_consumers, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: planned consumer exact-build evidence is malformed")
    planned_by_id: dict[str, Mapping[str, Any]] = {}
    for row in planned_consumers:
        consumer_id = canonicalize_block_id(str(row.get("task_id", "") or "")) if isinstance(row, Mapping) else ""
        if not consumer_id or consumer_id in planned_by_id:
            raise BoundaryDeltaReceiptError(f"{task_id}: malformed or duplicate planned consumer build")
        planned_by_id[consumer_id] = row
    if set(planned_by_id) != set(consumer_ids):
        raise BoundaryDeltaReceiptError(f"{task_id}: planned builds do not exactly cover direct consumers")
    consumer_builds = []
    for consumer_id in sorted(consumer_ids):
        path = (
            (resolved_build_root / consumer_id / "exact_mat_build_receipt_v1.json").resolve()
            if exact_build_root is not None
            else _planned_build_path(
                manifest_path, planned_by_id[consumer_id], task_id=consumer_id,
                exact_build_root=resolved_build_root,
            )
        )
        if not path.is_file():
            raise BoundaryDeltaReceiptError(f"{task_id}: consumer {consumer_id} exact-build receipt is missing: {path}")
        if exact_context is not None:
            _validate_context_exact_build(path, task_id=consumer_id, context=exact_context)
        consumer_builds.append(path)

    decision_path = None
    decision_raw = manifest.get("kenneth_author_decision")
    if decision_raw is not None:
        decision_path = resolve_input(
            decision_raw, label=f"{task_id}: Kenneth author decision",
        )

    if workspace_root is not None:
        _target_content, = (_bundle_content([target_repo.resolve()], target_subject, label="target")[0],)
        actual_kenneth = _author_provenance(
            task_id=task_id, kenneth_repo=kenneth_repo.resolve(),
            kenneth_commit=expected_kenneth_commit, author_decision_path=decision_path,
            target_files=_target_content,
        )
        kenneth_raw = _normalize_declared_kenneth_provenance(
            kenneth_raw, actual=actual_kenneth, task_id=task_id,
            kenneth_commit=expected_kenneth_commit, target_files=_target_content,
        )

    if authority_item is not None:
        if authority_item.get("target_subject_id") != target_subject.subject_id or authority_item.get("target_bundle_hash") != target_subject.bundle_hash:
            raise BoundaryDeltaReceiptError(f"{task_id}: batch authority target identity mismatch")
        for key, path in (("policy", policy_path), ("direct_consumer_manifest", consumer_manifest)):
            raw_ref = authority_item.get(key)
            if not isinstance(raw_ref, Mapping) or raw_ref.get("sha256") != sha256_file(path):
                raise BoundaryDeltaReceiptError(f"{task_id}: batch authority {key} hash mismatch")
    final_raw = manifest.get("final_boundary_receipt")
    if not isinstance(final_raw, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: final receipt declaration is missing")
    final_path = Path(str(final_raw.get("planned_path", "") or ""))
    final_path = final_path if final_path.is_absolute() else manifest_path.parent / final_path
    final_path = final_path.resolve()
    canonical_final = (task_dir / "validated_boundary_delta_receipt_v1.json").resolve()
    if final_path != canonical_final:
        raise BoundaryDeltaReceiptError(f"{task_id}: final receipt path is not canonical")

    orchestration_provenance: dict[str, Any] = {}
    if authority_manifest_path is not None and exact_build_root is not None:
        orchestration_provenance = {
            "batch_authority_manifest": {
                "path": str(authority_manifest_path.resolve()),
                "sha256": authority_manifest_sha256,
            },
            "batch_authority_original": dict(original_authority_ref or {}),
            "batch_authority_input_original": {
                "declared": dict(authority_input_ref or {}),
                "resolved": dict(original_input_ref or {}),
            },
            "central_exact_build_override": {
                "root": str(resolved_build_root),
                "receipt_name": "exact_mat_build_receipt_v1.json",
                "superseded_planned_exact_builds_sha256": sha256_json(planned),
                "target": _ref(target_build),
                "consumers": [_ref(path) for path in consumer_builds],
            },
        }
    build_args = {
        "source_authority_path": source_authority, "source_scope_path": source_scope,
        "source_repos": [Path(path).resolve() for path in source_repos],
        "target_build_path": target_build, "target_repo": target_repo.resolve(),
        "policy_path": policy_path, "consumer_manifest_path": consumer_manifest,
        "consumer_build_paths": consumer_builds, "kenneth_repo": kenneth_repo.resolve(),
        "kenneth_commit": expected_kenneth_commit, "author_decision_path": decision_path,
        "input_manifest_path": manifest_path,
        "exact_context": exact_context,
        "orchestration_provenance": orchestration_provenance,
    }
    expected = {
        "task_id": task_id,
        "input_manifest": {
            "path": str(manifest_path.resolve()),
            "sha256": str((input_snapshot_ref or {}).get("sha256", "")) or sha256_file(manifest_path),
        },
        "source_authority": _ref(source_authority), "source_scope": _ref(source_scope),
        "policy": _ref(policy_path), "consumer_manifest": _ref(consumer_manifest),
        "target_build": _ref(target_build),
        "consumer_builds": [_ref(path) for path in consumer_builds],
        "author_decision": _ref(decision_path) if decision_path else None,
        "kenneth_provenance": dict(kenneth_raw),
        "orchestration_provenance": orchestration_provenance,
        "target_subject_id": target_subject.subject_id,
        "target_build_schema": target_build_payload.get("schema"),
        "authority_guard": authority_guard,
    }
    if authority_guard is not None:
        _assert_batch_authority_fresh(**authority_guard, stage="prepare-after-read")
    return build_args, final_path, expected


def _assert_receipt_matches_batch_input(receipt: Mapping[str, Any], expected: Mapping[str, Any]) -> None:
    task_id = str(expected["task_id"])

    def plain_ref(raw: Any) -> dict[str, str] | None:
        if not isinstance(raw, Mapping):
            return None
        return {"path": str(raw.get("path", "") or ""), "sha256": str(raw.get("sha256", "") or "")}

    artifacts = receipt.get("artifacts")
    authority = receipt.get("source_authority")
    provenance = receipt.get("author_provenance")
    if not isinstance(artifacts, Mapping) or not isinstance(authority, Mapping) or not isinstance(provenance, Mapping):
        raise BoundaryDeltaReceiptError(f"{task_id}: receipt evidence is incomplete")
    orchestration = receipt.get("orchestration")
    if not isinstance(orchestration, Mapping) or plain_ref(orchestration.get("input_manifest")) != expected["input_manifest"]:
        raise BoundaryDeltaReceiptError(f"{task_id}: receipt binds another input manifest")
    for key, wanted in expected.get("orchestration_provenance", {}).items():
        if orchestration.get(key) != wanted:
            raise BoundaryDeltaReceiptError(f"{task_id}: receipt orchestration differs at {key}")
    comparisons = (
        (plain_ref(authority.get("artifact")), expected["source_authority"], "source authority"),
        (plain_ref(artifacts.get("source_scope")), expected["source_scope"], "source scope"),
        (plain_ref(artifacts.get("policy")), expected["policy"], "policy"),
        (plain_ref(artifacts.get("consumer_manifest")), expected["consumer_manifest"], "consumer manifest"),
        (plain_ref(artifacts.get("target_build")), expected["target_build"], "target build"),
        (plain_ref(provenance.get("artifact")), expected["author_decision"], "author decision"),
    )
    for actual, wanted, label in comparisons:
        if actual != wanted:
            raise BoundaryDeltaReceiptError(f"{task_id}: receipt binds another {label}")
    raw_consumer_builds = artifacts.get("consumer_builds")
    if not isinstance(raw_consumer_builds, list):
        raise BoundaryDeltaReceiptError(f"{task_id}: receipt consumer builds are malformed")
    actual_consumers = [plain_ref(item) for item in raw_consumer_builds]
    if actual_consumers != expected["consumer_builds"]:
        raise BoundaryDeltaReceiptError(f"{task_id}: receipt binds other consumer builds")
    for key, wanted in expected["kenneth_provenance"].items():
        if provenance.get(key) != wanted:
            raise BoundaryDeltaReceiptError(f"{task_id}: receipt Kenneth provenance differs at {key}")


def _validate_existing_batch_receipt(
    receipt_path: Path, *, build_args: Mapping[str, Any], expected: Mapping[str, Any],
) -> dict[str, Any]:
    receipt, _source, target = validate_verified_boundary_delta(
        receipt_path,
        source_repos=build_args["source_repos"],
        target_repo=build_args["target_repo"],
        kenneth_repo=build_args["kenneth_repo"],
    )
    input_ref = receipt.get("orchestration", {}).get("input_manifest")
    if input_ref != expected["input_manifest"]:
        raise BoundaryDeltaReceiptError(f"{expected['task_id']}: existing receipt binds another input manifest")
    if target.subject_id != expected["target_subject_id"]:
        raise BoundaryDeltaReceiptError(f"{expected['task_id']}: existing receipt target mismatch")
    _assert_receipt_matches_batch_input(receipt, expected)
    return {
        "task_id": expected["task_id"], "status": "skipped_existing",
        "receipt": str(receipt_path), "receipt_sha256": sha256_file(receipt_path),
    }


def emit_verified_boundary_delta_batch(
    *, task_dirs: Sequence[Path], source_repos: Sequence[Path], target_repo: Path,
    kenneth_repo: Path, expected_target_commit: str, expected_kenneth_commit: str,
    skip_existing: bool = True,
    authority_manifest_path: Path | None = None,
    authority_manifest_sha256: str = "",
    workspace_root: Path | None = None,
    exact_build_root: Path | None = None,
) -> dict[str, Any]:
    """Consume pre-existing exact builds and emit independent immutable receipts."""

    tasks: list[dict[str, Any]] = []
    authority_entries: dict[str, tuple[Path, dict[str, Any]]] = {}
    exact_context = None
    snapshot_root: Path | None = None
    authority_snapshot_ref: dict[str, str] | None = None
    authority_snapshot_publication: dict[str, Any] | None = None
    verified_bytes: dict[str, Any] = {}
    if authority_manifest_path is not None:
        if workspace_root is None or exact_build_root is None:
            raise BoundaryDeltaReceiptError(
                "authority batch mode requires explicit workspace_root and exact_build_root"
            )
        parents = {Path(task).resolve().parent for task in task_dirs}
        if len(parents) != 1:
            raise BoundaryDeltaReceiptError("authority batch tasks must share one batch evidence root")
        # Keep the root short enough for Windows while the SHA filename and
        # atomic staging suffix remain fully content-addressed.
        snapshot_root = next(iter(parents)) / "_evidence"
        authority, authority_entries = load_boundary_batch_authority_manifest(
            authority_manifest_path, workspace_root=workspace_root,
            expected_sha256=authority_manifest_sha256,
            expected_target_commit=expected_target_commit,
            expected_kenneth_commit=expected_kenneth_commit,
            verified_bytes=verified_bytes,
        )
        authority_snapshot_ref, authority_snapshot_publication = _ensure_content_addressed_json_snapshot(
            snapshot_root, kind="authority", expected_sha256=authority_manifest_sha256,
            payload=verified_bytes["authority"],
        )
        exact_context = _exact_catalog_context(
            target_repo=target_repo, commit=expected_target_commit,
            task_ids=list(authority["unique_planned_exact_build_tasks"]),
        )
    elif any(value is not None for value in (workspace_root, exact_build_root)) or authority_manifest_sha256:
        raise BoundaryDeltaReceiptError(
            "workspace/exact-build authority options require authority_manifest_path"
        )
    seen: set[Path] = set()
    for raw_dir in task_dirs:
        task_dir = raw_dir.resolve()
        task_id = task_dir.name
        if task_dir in seen:
            tasks.append({"task_id": task_id, "status": "failed", "error": "duplicate task directory"})
            continue
        seen.add(task_dir)
        try:
            input_path = None
            authority_item = None
            if authority_manifest_path is not None:
                entry = authority_entries.get(task_id)
                if entry is None:
                    raise BoundaryDeltaReceiptError(f"{task_id}: task is absent from batch authority")
                input_path, authority_item = entry
                authority_input_ref = dict(authority_item["input_manifest"])
                if input_path.parent != task_dir:
                    raise BoundaryDeltaReceiptError(f"{task_id}: authority input is outside the selected task directory")
                input_snapshot_ref, _input_snapshot_publication = _ensure_content_addressed_json_snapshot(
                    snapshot_root, kind="input",
                    expected_sha256=str(authority_input_ref["sha256"]),
                    payload=verified_bytes["inputs"][task_id],
                )
                original_input_ref = {
                    "path": str(input_path), "sha256": str(authority_input_ref["sha256"]),
                }
            build_args, final_path, expected = _prepare_boundary_batch_task(
                task_dir, source_repos=source_repos, target_repo=target_repo,
                kenneth_repo=kenneth_repo, expected_target_commit=expected_target_commit,
                expected_kenneth_commit=expected_kenneth_commit,
                input_manifest_path=(
                    Path(input_snapshot_ref["path"])
                    if authority_manifest_path is not None else input_path
                ),
                workspace_root=workspace_root,
                exact_build_root=exact_build_root,
                exact_context=exact_context,
                authority_manifest_path=(
                    Path(authority_snapshot_ref["path"])
                    if authority_snapshot_ref is not None else authority_manifest_path
                ),
                authority_manifest_sha256=authority_manifest_sha256,
                authority_item=authority_item,
                authority_input_ref=authority_input_ref if authority_manifest_path is not None else None,
                input_snapshot_ref=input_snapshot_ref if authority_manifest_path is not None else None,
                original_authority_ref=(
                    {"path": str(authority_manifest_path.resolve()), "sha256": authority_manifest_sha256}
                    if authority_manifest_path is not None else None
                ),
                original_input_ref=original_input_ref if authority_manifest_path is not None else None,
            )
            if final_path.exists():
                if not skip_existing:
                    raise BoundaryDeltaReceiptError(f"{task_id}: immutable final receipt already exists")
                existing = _validate_existing_batch_receipt(
                    final_path, build_args=build_args, expected=expected,
                )
                if expected["authority_guard"] is not None:
                    _assert_batch_authority_fresh(
                        **expected["authority_guard"], stage="existing-after-validation",
                    )
                tasks.append(existing)
                continue
            receipt = build_verified_boundary_delta(**build_args)
            if expected["authority_guard"] is not None:
                _assert_batch_authority_fresh(
                    **expected["authority_guard"], stage="build-after",
                )
            if receipt.get("task_id") != expected["task_id"]:
                raise BoundaryDeltaReceiptError(f"{task_id}: builder returned another task")
            _assert_receipt_matches_batch_input(receipt, expected)
            rendered = (json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")
            if expected["authority_guard"] is not None:
                _assert_batch_authority_fresh(
                    **expected["authority_guard"], stage="publish-before",
                )
            publication = _atomic_publish_no_replace(
                final_path, rendered, label=f"{task_id}: receipt",
            )
            tasks.append({
                "task_id": task_id, "status": "emitted", "receipt": str(final_path),
                "receipt_sha256": hashlib.sha256(rendered).hexdigest(),
                "temporary_cleanup": publication["temporary_cleanup"],
            })
        except (BoundaryDeltaReceiptError, OSError, ValueError) as exc:
            tasks.append({"task_id": task_id, "status": "failed", "error": str(exc)})
    emitted = sum(item["status"] == "emitted" for item in tasks)
    skipped = sum(item["status"] == "skipped_existing" for item in tasks)
    failed = sum(item["status"] == "failed" for item in tasks)
    result = {
        "status": "failed" if failed else ("all_existing" if skipped and not emitted else "emitted"),
        "requested": len(task_dirs), "emitted": emitted, "skipped_existing": skipped,
        "failed": failed, "target_commit": expected_target_commit,
        "kenneth_commit": expected_kenneth_commit, "tasks": tasks,
    }
    if authority_snapshot_ref is not None:
        result["content_addressed_snapshots"] = {
            "root": str(snapshot_root.resolve()),
            "authority": authority_snapshot_ref,
            "authority_publication": authority_snapshot_publication,
            "selected_input_count": len({item.get("task_id") for item in tasks}),
        }
    return result
