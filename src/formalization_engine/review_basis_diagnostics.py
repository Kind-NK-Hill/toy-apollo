"""Read-only explanations of review freshness, never an acceptance policy.

The original basis remains the authority input. Every JSON leaf, including
unknown fields and empty containers, contributes to exactly one diagnostic
dimension. A whole Lean file hash is a subject/dependency *bundle* identity;
it cannot establish a frozen theorem signature or distinguish proof-only edits.
"""
from __future__ import annotations

from typing import Any

from .phase2_pack_shared.io import sha256_json


DIMENSIONS = (
    "target_context", "subject_bundle", "dependency_bundle", "environment",
    "review_evidence", "runtime_mirrors", "unclassified",
)
_TARGET_FIELDS = {
    "review_profile", "output_owner_task_id", "output_module",
    "official_task_declarations", "source_evidence",
}
_REVIEW_FIELDS = {
    "required_evidence_classes", "direct_downstream_consumers",
    "route_inspection_gate", "spine_review_contract", "audit_evidence",
    "classification_history", "downstream_evidence", "allowed_abstractions",
    "forbidden_weakenings", "historical_shortcut_risks", "downstream_acceptance_checklist",
}


def _leaves(
    value: Any,
    path: tuple[str, ...] = (),
    container_types: tuple[str, ...] = (),
) -> dict[tuple[str, ...], Any]:
    if isinstance(value, dict) and value:
        return {key: leaf for name, item in value.items()
                for key, leaf in _leaves(item, (*path, str(name)), (*container_types, "object")).items()}
    if isinstance(value, list) and value:
        return {key: leaf for index, item in enumerate(value)
                for key, leaf in _leaves(item, (*path, str(index)), (*container_types, "array")).items()}
    # Keep ancestor types so {"0": 1} and [1] cannot alias at the same pointer.
    return {path: {"container_types": container_types, "value": value}}


def _pointer(path: tuple[str, ...]) -> str:
    return "/" + "/".join(part.replace("~", "~0").replace("/", "~1") for part in path)


def _dimension(path: tuple[str, ...]) -> str:
    if not path:
        return "unclassified"
    root, leaf = path[0], path[-1]
    if root == "task":
        return "runtime_mirrors" if leaf == "soft_imports_confirmed_at" else "target_context"
    if root in _TARGET_FIELDS:
        return "runtime_mirrors" if leaf == "tex_file" else "target_context"
    if root == "runtime_environment_evidence":
        return "environment"
    if root == "dependency_status":
        return "runtime_mirrors" if leaf in {"ledger_status", "official_output_file", "source_plan"} else "dependency_bundle"
    if root in {"review_subject_kind", "review_subject_hash", "lean_subject_evidence", "subject_imports"}:
        return "subject_bundle"
    if root == "hash_evidence":
        if leaf.endswith("_file"):
            return "runtime_mirrors"
        return "review_evidence" if leaf == "build_result_hash" else "subject_bundle"
    if root in {"ledger_status", "official_output_targets"}:
        return "runtime_mirrors"
    if root in _REVIEW_FIELDS:
        return "review_evidence"
    return "unclassified"


def review_basis_fingerprints(basis: dict[str, Any]) -> dict[str, Any]:
    """Derive diagnostics without mutating or normalizing the authority basis."""
    groups: dict[str, dict[str, Any]] = {name: {} for name in DIMENSIONS}
    for path, value in _leaves(basis).items():
        groups[_dimension(path)][_pointer(path)] = value
    return {
        "schema_version": "phase2.review_basis.diagnostics.v1",
        "authority_basis_hash": sha256_json(basis),
        "fingerprints": {name: sha256_json(items) for name, items in groups.items()},
        "field_counts": {name: len(items) for name, items in groups.items()},
        "authority_effect": "none",
        "target_context_is_frozen_goal": False,
    }


def compare_review_bases(recorded: dict[str, Any], current: dict[str, Any]) -> dict[str, Any]:
    """Explain exact differences, exposing paths and hashes rather than values."""
    before, after = review_basis_fingerprints(recorded), review_basis_fingerprints(current)
    old, new = _leaves(recorded), _leaves(current)
    changed_paths = [path for path in sorted(old.keys() | new.keys())
                     if path not in old or path not in new or sha256_json(old[path]) != sha256_json(new[path])]
    return {
        "schema_version": "phase2.review_basis.comparison.v1",
        "recorded": before,
        "current": after,
        "changed_dimensions": [name for name in DIMENSIONS
                               if before["fingerprints"][name] != after["fingerprints"][name]],
        "changes": [{"path": _pointer(path), "dimension": _dimension(path),
                     "kind": "added" if path not in old else "removed" if path not in new else "changed"}
                    for path in changed_paths],
        "exact_basis_changed": before["authority_basis_hash"] != after["authority_basis_hash"],
        "authority_effect": "none; existing freshness and retirement rules remain authoritative",
    }


def frozen_target_pilot_fingerprints(snapshot: dict[str, Any]) -> dict[str, str]:
    """Hash an explicit fixture manifest; this is not a Lean signature extractor.

    Targets must include their declaration, definition dependency closure and
    toolchain. No fixture fingerprint is consumed by review-apply or the cache.
    """
    required = {"target", "proof", "review_evidence", "runtime_mirrors"}
    if set(snapshot) != required:
        raise ValueError(f"pilot snapshot must contain exactly {sorted(required)}")
    target = snapshot["target"]
    if not isinstance(target, dict) or set(target) != {"declaration", "definition_dependencies", "toolchain"}:
        raise ValueError("pilot target requires declaration, definition_dependencies, and toolchain")
    if not isinstance(target["declaration"], str) or not target["declaration"].strip():
        raise ValueError("pilot declaration must be nonempty")
    if not isinstance(target["definition_dependencies"], dict) or not target["toolchain"]:
        raise ValueError("pilot target requires an explicit dependency map and toolchain")
    return {"target_identity": sha256_json(target),
            "proof_version": sha256_json(snapshot["proof"]),
            "review_evidence": sha256_json(snapshot["review_evidence"]),
            "runtime_mirrors": sha256_json(snapshot["runtime_mirrors"])}
