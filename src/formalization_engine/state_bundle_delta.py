from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from typing import Any, Iterable, Mapping

from .state_store import WorkspaceStateStore


@dataclass(frozen=True)
class BundleComparison:
    classification: str
    reviewed_file_count: int
    current_file_count: int
    primary_equal: bool
    content_multiset_equal: bool

    def as_dict(self) -> dict[str, Any]:
        return {
            "classification": self.classification,
            "reviewed_file_count": self.reviewed_file_count,
            "current_file_count": self.current_file_count,
            "primary_equal": self.primary_equal,
            "content_multiset_equal": self.content_multiset_equal,
        }


def _manifest(raw: Any) -> list[dict[str, Any]]:
    if isinstance(raw, str):
        try:
            raw = json.loads(raw)
        except json.JSONDecodeError:
            return []
    if not isinstance(raw, list):
        return []
    return [dict(item) for item in raw if isinstance(item, Mapping)]


def _content_identity(item: Mapping[str, Any]) -> str:
    content = str(item.get("content_sha256", "") or "")
    if content:
        return f"sha256:{content}"
    git_blob = str(item.get("git_blob_sha", "") or "")
    if git_blob:
        return f"git:{git_blob}"
    return f"unknown-size:{int(item.get('size', 0) or 0)}"


def compare_bundles(
    reviewed: Mapping[str, Any],
    current: Mapping[str, Any],
) -> BundleComparison:
    reviewed_manifest = _manifest(reviewed.get("manifest_json", reviewed.get("files", [])))
    current_manifest = _manifest(current.get("manifest_json", current.get("files", [])))
    primary_equal = bool(reviewed.get("primary_hash")) and (
        str(reviewed.get("primary_hash")) == str(current.get("primary_hash"))
    )
    content_equal = Counter(map(_content_identity, reviewed_manifest)) == Counter(
        map(_content_identity, current_manifest)
    )
    if (
        str(reviewed.get("bundle_hash", ""))
        and str(reviewed.get("bundle_hash", "")) == str(current.get("bundle_hash", ""))
    ):
        classification = "exact_bundle"
    elif primary_equal and content_equal:
        classification = "path_only_relocation"
    elif primary_equal and len(reviewed_manifest) == 1 and len(current_manifest) > 1:
        classification = "support_scope_unbound"
    elif primary_equal:
        classification = "support_delta"
    else:
        classification = "primary_delta"
    return BundleComparison(
        classification=classification,
        reviewed_file_count=len(reviewed_manifest),
        current_file_count=len(current_manifest),
        primary_equal=primary_equal,
        content_multiset_equal=content_equal,
    )


def _compatible_reviews(connection, task_id: str) -> list[dict[str, Any]]:
    rows = connection.execute(
        """
        SELECT r.review_id, r.subject_id, r.reviewed_at, r.evidence_path,
               r.evidence_hash, r.authority_scope, r.authority_eligible,
               m.prompt_version, m.rubric_version,
               s.bundle_hash, s.primary_hash, s.primary_path, s.manifest_json
        FROM reviews r
        JOIN review_metadata m ON m.review_id = r.review_id
        JOIN subjects s ON s.subject_id = r.subject_id
        WHERE r.task_id = ?
          AND lower(r.verdict) = 'pass' AND lower(r.phase2_status) = 'pass'
          AND m.prompt_version IN (9, 10, 11) AND m.rubric_version = 9
        ORDER BY r.authority_eligible DESC, r.reviewed_at DESC, r.review_id
        """,
        (task_id,),
    ).fetchall()
    return [dict(row) for row in rows]


def _validated_transformation(
    connection,
    *,
    review_subject_id: str,
    current: Mapping[str, Any],
) -> dict[str, Any] | None:
    row = connection.execute(
        """
        SELECT t.transformation_id, t.transformation_kind,
               t.mechanical_status, t.build_status, t.evidence_path,
               t.evidence_hash
        FROM transformations t
        JOIN subjects target ON target.subject_id = t.target_subject_id
        WHERE t.source_subject_id = ?
          AND target.task_id = ? AND target.bundle_hash = ?
          AND t.mechanical_status = 'pass'
          AND t.build_status IN ('pass', 'not_required')
        ORDER BY t.created_at DESC, t.transformation_id
        LIMIT 1
        """,
        (
            review_subject_id,
            str(current["task_id"]),
            str(current["bundle_hash"]),
        ),
    ).fetchone()
    return dict(row) if row is not None else None


def _typed_evidence_bridge(connection, current: Mapping[str, Any]) -> dict[str, Any] | None:
    present = connection.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='authority_bindings'"
    ).fetchone()
    if present is None:
        return None
    row = connection.execute(
        """
        SELECT b.binding_id, b.bridge_route, b.authority_type, b.capability,
               b.decision_path, b.decision_hash, b.evidence_path, b.evidence_hash,
               t.transformation_id, t.transformation_kind,
               t.mechanical_status, t.build_status
        FROM valid_authority_bindings_v2 b
        JOIN transformations t ON t.transformation_id = b.transformation_id
        JOIN subjects target ON target.subject_id = b.target_subject_id
        WHERE b.target_subject_id = ?
          AND target.task_id = ? AND target.bundle_hash = ?
        ORDER BY b.created_at DESC, b.binding_id
        LIMIT 1
        """,
        (str(current["subject_id"]), str(current["task_id"]), str(current["bundle_hash"])),
    ).fetchone()
    return dict(row) if row is not None else None


def analyze_current_mat_bundles(
    store: WorkspaceStateStore,
    *,
    task_ids: Iterable[str] | None = None,
) -> dict[str, Any]:
    """Classify review-to-current-MAT deltas without granting new authority."""

    requested = sorted(set(task_ids or []))
    store.assert_integrity()
    with store._connection(write=False) as connection:
        parameters: list[Any] = []
        predicate = ""
        if requested:
            predicate = " AND h.task_id IN (" + ",".join("?" for _ in requested) + ")"
            parameters.extend(requested)
        current_rows = connection.execute(
            """
            SELECT h.task_id, h.subject_id, h.freshness,
                   s.bundle_hash, s.primary_hash, s.primary_path, s.manifest_json
            FROM task_heads h
            JOIN subjects s ON s.subject_id = h.subject_id
            WHERE h.role = 'mat_main' AND h.freshness IN ('fresh', 'local')
            """
            + predicate
            + " ORDER BY h.task_id",
            parameters,
        ).fetchall()
        results: list[dict[str, Any]] = []
        for current_row in current_rows:
            current = dict(current_row)
            reviews = _compatible_reviews(connection, str(current["task_id"]))
            authority_reviews = [row for row in reviews if int(row["authority_eligible"]) == 1]
            typed_bridge = _typed_evidence_bridge(connection, current)
            if not authority_reviews:
                if typed_bridge is not None:
                    results.append(
                        {
                            "task_id": current["task_id"],
                            "current_subject_id": current["subject_id"],
                            "current_bundle_hash": current["bundle_hash"],
                            "status": "validated_evidence_bridge",
                            "authority_coverage": typed_bridge,
                            "compatible_pass_count": len(reviews),
                        }
                    )
                    continue
                status = "compatible_pass_not_authority" if reviews else "no_compatible_pass"
                results.append(
                    {
                        "task_id": current["task_id"],
                        "current_subject_id": current["subject_id"],
                        "current_bundle_hash": current["bundle_hash"],
                        "status": status,
                        "compatible_pass_count": len(reviews),
                    }
                )
                continue

            ranked: list[tuple[int, str, dict[str, Any], BundleComparison]] = []
            priority = {
                "exact_bundle": 0,
                "path_only_relocation": 1,
                "support_scope_unbound": 2,
                "support_delta": 3,
                "primary_delta": 4,
            }
            for review in authority_reviews:
                comparison = compare_bundles(review, current)
                ranked.append(
                    (
                        priority[comparison.classification],
                        str(review.get("reviewed_at", "")),
                        review,
                        comparison,
                    )
                )
            best_rank = min(item[0] for item in ranked)
            _rank, _time, review, comparison = max(
                (item for item in ranked if item[0] == best_rank),
                key=lambda item: (item[1], str(item[2].get("review_id", ""))),
            )
            transformation = _validated_transformation(
                connection,
                review_subject_id=str(review["subject_id"]),
                current=current,
            )
            if comparison.classification == "exact_bundle":
                status = "exact_current_compatible_authority"
            elif typed_bridge is not None:
                status = "validated_evidence_bridge"
            elif transformation is not None:
                status = "validated_rebind"
            elif comparison.classification == "path_only_relocation":
                status = "mechanical_rebind_required"
            elif comparison.classification == "support_scope_unbound":
                status = "support_scope_rebind_required"
            elif comparison.classification == "support_delta":
                status = "support_delta_review_required"
            else:
                status = "fresh_review_required"
            results.append(
                {
                    "task_id": current["task_id"],
                    "current_subject_id": current["subject_id"],
                    "current_bundle_hash": current["bundle_hash"],
                    "status": status,
                    "basis_review_id": review["review_id"],
                    "basis_subject_id": review["subject_id"],
                    "basis_evidence_path": review["evidence_path"],
                    "prompt_version": review["prompt_version"],
                    "rubric_version": review["rubric_version"],
                    "comparison": comparison.as_dict(),
                    "transformation": transformation or {},
                    "authority_coverage": typed_bridge or {},
                    "compatible_pass_count": len(reviews),
                }
            )
    distribution = Counter(str(row["status"]) for row in results)
    return {
        "schema_version": "toy-apollo.current-mat-review-delta.v1",
        "task_count": len(results),
        "status_counts": dict(sorted(distribution.items())),
        "tasks": results,
    }
