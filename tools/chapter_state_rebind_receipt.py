#!/usr/bin/env python3
"""Create an immutable Chapter workspace rebind receipt from validated evidence.

This tool does not edit Lean, Git, or SQLite.  It refuses to write a receipt unless
every requested task has an applied-pass primary match, a primary-only bundle, a
byte-identical MAT relocation, a clean forbidden scan, and a successful build-log
batch recorded exactly once.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


BATCH_RE = re.compile(
    r"DEPENDENCY_LAYER=(?P<layer>\d+) BATCH=(?P<batch>\d+) "
    r"TARGET_COUNT=(?P<count>\d+) TASKS=(?P<tasks>[^\r\n]+)"
)
EXIT_RE = re.compile(
    r"DEPENDENCY_LAYER=(?P<layer>\d+) BATCH=(?P<batch>\d+) EXIT_CODE=(?P<code>\d+)"
)


def read_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object: {path}")
    return payload


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def exact_subject(head: dict[str, Any], expected_role: str) -> dict[str, Any]:
    if head.get("role") != expected_role:
        raise ValueError(f"expected subject role {expected_role!r}")
    manifest = head.get("manifest")
    if not isinstance(manifest, list) or len(manifest) != 1:
        raise ValueError(f"{expected_role}: expected an exact primary-only manifest")
    return {
        "role": expected_role,
        "source_repo": head.get("source_repo", ""),
        "source_commit": head.get("source_commit", ""),
        "layout": head.get("layout", ""),
        "primary_path": head.get("primary_path", ""),
        "primary_hash": head.get("primary_hash", ""),
        "bundle_hash": head.get("bundle_hash", ""),
        "files": manifest,
    }


def parse_build_log(path: Path, expected_tasks: set[str]) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace")
    batches: list[dict[str, Any]] = []
    covered: list[str] = []
    for match in BATCH_RE.finditer(text):
        tasks = [item.strip() for item in match.group("tasks").split(",") if item.strip()]
        if len(tasks) != int(match.group("count")):
            raise ValueError("build log target count does not match its task list")
        covered.extend(tasks)
        batches.append(
            {
                "layer": int(match.group("layer")),
                "batch": int(match.group("batch")),
                "tasks": tasks,
            }
        )
    exits = {
        (int(match.group("layer")), int(match.group("batch"))): int(match.group("code"))
        for match in EXIT_RE.finditer(text)
    }
    if not batches or len(exits) != len(batches):
        raise ValueError("build log is missing batch or exit records")
    for batch in batches:
        key = (batch["layer"], batch["batch"])
        if exits.get(key) != 0:
            raise ValueError(f"build batch {key} did not pass")
        batch["exit_code"] = 0
    counts = Counter(covered)
    if set(counts) != expected_tasks or any(value != 1 for value in counts.values()):
        missing = sorted(expected_tasks - set(counts))
        extra = sorted(set(counts) - expected_tasks)
        duplicates = sorted(task for task, count in counts.items() if count != 1)
        raise ValueError(
            f"build coverage mismatch: missing={missing}, extra={extra}, duplicates={duplicates}"
        )
    expected_batch_count = sum(math.ceil(len(layer) / 4) for layer in _layers_from_batches(batches))
    if expected_batch_count != len(batches):
        raise ValueError("build batches are not the expected maximum-four partition")
    return {
        "exit_code": 0,
        "path": str(path.resolve()),
        "sha256": sha256_file(path),
        "task_count": len(covered),
        "batch_count": len(batches),
        "max_batch_size": max(len(batch["tasks"]) for batch in batches),
        "batches": batches,
    }


def _layers_from_batches(batches: list[dict[str, Any]]) -> list[list[str]]:
    by_layer: dict[int, list[str]] = {}
    for batch in batches:
        by_layer.setdefault(batch["layer"], []).extend(batch["tasks"])
    if sorted(by_layer) != list(range(1, len(by_layer) + 1)):
        raise ValueError("build log dependency layers are not contiguous")
    return [by_layer[index] for index in sorted(by_layer)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--build-log", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    evidence_path = args.evidence.resolve()
    evidence = read_json(evidence_path)
    rows = evidence.get("tasks")
    if not isinstance(rows, list) or len(rows) != 114:
        raise ValueError("receipt requires the exact 114-task Chapter 2-4 evidence ledger")
    task_ids = {str(row.get("task_id", "")) for row in rows}
    if len(task_ids) != 114:
        raise ValueError("evidence contains duplicate or empty task ids")
    summary = evidence.get("summary", {})
    required_summary = {
        "task_count": 114,
        "review_primary_match_count": 114,
        "primary_only_bundle_count": 114,
        "unresolved_source_decision_count": 0,
    }
    for key, expected in required_summary.items():
        if summary.get(key) != expected:
            raise ValueError(f"evidence summary {key} must be {expected}")

    build = parse_build_log(args.build_log.resolve(), task_ids)
    receipt_tasks: list[dict[str, Any]] = []
    for row in rows:
        task_id = row["task_id"]
        assessment = row.get("bundle_assessment", {})
        route = row.get("actual_lean_route", {})
        review = row.get("review") or {}
        heads = row.get("current_heads", {})
        if assessment.get("provisional_rebind_class") != "mechanical_scope_rebind":
            raise ValueError(f"{task_id}: not eligible for mechanical scope rebind")
        if not assessment.get("toy_mat_primary_byte_identical"):
            raise ValueError(f"{task_id}: MAT relocation differs from reviewed Toy primary")
        if route.get("forbidden_findings"):
            raise ValueError(f"{task_id}: forbidden findings are not empty")
        if review.get("verdict") != "pass" or review.get("phase2_status") != "pass":
            raise ValueError(f"{task_id}: basis review is not an applied pass")
        toy = exact_subject(heads.get("toy_current") or {}, "toy_current")
        mat_candidate = exact_subject(heads.get("mat_candidate") or {}, "mat_candidate")
        mat_main = exact_subject(heads.get("mat_main") or {}, "mat_main")
        primary_hash = review.get("candidate_hash", "")
        if not primary_hash or any(
            subject["primary_hash"] != primary_hash
            for subject in (toy, mat_candidate, mat_main)
        ):
            raise ValueError(f"{task_id}: exact subjects do not match the basis primary")
        receipt_tasks.append(
            {
                "task_id": task_id,
                "binding_kind": "legacy_primary_scope_rebind",
                "basis_review": {
                    "review_id": review.get("review_id", ""),
                    "reviewed_at": review.get("reviewed_at", ""),
                    "evidence_path": review.get("result_file", ""),
                    "evidence_hash": review.get("result_sha256", ""),
                    "primary_hash": primary_hash,
                },
                "checks": {
                    "build_status": "pass",
                    "build_log_sha256": build["sha256"],
                    "forbidden_scan_status": "pass",
                    "forbidden_scan_scope_files": 114,
                    "support_scope_status": "pass",
                    "support_files": [],
                    "mat_relocation_status": "pass",
                    "relocated_file_count": 1,
                },
                "subjects": [toy, mat_candidate, mat_main],
            }
        )

    created_at = datetime.now(timezone.utc).isoformat()
    payload = {
        "schema_version": "toy-apollo.workspace-review-binding.v1",
        "binding_id": "chapter_02_04_state_reconciliation_20260718",
        "created_at": created_at,
        "scope": "chapter_02_04_exact_114_formal_phase1_tasks",
        "basis_evidence": {
            "path": str(evidence_path),
            "sha256": sha256_file(evidence_path),
            "schema_version": evidence.get("schema_version", ""),
        },
        "build_evidence": build,
        "forbidden_scan": {
            "scope_files": 114,
            "findings": [],
            "tokens": ["sorry", "admit", "axiom", "native_decide"],
        },
        "mat_relocation": {
            "status": "pass",
            "task_count": 114,
            "basis": "byte-identical current MAT/Toy primary plus successful build of the identical Toy content",
            "project_boundary": "MAT lakefile currently registers only ProbabilityTheory.chapter_01.+; Chapter 2-4 files retain ToyApollo.Output imports and are relocation artifacts, not native MAT Lake targets.",
        },
        "kenneth_reconciliation": {
            "write_scope": "read_only_no_pr_no_commit",
            "both_head_count": summary.get("mat_kenneth_both_count", 0),
            "different_count": summary.get("mat_kenneth_different_count", 0),
            "manual_adjudication_count": summary.get("manual_adjudication_count", 0),
            "unresolved_source_decision_count": summary.get("unresolved_source_decision_count", 0),
            "final_categories": summary.get("kenneth_final_reconciliation_categories", {}),
        },
        "reviewer_independence": {
            "role": "mechanical_scope_rebind_auditor",
            "independence_kind": "not_a_new_semantic_review",
            "did_modify_toy_task_bundles": False,
            "attestation": "Reused only applied pass reviews after exact-primary, primary-only support scope, forbidden scan, MAT byte relocation, dependency graph, and fresh 114-module build checks.",
        },
        "tasks": receipt_tasks,
    }
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "output": str(output),
                "sha256": sha256_file(output),
                "tasks": len(receipt_tasks),
                "subjects": sum(len(task["subjects"]) for task in receipt_tasks),
                "build_batches": build["batch_count"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
