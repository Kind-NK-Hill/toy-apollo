#!/usr/bin/env python3
"""Offline review-basis diagnostics and an explicit-manifest identity experiment.

No state database, ledger, prompt pack, model, or canonical Lean file is written.
Only --output writes a report at the path explicitly supplied by the caller.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from formalization_engine.review_basis_diagnostics import (  # noqa: E402
    compare_review_bases,
    frozen_target_pilot_fingerprints,
)


def run_identity_pilot() -> dict:
    baseline = {
        "target": {
            "declaration": "theorem eligible_self (n : Nat) (h : Eligible n) : Eligible n",
            "definition_dependencies": {"Eligible": "def Eligible (n : Nat) : Prop := 0 < n"},
            "toolchain": {"lean": "leanprover/lean4:v4.19.0", "imports": []},
        },
        "proof": "by exact h",
        "review_evidence": {"rubric": "fixture-v1", "observations": []},
        "runtime_mirrors": {"status": "awaiting_review", "report": "run-1.json"},
    }
    before = frozen_target_pilot_fingerprints(baseline)
    mutations = [
        ("unchanged", (), None, []),
        ("runtime_status", ("runtime_mirrors", "status"), "review_requested", ["runtime_mirrors"]),
        ("proof_only", ("proof",), "by assumption", ["proof_version"]),
        ("declaration", ("target", "declaration"),
         "theorem eligible_pair (n : Nat) (h : Eligible n) : Eligible n ∧ Eligible n", ["target_identity"]),
        ("definition_dependency", ("target", "definition_dependencies", "Eligible"),
         "def Eligible (n : Nat) : Prop := 1 < n", ["target_identity"]),
        ("toolchain", ("target", "toolchain", "lean"), "leanprover/lean4:v4.20.0", ["target_identity"]),
        ("review_evidence", ("review_evidence", "observations"), ["check assumptions"], ["review_evidence"]),
    ]
    rows = []
    for name, path, value, expected in mutations:
        current = deepcopy(baseline)
        if path:
            node = current
            for component in path[:-1]:
                node = node[component]
            node[path[-1]] = value
        after = frozen_target_pilot_fingerprints(current)
        changed = [key for key in before if before[key] != after[key]]
        rows.append({"scenario": name, "changed_identities": changed,
                     "expected": expected, "check_passed": changed == expected,
                     "fingerprints": after})
    return {
        "schema_version": "phase2.frozen_target.identity_pilot.v1",
        "experiment_kind": "synthetic_manifest_identity_check",
        "baseline": baseline,
        "baseline_fingerprints": before,
        "scenarios": rows,
        "all_checks_passed": all(row["check_passed"] for row in rows),
        "authority_effect": "none",
        "limitations": [
            "The target/dependency manifest is explicit, not extracted from Lean.",
            "Declaration edits are identity probes, not new proved theorems.",
            "No semantic accuracy, model cost, performance, or historical churn improvement is measured.",
            "No review may be reused on this basis; production exact-hash checks remain unchanged.",
        ],
    }


def _read_basis(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected a JSON object")
    basis = payload.get("review_basis", payload)
    if not isinstance(basis, dict):
        raise ValueError(f"{path}: review_basis must be an object")
    return basis


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, help="Saved basis or semantic_review_input JSON")
    parser.add_argument("--after", type=Path, help="Second saved basis or semantic_review_input JSON")
    parser.add_argument("--output", type=Path, help="Optional explicit report output (otherwise stdout)")
    args = parser.parse_args()
    if bool(args.before) != bool(args.after):
        parser.error("--before and --after must be provided together")
    try:
        report = compare_review_bases(_read_basis(args.before), _read_basis(args.after)) if args.before else run_identity_pilot()
    except (OSError, ValueError) as error:
        parser.error(str(error))
    rendered = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0 if report.get("all_checks_passed", True) else 1


if __name__ == "__main__":
    raise SystemExit(main())
