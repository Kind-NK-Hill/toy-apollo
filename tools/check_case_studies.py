from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Mapping


HEX64 = re.compile(r"[0-9a-f]{64}")
MINIMUM_CASES = 7
MAXIMUM_CASES = 10
MINIMUM_DISTINCT_PRIMARY_FAILURE_MODES = 6
MINIMUM_STATEMENT_DRIFT_CASES = 5
REQUIRED_CASE_FILES = {
    "README.md",
    "initial.lean",
    "final.lean",
    "review-timeline.json",
}
FORBIDDEN_PUBLIC_MARKERS = (
    "TASK CONTENT:",
    "\\begin{defbox}",
    "\\begin{thmbox}",
    "SOURCE PLAN:",
    "C:\\Users\\",
    "D:\\Grad",
    "Grad_Study",
)


def _is_hex64(value: Any) -> bool:
    return isinstance(value, str) and HEX64.fullmatch(value) is not None


def validate_timeline(payload: Mapping[str, Any], *, case_id: str) -> list[str]:
    errors: list[str] = []
    if payload.get("schema_version") != 1:
        errors.append(f"{case_id}: timeline schema_version must be 1")
    if payload.get("case_id") != case_id:
        errors.append(f"{case_id}: timeline case_id mismatch")

    modes = payload.get("failure_modes")
    if not isinstance(modes, list) or not modes or not all(
        isinstance(item, str) and item for item in modes
    ):
        errors.append(f"{case_id}: failure_modes must be a non-empty string list")
    if not isinstance(payload.get("statement_drift"), bool):
        errors.append(f"{case_id}: statement_drift must be boolean")

    curation = payload.get("curation")
    if not isinstance(curation, Mapping):
        errors.append(f"{case_id}: curation must be an object")
    else:
        if curation.get("full_pack_tracked_publicly") is not False:
            errors.append(f"{case_id}: full private pack must not be public")
        if not curation.get("snapshot_kind"):
            errors.append(f"{case_id}: snapshot_kind is required")

    reviews = payload.get("reviews")
    if not isinstance(reviews, list) or not reviews:
        errors.append(f"{case_id}: reviews must be a non-empty list")
        reviews = []

    counts = payload.get("counts")
    if not isinstance(counts, Mapping):
        errors.append(f"{case_id}: counts must be an object")
    else:
        expected = {
            "semantic_review_results": len(reviews),
            "review_failures": sum(
                isinstance(review, Mapping) and review.get("verdict") == "fail"
                for review in reviews
            ),
            "review_passes": sum(
                isinstance(review, Mapping) and review.get("verdict") == "pass"
                for review in reviews
            ),
        }
        for key, value in expected.items():
            if counts.get(key) != value:
                errors.append(f"{case_id}: counts.{key} must equal {value}")

    for index, review in enumerate(reviews, start=1):
        if not isinstance(review, Mapping):
            errors.append(f"{case_id}: review {index} must be an object")
            continue
        if review.get("round") != index:
            errors.append(f"{case_id}: review rounds must be contiguous from 1")
        if review.get("verdict") not in {"pass", "fail", "inconclusive"}:
            errors.append(f"{case_id}: review {index} has invalid verdict")
        for field in ("candidate_hash", "private_review_sha256"):
            if not _is_hex64(review.get(field)):
                errors.append(f"{case_id}: review {index} has invalid {field}")
        if not review.get("finding"):
            errors.append(f"{case_id}: review {index} needs a finding")

    evidence = payload.get("private_evidence_sha256")
    if not isinstance(evidence, Mapping) or not evidence:
        errors.append(f"{case_id}: private_evidence_sha256 must be non-empty")
    else:
        for name, digest in evidence.items():
            if not isinstance(name, str) or not _is_hex64(digest):
                errors.append(f"{case_id}: invalid private evidence hash for {name}")
    return errors


def validate_case_studies(case_root: Path) -> list[str]:
    errors: list[str] = []
    catalog_path = case_root / "cases.json"
    try:
        catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"cannot read case catalog: {exc}"]
    if not isinstance(catalog, Mapping):
        return ["cases.json: root must be an object"]

    if catalog.get("schema_version") != 1:
        errors.append("cases.json: schema_version must be 1")

    policy = catalog.get("selection_policy", {})
    if not isinstance(policy, Mapping):
        return errors + ["cases.json: selection_policy must be an object"]
    required_policy = {
        "minimum_cases": MINIMUM_CASES,
        "maximum_cases": MAXIMUM_CASES,
        "minimum_distinct_primary_failure_modes": (
            MINIMUM_DISTINCT_PRIMARY_FAILURE_MODES
        ),
        "minimum_statement_drift_cases": MINIMUM_STATEMENT_DRIFT_CASES,
        "full_private_packs_public": False,
    }
    for field, required_value in required_policy.items():
        if policy.get(field) != required_value:
            errors.append(
                f"cases.json: selection_policy.{field} must be {required_value!r}"
            )

    catalog_cases = catalog.get("cases")
    if not isinstance(catalog_cases, list):
        return ["cases.json: cases must be a list"]

    case_ids = [
        item["case_id"]
        for item in catalog_cases
        if isinstance(item, Mapping) and isinstance(item.get("case_id"), str)
    ]
    if len(case_ids) != len(set(case_ids)):
        errors.append("cases.json: case_id values must be unique")
    if not MINIMUM_CASES <= len(case_ids) <= MAXIMUM_CASES:
        errors.append(
            "cases.json: expected "
            f"{MINIMUM_CASES}..{MAXIMUM_CASES} cases, found {len(case_ids)}"
        )

    actual_dirs = sorted(path.name for path in case_root.iterdir() if path.is_dir())
    if sorted(case_ids) != actual_dirs:
        errors.append("cases.json: catalog case IDs do not match case directories")

    primary_modes: set[str] = set()
    statement_drift_count = 0
    for item in catalog_cases:
        if not isinstance(item, Mapping):
            errors.append("cases.json: every case entry must be an object")
            continue
        case_id = item.get("case_id")
        if not isinstance(case_id, str) or not case_id:
            errors.append("cases.json: every case needs a case_id")
            continue
        mode = item.get("primary_failure_mode")
        if isinstance(mode, str) and mode:
            primary_modes.add(mode)
        else:
            errors.append(f"{case_id}: primary_failure_mode is required")
        if not isinstance(item.get("statement_drift"), bool):
            errors.append(f"{case_id}: statement_drift must be boolean")
        elif item.get("statement_drift") is True:
            statement_drift_count += 1
        if not item.get("interview_hook"):
            errors.append(f"{case_id}: interview_hook is required")

        case_dir = case_root / case_id
        missing = sorted(
            name for name in REQUIRED_CASE_FILES if not (case_dir / name).is_file()
        )
        if missing:
            errors.append(f"{case_id}: missing files {', '.join(missing)}")
            continue

        try:
            timeline = json.loads(
                (case_dir / "review-timeline.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"{case_id}: cannot read timeline: {exc}")
            continue
        if not isinstance(timeline, Mapping):
            errors.append(f"{case_id}: timeline root must be an object")
            continue
        errors.extend(validate_timeline(timeline, case_id=case_id))
        if timeline.get("statement_drift") != item.get("statement_drift"):
            errors.append(f"{case_id}: catalog/timeline statement_drift mismatch")
        timeline_modes = timeline.get("failure_modes")
        if not isinstance(timeline_modes, list) or mode not in timeline_modes:
            errors.append(f"{case_id}: primary failure mode is absent from timeline")

        for name in REQUIRED_CASE_FILES:
            text = (case_dir / name).read_text(encoding="utf-8")
            for marker in FORBIDDEN_PUBLIC_MARKERS:
                if marker in text:
                    errors.append(f"{case_id}/{name}: forbidden public marker {marker!r}")

        for snapshot_name in ("initial.lean", "final.lean"):
            snapshot = (case_dir / snapshot_name).read_text(encoding="utf-8")
            if re.search(r"\b(?:sorry|admit)\b", snapshot):
                errors.append(f"{case_id}/{snapshot_name}: proof placeholder is forbidden")
        if (case_dir / "initial.lean").read_bytes() == (
            case_dir / "final.lean"
        ).read_bytes():
            errors.append(f"{case_id}: initial and final snapshots must differ")

    if len(primary_modes) < MINIMUM_DISTINCT_PRIMARY_FAILURE_MODES:
        errors.append(
            "cases.json: expected at least "
            f"{MINIMUM_DISTINCT_PRIMARY_FAILURE_MODES} distinct primary failure modes"
        )
    if statement_drift_count < MINIMUM_STATEMENT_DRIFT_CASES:
        errors.append(
            "cases.json: expected at least "
            f"{MINIMUM_STATEMENT_DRIFT_CASES} statement-drift cases"
        )
    return errors


def main() -> int:
    root = Path(__file__).resolve().parents[1] / "examples" / "case-studies"
    errors = validate_case_studies(root)
    if errors:
        print("Case-study check failed:")
        for error in errors:
            print(f" - {error}")
        return 1
    print("Case-study check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
