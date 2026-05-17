from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id

from .phase2_proof_obligations import (
    validate_obligation_review_for_pass,
    validate_obligation_review_shape,
)


SEMANTIC_REVIEW_PROMPT_VERSION = 5
SEMANTIC_REVIEW_RUBRIC_VERSION = 5
SEMANTIC_REVIEW_REQUIRED_FIELDS = {
    "verdict",
    "confidence",
    "summary",
    "source_claims",
    "claim_mapping",
    "spine_alignment",
    "obligation_review",
    "interface_contract",
    "downstream_adequacy",
    "forbidden_weakenings",
    "findings",
    "recommended_disposition",
}
SEMANTIC_REVIEW_RESULT_PREFIX = "semantic_review_result"
SEMANTIC_REVIEW_INPUT_PREFIX = "semantic_review_input"
SEMANTIC_REVIEW_PROMPT_PREFIX = "semantic_review_prompt"
SEMANTIC_REVIEW_CONTEXT_PREFIX = "semantic_review_context"
SEMANTIC_REVIEW_REPORT_PREFIX = "semantic_review_report"
MAX_CAPTURE_CHARS = 12000


@dataclass(frozen=True)
class SemanticReviewerConfig:
    argv_template: list[str]
    backend_id: str
    timeout_seconds: int

    @property
    def argv_hash(self) -> str:
        return _hash_text(json.dumps(self.argv_template, ensure_ascii=False, sort_keys=True))


def utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def _hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _hash_json(payload: Any) -> str:
    return _hash_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))


def load_reviewer_config_from_env() -> SemanticReviewerConfig | None:
    raw_argv = os.getenv("TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON", "").strip()
    if not raw_argv:
        return None
    try:
        parsed = json.loads(raw_argv)
    except json.JSONDecodeError as exc:
        raise ValueError(f"TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON is not valid JSON: {exc}") from exc
    if not isinstance(parsed, list) or not parsed or not all(isinstance(item, str) and item for item in parsed):
        raise ValueError("TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON must be a non-empty JSON array of strings.")
    raw_timeout = os.getenv("TOY_APOLLO_PHASE2_REVIEWER_TIMEOUT_SECONDS", "").strip()
    timeout = 300
    if raw_timeout:
        try:
            timeout = int(raw_timeout)
        except ValueError as exc:
            raise ValueError("TOY_APOLLO_PHASE2_REVIEWER_TIMEOUT_SECONDS must be an integer.") from exc
    if timeout <= 0:
        raise ValueError("TOY_APOLLO_PHASE2_REVIEWER_TIMEOUT_SECONDS must be positive.")
    return SemanticReviewerConfig(
        argv_template=parsed,
        backend_id=os.getenv("TOY_APOLLO_PHASE2_REVIEWER_BACKEND_ID", "local-reviewer").strip() or "local-reviewer",
        timeout_seconds=timeout,
    )


def next_semantic_review_artifact_paths(pack_dir: Path, attempt: int) -> dict[str, Path]:
    return {
        "input": pack_dir / f"{SEMANTIC_REVIEW_INPUT_PREFIX}_v{attempt}.json",
        "prompt": pack_dir / f"{SEMANTIC_REVIEW_PROMPT_PREFIX}_v{attempt}.md",
        "result": pack_dir / f"{SEMANTIC_REVIEW_RESULT_PREFIX}_v{attempt}.json",
        "report": pack_dir / f"{SEMANTIC_REVIEW_REPORT_PREFIX}_v{attempt}.md",
    }


def latest_semantic_review_artifact_paths(pack_dir: Path) -> dict[str, Path]:
    return {
        "input": pack_dir / f"{SEMANTIC_REVIEW_INPUT_PREFIX}.json",
        "prompt": pack_dir / f"{SEMANTIC_REVIEW_PROMPT_PREFIX}.md",
        "result": pack_dir / f"{SEMANTIC_REVIEW_RESULT_PREFIX}.json",
        "report": pack_dir / f"{SEMANTIC_REVIEW_REPORT_PREFIX}.md",
    }


def next_semantic_review_context_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{SEMANTIC_REVIEW_CONTEXT_PREFIX}_v{attempt}.md"


def latest_semantic_review_context_path(pack_dir: Path) -> Path:
    return pack_dir / f"{SEMANTIC_REVIEW_CONTEXT_PREFIX}.md"


def build_semantic_review_input(
    *,
    task: dict[str, Any],
    mode: str,
    attempt: int,
    candidate_path: Path,
    candidate_code: str,
    import_lines: list[str],
    dependency_summary: list[dict[str, Any]],
    search_summary: dict[str, Any],
    build_summary: dict[str, Any],
    backend_id: str,
    reviewer_argv_hash: str,
    review_subject_kind: str = "candidate",
    build_result_file: str = "",
    build_candidate_file: str = "",
    build_candidate_hash: str = "",
    sanity_build_module: str = "",
    sanity_build_passed: bool = False,
    review_context_file: str = "",
    review_context_hash: str = "",
    review_context_markdown: str = "",
    review_basis: dict[str, Any] | None = None,
    review_basis_hash: str = "",
) -> dict[str, Any]:
    task_payload = {
        "block_id": task.get("block_id", ""),
        "type": task.get("type", ""),
        "title": task.get("title", ""),
        "content": task.get("content", ""),
        "source_plan": task.get("source_plan", ""),
        "dependencies": task.get("dependencies", []),
        "soft_imports": task.get("soft_imports", []),
    }
    dependency_summary_hash = _hash_json(dependency_summary)
    task_source_hash = _hash_json(task_payload)
    candidate_hash = _hash_text(candidate_code)
    if not isinstance(review_basis, dict):
        review_basis = {}
    build_precondition = {
        "kind": "candidate_build_ready" if review_subject_kind == "candidate" else "official_output_sanity",
        "build_result_file": build_result_file,
        "build_candidate_file": build_candidate_file,
        "build_candidate_hash": build_candidate_hash,
        "sanity_build_module": sanity_build_module,
        "sanity_build_passed": bool(sanity_build_passed),
    }
    resolved_review_basis_hash = review_basis_hash or (_hash_json(review_basis) if review_basis else "")
    cache_basis = {
        "task_source_hash": task_source_hash,
        "candidate_hash": candidate_hash,
        "dependency_summary_hash": dependency_summary_hash,
        "build_precondition_hash": _hash_json(build_precondition),
        "review_basis_hash": resolved_review_basis_hash,
        "review_subject_kind": review_subject_kind,
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "backend_id": backend_id,
        "reviewer_argv_hash": reviewer_argv_hash,
    }
    return {
        "schema_version": "phase2.semantic_review.input.v3",
        "mode": mode,
        "attempt": attempt,
        "generated_at": utc_stamp(),
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "task": task_payload,
        "review_subject_kind": review_subject_kind,
        "review_subject_file": str(candidate_path),
        "review_subject_hash": candidate_hash,
        "candidate": {
            "file": str(candidate_path),
            "hash": candidate_hash,
            "lean": candidate_code,
        },
        "review_context_file": review_context_file,
        "review_context_hash": review_context_hash,
        "review_context_markdown": review_context_markdown,
        "review_basis": review_basis,
        "review_basis_hash": resolved_review_basis_hash,
        "imports": import_lines,
        "dependencies": dependency_summary,
        "search_summary": search_summary,
        "build_summary": build_summary,
        "build_precondition": build_precondition,
        "reviewer_backend_id": backend_id,
        "reviewer_argv_hash": reviewer_argv_hash,
        "cache_basis": cache_basis,
        "cache_key": _hash_json(cache_basis),
        "rubric": [
            "Extract the source TeX's main mathematical claims.",
            "Map each source claim to the Lean candidate's declaration, assumptions, and conclusion.",
            "Fail or mark inconclusive if a claim is missing, weakened, converted into an assumption, or hidden behind a placeholder.",
            "When the source TeX contains an essential proof, construction, partition argument, or contradiction argument, preserve that proof spine at an appropriate abstraction level instead of replacing it with a theorem-specific wrapper.",
            "When proof_obligations are present in the review basis, judge each blocking obligation explicitly in obligation_review.items.",
            "Read the full semantic review context markdown before judging the candidate.",
            "Do not accept a pass verdict without non-empty source_claims, claim_mapping, obligation_review, interface_contract, downstream_adequacy, and forbidden_weakenings.",
            "A theorem that cannot honestly support its direct downstream consumers does not pass semantic review.",
            "Fail any theorem whose direct downstream textbook consumer would need a fresh theorem-level hypothesis that is absent from the source downstream task.",
            "For definitions, fail if divergence or undefinedness is hidden behind an arbitrary fallback value such as `0`, `default`, or an unconditional witness.",
            "For definitions that split convergence and value, fail if the exported value can be consumed downstream without an explicit convergence proof or equivalent guard.",
            "Lean build success is necessary but not sufficient for semantic faithfulness.",
        ],
    }


def render_semantic_review_prompt(review_input: dict[str, Any]) -> str:
    task = review_input["task"]
    candidate = review_input["candidate"]
    context_markdown = str(review_input.get("review_context_markdown", "")).strip()
    return "\n".join(
        [
            f"# Semantic Review for {task.get('block_id', '')}",
            "",
            f"- Mode: `{review_input.get('mode')}`",
            f"- Prompt version: `{review_input.get('prompt_version')}`",
            f"- Rubric version: `{review_input.get('rubric_version')}`",
            f"- Candidate: `{candidate.get('file')}`",
            f"- Review context file: `{review_input.get('review_context_file', '') or '(none)'}`",
            "",
            "## Task Source",
            "",
            f"Type: `{task.get('type', '')}`",
            f"Source plan: `{task.get('source_plan', '')}`",
            "",
            "### Title",
            "",
            str(task.get("title", "")).strip() or "(untitled)",
            "",
            "### TeX / Plan Content",
            "",
            str(task.get("content", "")).strip() or "(empty)",
            "",
            "## Candidate Lean",
            "",
            "```lean",
            str(candidate.get("lean", "")).rstrip(),
            "```",
            "",
            "## Full Review Context",
            "",
            context_markdown or "(missing review context markdown)",
            "",
            "## Review Task",
            "",
            "Return JSON only, written to the result path supplied by the runner.",
            "Use the generated result template as the starting JSON payload.",
            "Keep these binding fields unchanged: task_id, mode, attempt, prompt_version, rubric_version, review_input_file, review_prompt_file, expected_result_file, candidate_hash.",
            "Fill these semantic review fields: verdict, confidence, summary, source_claims, claim_mapping, spine_alignment, obligation_review, interface_contract, downstream_adequacy, forbidden_weakenings, findings, recommended_disposition.",
            "Allowed verdict values: pass, fail, inconclusive.",
            "A pass requires non-empty source_claims and claim_mapping that explicitly connect source claims to Lean declarations, assumptions, and conclusions.",
            "A pass also requires spine_alignment.status = covered with non-empty obligations_checked, obligation_review.status = covered with every blocking proof obligation covered or not_applicable, plus interface_contract.status = covered and downstream_adequacy.status = covered.",
            "If the source text relies on a proof, construction, reduction, interface translation, proof-debt support, case split, contradiction, partition argument, or other intermediate obligation, a pass must explain in spine_alignment.obligations_checked where that source spine lands in Lean.",
            "If the review context lists proof_obligations, obligation_review.items must cite each obligation_id, status, and Lean evidence; open blockers or scaffold hypotheses without a discharge plan rule out pass.",
            "If the reviewer cannot point to the Lean landing place of the source spine and can only describe a shortcut or black-box replacement, the verdict must be fail or inconclusive rather than pass.",
            "When the review basis lists direct downstream consumers, a pass must include one consumers_checked entry per consumer with status covered/not_applicable and no blocking_issues.",
            "Every forbidden weakening listed in the context must be judged explicitly in forbidden_weakenings.",
            "If a theorem is only locally correct but its direct downstream consumer would need new theorem-level assumptions, the verdict must be fail rather than pass.",
            "If a definition uses a fallback value to mask divergence or undefinedness, the verdict must be fail rather than pass.",
        ]
    ).rstrip() + "\n"


def normalize_reviewer_result(raw: Any, *, review_input: dict[str, Any], runner_metadata: dict[str, Any]) -> dict[str, Any]:
    base = {
        "schema_version": "phase2.semantic_review.result.v5",
        "task_id": review_input.get("task", {}).get("block_id", ""),
        "mode": review_input.get("mode", ""),
        "attempt": review_input.get("attempt"),
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "review_input_hash": _hash_json(review_input),
        "cache_key": review_input.get("cache_key", ""),
        "reviewer_backend_id": review_input.get("reviewer_backend_id", ""),
        "runner": runner_metadata,
    }
    if not isinstance(raw, dict):
        return _inconclusive_result(base, "reviewer result is not a JSON object", cache_class="operational_failure")
    missing = sorted(SEMANTIC_REVIEW_REQUIRED_FIELDS - set(raw.keys()))
    if missing:
        return _inconclusive_result(
            base,
            "reviewer result is missing required fields: " + ", ".join(missing),
            raw=raw,
            cache_class="operational_failure",
        )
    result = {**base, **raw}
    expected_task_id = canonicalize_block_id(str(review_input.get("task", {}).get("block_id", "") or ""))
    result_task_id = canonicalize_block_id(str(result.get("task_id", "") or ""))
    if result_task_id != expected_task_id:
        return _inconclusive_result(
            base,
            f"reviewer result task id mismatch: expected {expected_task_id}, got {result_task_id or '(missing)'}",
            raw=raw,
            cache_class="operational_failure",
        )
    if int(result.get("prompt_version") or 0) != SEMANTIC_REVIEW_PROMPT_VERSION:
        return _inconclusive_result(
            base,
            "reviewer result prompt_version does not match current semantic review prompt version",
            raw=raw,
            cache_class="operational_failure",
        )
    if int(result.get("rubric_version") or 0) != SEMANTIC_REVIEW_RUBRIC_VERSION:
        return _inconclusive_result(
            base,
            "reviewer result rubric_version does not match current semantic review rubric version",
            raw=raw,
            cache_class="operational_failure",
        )
    if str(result.get("review_input_hash", "") or "") != str(base["review_input_hash"]):
        return _inconclusive_result(
            base,
            "reviewer result review_input_hash does not match current semantic review input",
            raw=raw,
            cache_class="operational_failure",
        )
    expected_review_input_path = _expected_review_input_path(review_input)
    raw_review_input_file = str(result.get("review_input_file", "") or "").strip()
    if raw_review_input_file and expected_review_input_path is not None:
        resolved_review_input = Path(raw_review_input_file).expanduser()
        if not resolved_review_input.is_absolute():
            resolved_review_input = (expected_review_input_path.parent / resolved_review_input).resolve()
        if resolved_review_input != expected_review_input_path:
            return _inconclusive_result(
                base,
                "reviewer result review_input_file does not match current semantic review input file",
                raw=raw,
                cache_class="operational_failure",
            )
    expected_candidate_hash = str(review_input.get("candidate", {}).get("hash", "") or "")
    if str(result.get("candidate_hash", "") or "") != expected_candidate_hash:
        return _inconclusive_result(
            base,
            "reviewer result candidate_hash does not match current semantic review input candidate hash",
            raw=raw,
            cache_class="operational_failure",
        )
    verdict = str(result.get("verdict", "")).strip().lower()
    if verdict not in {"pass", "fail", "inconclusive"}:
        return _inconclusive_result(base, f"invalid reviewer verdict: {result.get('verdict')}", raw=raw, cache_class="operational_failure")
    result["verdict"] = verdict
    for field in ("source_claims", "claim_mapping", "forbidden_weakenings", "findings"):
        if not isinstance(result.get(field), list):
            return _inconclusive_result(base, f"reviewer field {field} must be a list", raw=raw, cache_class="operational_failure")
    if not isinstance(result.get("spine_alignment"), dict):
        return _inconclusive_result(base, "reviewer field spine_alignment must be an object", raw=raw, cache_class="operational_failure")
    spine_status = str(result["spine_alignment"].get("status", "")).strip().lower()
    if spine_status not in {"covered", "partial", "missing", "violated", "unclear"}:
        return _inconclusive_result(
            base,
            "reviewer field spine_alignment.status must be one of covered/partial/missing/violated/unclear",
            raw=raw,
            cache_class="operational_failure",
        )
    obligations_checked = result["spine_alignment"].get("obligations_checked", [])
    if not isinstance(obligations_checked, list):
        return _inconclusive_result(
            base,
            "reviewer field spine_alignment.obligations_checked must be a list",
            raw=raw,
            cache_class="operational_failure",
        )
    missing_obligations = result["spine_alignment"].get("missing_obligations", [])
    if not isinstance(missing_obligations, list):
        return _inconclusive_result(
            base,
            "reviewer field spine_alignment.missing_obligations must be a list",
            raw=raw,
            cache_class="operational_failure",
        )
    obligation_shape_error = validate_obligation_review_shape(result)
    if obligation_shape_error:
        return _inconclusive_result(base, obligation_shape_error, raw=raw, cache_class="operational_failure")
    for field in ("interface_contract", "downstream_adequacy"):
        if not isinstance(result.get(field), dict):
            return _inconclusive_result(base, f"reviewer field {field} must be an object", raw=raw, cache_class="operational_failure")
        status = str(result.get(field, {}).get("status", "")).strip().lower()
        if status not in {"covered", "partial", "missing", "violated", "unclear"}:
            return _inconclusive_result(
                base,
                f"reviewer field {field}.status must be one of covered/partial/missing/violated/unclear",
                raw=raw,
                cache_class="operational_failure",
            )
    mismatches = result["interface_contract"].get("mismatches", [])
    if not isinstance(mismatches, list):
        return _inconclusive_result(base, "reviewer field interface_contract.mismatches must be a list", raw=raw, cache_class="operational_failure")
    consumers_checked = result["downstream_adequacy"].get("consumers_checked", [])
    if not isinstance(consumers_checked, list):
        return _inconclusive_result(base, "reviewer field downstream_adequacy.consumers_checked must be a list", raw=raw, cache_class="operational_failure")
    blocking_issues = result["downstream_adequacy"].get("blocking_issues", [])
    if not isinstance(blocking_issues, list):
        return _inconclusive_result(base, "reviewer field downstream_adequacy.blocking_issues must be a list", raw=raw, cache_class="operational_failure")
    if verdict == "pass" and (
        not result["source_claims"]
        or not result["claim_mapping"]
        or spine_status != "covered"
        or not obligations_checked
        or str(result["interface_contract"].get("status", "")).strip().lower() != "covered"
        or str(result["downstream_adequacy"].get("status", "")).strip().lower() != "covered"
        or not result["forbidden_weakenings"]
    ):
        return _inconclusive_result(
            base,
            "invalid reviewer output: pass verdict requires non-empty source_claims/claim_mapping/"
            "spine_alignment.obligations_checked/forbidden_weakenings and covered spine_alignment/"
            "interface_contract/downstream_adequacy",
            raw=raw,
            cache_class="operational_failure",
        )
    obligation_pass_error = validate_obligation_review_for_pass(review_input, result) if verdict == "pass" else ""
    if obligation_pass_error:
        return _inconclusive_result(base, obligation_pass_error, raw=raw, cache_class="operational_failure")
    if verdict == "pass":
        invalid_fw = [
            item for item in result["forbidden_weakenings"]
            if not isinstance(item, dict)
            or str(item.get("status", "")).strip().lower() not in {"not_present", "present", "not_applicable"}
        ]
        if invalid_fw:
            return _inconclusive_result(
                base,
                "invalid reviewer output: forbidden_weakenings entries must explicitly use status not_present/present/not_applicable",
                raw=raw,
                cache_class="operational_failure",
            )
        elif any(str(item.get("status", "")).strip().lower() == "present" for item in result["forbidden_weakenings"] if isinstance(item, dict)):
            return _inconclusive_result(
                base,
                "invalid reviewer output: pass verdict cannot include forbidden weakening marked present",
                raw=raw,
                cache_class="operational_failure",
            )
    if result["verdict"] == "pass":
        review_basis = review_input.get("review_basis", {})
        direct_consumers = review_basis.get("direct_downstream_consumers", []) if isinstance(review_basis, dict) else []
        normalized_direct_consumers = [
            str(item.get("block_id", "")).strip()
            for item in direct_consumers
            if isinstance(item, dict) and str(item.get("block_id", "")).strip()
        ]
        if normalized_direct_consumers:
            if not consumers_checked:
                return _inconclusive_result(
                    base,
                    "invalid reviewer output: pass verdict requires consumer-level downstream coverage for all direct downstream consumers",
                    raw=raw,
                    cache_class="operational_failure",
                )
            else:
                covered_consumers: dict[str, str] = {}
                invalid_consumer_entries = False
                for item in consumers_checked:
                    if not isinstance(item, dict):
                        invalid_consumer_entries = True
                        break
                    consumer_id = str(item.get("block_id", "")).strip()
                    consumer_status = str(item.get("status", "")).strip().lower()
                    if not consumer_id or consumer_status not in {"covered", "not_applicable", "blocked"}:
                        invalid_consumer_entries = True
                        break
                    covered_consumers[consumer_id] = consumer_status
                missing_consumers = [consumer_id for consumer_id in normalized_direct_consumers if consumer_id not in covered_consumers]
                blocked_consumers = [consumer_id for consumer_id in normalized_direct_consumers if covered_consumers.get(consumer_id) == "blocked"]
                if invalid_consumer_entries or missing_consumers or blocked_consumers or blocking_issues:
                    return _inconclusive_result(
                        base,
                        "invalid reviewer output: pass verdict requires explicit downstream coverage for each direct downstream consumer "
                        "with no blocking issues",
                        raw=raw,
                        cache_class="operational_failure",
                    )
    result["cache_class"] = "semantic_verdict"
    return result


def _expected_review_input_path(review_input: dict[str, Any]) -> Path | None:
    attempt = int(review_input.get("attempt") or 0)
    if attempt <= 0:
        return None
    review_context_file = str(review_input.get("review_context_file", "") or "").strip()
    if review_context_file:
        base_path = Path(review_context_file).expanduser()
        if not base_path.is_absolute():
            base_path = (Path.cwd() / base_path).resolve()
        return (base_path.parent / f"{SEMANTIC_REVIEW_INPUT_PREFIX}_v{attempt}.json").resolve()
    review_subject_file = str(
        review_input.get("review_subject_file", "")
        or review_input.get("candidate", {}).get("file", "")
        or ""
    ).strip()
    if review_subject_file:
        base_path = Path(review_subject_file).expanduser()
        if not base_path.is_absolute():
            base_path = (Path.cwd() / base_path).resolve()
        return (base_path.parent / f"{SEMANTIC_REVIEW_INPUT_PREFIX}_v{attempt}.json").resolve()
    return None


def _inconclusive_result(
    base: dict[str, Any],
    reason: str,
    *,
    raw: Any | None = None,
    cache_class: str = "semantic_verdict",
) -> dict[str, Any]:
    result = {
        **base,
        "verdict": "inconclusive",
        "confidence": "none",
        "summary": reason,
        "source_claims": [],
        "claim_mapping": [],
        "spine_alignment": {
            "status": "unclear",
            "summary": reason,
            "obligations_checked": [],
            "missing_obligations": [],
            "shortcut_assessment": "unclear",
        },
        "obligation_review": {
            "status": "unclear",
            "summary": reason,
            "items": [],
            "open_blockers": [],
            "scaffold_assessment": [],
        },
        "interface_contract": {
            "status": "unclear",
            "summary": reason,
            "mismatches": [],
        },
        "downstream_adequacy": {
            "status": "unclear",
            "summary": reason,
            "consumers_checked": [],
            "blocking_issues": [],
        },
        "forbidden_weakenings": [],
        "findings": [
            {
                "severity": "error",
                "category": "reviewer_runner",
                "message": reason,
            }
        ],
        "recommended_disposition": "needs_review",
        "normalization_reason": reason,
        "cache_class": cache_class,
    }
    if raw is not None:
        result["raw_result"] = raw
    return result


def run_semantic_review(
    *,
    pack_dir: Path,
    attempt: int,
    review_input: dict[str, Any],
    config: SemanticReviewerConfig | None,
    allow_missing_config: bool,
) -> dict[str, Any]:
    pack_dir.mkdir(parents=True, exist_ok=True)
    paths = next_semantic_review_artifact_paths(pack_dir, attempt)
    latest = latest_semantic_review_artifact_paths(pack_dir)
    context_path = next_semantic_review_context_path(pack_dir, attempt)
    latest_context = latest_semantic_review_context_path(pack_dir)
    prompt_text = render_semantic_review_prompt(review_input)
    context_markdown = str(review_input.get("review_context_markdown", "") or "").strip()
    _write_json(paths["input"], review_input)
    paths["prompt"].write_text(prompt_text, encoding="utf-8")
    if context_markdown:
        context_path.write_text(context_markdown + "\n", encoding="utf-8")

    cached = _find_cached_result(pack_dir, review_input.get("cache_key", ""), exclude_attempt=attempt)
    if cached is not None:
        result = dict(cached)
        result["cache_hit"] = True
        result["cached_from"] = cached.get("review_result_file", "")
    else:
        result = _run_or_inconclusive(paths, review_input, config, allow_missing_config)
        result["cache_hit"] = False

    result["review_result_file"] = str(paths["result"])
    result["review_input_file"] = str(paths["input"])
    result["review_prompt_file"] = str(paths["prompt"])
    result["review_report_file"] = str(paths["report"])
    _write_json(paths["result"], result)
    paths["report"].write_text(render_semantic_review_report(result), encoding="utf-8")

    for key, path in latest.items():
        if path.exists():
            path.unlink()
        shutil.copyfile(paths[key], path)
    if context_path.exists():
        if latest_context.exists():
            latest_context.unlink()
        shutil.copyfile(context_path, latest_context)

    return result


def _run_or_inconclusive(
    paths: dict[str, Path],
    review_input: dict[str, Any],
    config: SemanticReviewerConfig | None,
    allow_missing_config: bool,
) -> dict[str, Any]:
    if config is None:
        metadata = {"status": "missing_config", "stdout": "", "stderr": "", "returncode": None}
        reason = (
            "TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON is not configured. "
            "Use review-pack/review-apply for Codex or manual review."
        )
        if not allow_missing_config:
            reason = (
                "semantic reviewer is required for verify but TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON is not configured. "
                "Use review-pack/review-apply for Codex or manual review."
            )
        return _inconclusive_result(
            _base_for_runner_failure(review_input, metadata),
            reason,
            cache_class="operational_failure",
        )

    argv = [
        item.format(input=str(paths["input"]), prompt=str(paths["prompt"]), result=str(paths["result"]))
        for item in config.argv_template
    ]
    try:
        proc = subprocess.run(
            argv,
            shell=False,
            cwd=str(paths["input"].parent),
            capture_output=True,
            text=True,
            timeout=config.timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        metadata = {
            "status": "timeout",
            "argv": argv,
            "stdout": _bounded(exc.stdout or ""),
            "stderr": _bounded(exc.stderr or ""),
            "returncode": None,
        }
        return _inconclusive_result(
            _base_for_runner_failure(review_input, metadata),
            "semantic reviewer timed out",
            cache_class="operational_failure",
        )
    except Exception as exc:
        metadata = {"status": "runner_error", "argv": argv, "stdout": "", "stderr": str(exc), "returncode": None}
        return _inconclusive_result(
            _base_for_runner_failure(review_input, metadata),
            f"semantic reviewer failed to start: {exc}",
            cache_class="operational_failure",
        )

    metadata = {
        "status": "completed" if proc.returncode == 0 else "nonzero_exit",
        "argv": argv,
        "stdout": _bounded(proc.stdout or ""),
        "stderr": _bounded(proc.stderr or ""),
        "returncode": proc.returncode,
    }
    if proc.returncode != 0:
        return _inconclusive_result(
            _base_for_runner_failure(review_input, metadata),
            "semantic reviewer exited nonzero",
            cache_class="operational_failure",
        )
    if not paths["result"].exists():
        return _inconclusive_result(
            _base_for_runner_failure(review_input, metadata),
            "semantic reviewer did not write result file",
            cache_class="operational_failure",
        )
    try:
        raw = json.loads(paths["result"].read_text(encoding="utf-8"))
    except Exception as exc:
        return _inconclusive_result(
            _base_for_runner_failure(review_input, metadata),
            f"semantic reviewer wrote invalid JSON: {exc}",
            cache_class="operational_failure",
        )
    return normalize_reviewer_result(raw, review_input=review_input, runner_metadata=metadata)


def _base_for_runner_failure(review_input: dict[str, Any], metadata: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": "phase2.semantic_review.result.v5",
        "task_id": review_input.get("task", {}).get("block_id", ""),
        "mode": review_input.get("mode", ""),
        "attempt": review_input.get("attempt"),
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "review_input_hash": _hash_json(review_input),
        "cache_key": review_input.get("cache_key", ""),
        "reviewer_backend_id": review_input.get("reviewer_backend_id", ""),
        "runner": metadata,
    }


def _find_cached_result(pack_dir: Path, cache_key: str, *, exclude_attempt: int) -> dict[str, Any] | None:
    if not cache_key:
        return None
    for path in sorted(pack_dir.glob(f"{SEMANTIC_REVIEW_RESULT_PREFIX}_v*.json")):
        match = re.fullmatch(rf"{SEMANTIC_REVIEW_RESULT_PREFIX}_v(\d+)\.json", path.name)
        if match and int(match.group(1)) == exclude_attempt:
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if (
            isinstance(payload, dict)
            and payload.get("cache_key") == cache_key
            and payload.get("cache_class") == "semantic_verdict"
        ):
            return payload
    return None


def render_semantic_review_report(result: dict[str, Any]) -> str:
    findings = result.get("findings", [])
    interface_contract = result.get("interface_contract", {})
    downstream_adequacy = result.get("downstream_adequacy", {})
    obligation_review = result.get("obligation_review", {})
    forbidden_weakenings = result.get("forbidden_weakenings", [])
    lines = [
        f"# Semantic Review Report for {result.get('task_id', '')}",
        "",
        f"- Verdict: `{result.get('verdict', 'inconclusive')}`",
        f"- Confidence: `{result.get('confidence', '')}`",
        f"- Recommended disposition: `{result.get('recommended_disposition', '')}`",
        f"- Cache hit: `{bool(result.get('cache_hit', False))}`",
        "",
        "## Summary",
        "",
        str(result.get("summary", "")).strip() or "(no summary)",
        "",
        "## Interface Contract",
        "",
        f"- Status: `{interface_contract.get('status', 'unclear')}`",
        f"- Summary: {str(interface_contract.get('summary', '')).strip() or '(no summary)'}",
        "",
        "## Proof Obligations",
        "",
        f"- Status: `{obligation_review.get('status', 'unclear') if isinstance(obligation_review, dict) else 'unclear'}`",
        f"- Summary: {str(obligation_review.get('summary', '') if isinstance(obligation_review, dict) else '').strip() or '(no summary)'}",
        "",
        "## Downstream Adequacy",
        "",
        f"- Status: `{downstream_adequacy.get('status', 'unclear')}`",
        f"- Summary: {str(downstream_adequacy.get('summary', '')).strip() or '(no summary)'}",
        "",
        "## Forbidden Weakenings",
        "",
    ]
    if isinstance(forbidden_weakenings, list) and forbidden_weakenings:
        for item in forbidden_weakenings:
            if isinstance(item, dict):
                lines.append(
                    f"- `{item.get('status', 'unclear')}` `{item.get('name', 'unnamed')}`: {item.get('notes', '')}"
                )
            else:
                lines.append(f"- {item}")
    else:
        lines.append("- No explicit forbidden weakening judgments were reported.")
    lines.extend(
        [
            "",
        "## Findings",
        "",
        ]
    )
    if isinstance(findings, list) and findings:
        for item in findings:
            if isinstance(item, dict):
                lines.append(f"- `{item.get('severity', 'info')}` / `{item.get('category', 'general')}`: {item.get('message', '')}")
            else:
                lines.append(f"- {item}")
    else:
        lines.append("- No findings reported.")
    return "\n".join(lines).rstrip() + "\n"


def _bounded(text: str) -> str:
    text = str(text or "")
    if len(text) <= MAX_CAPTURE_CHARS:
        return text
    return text[:MAX_CAPTURE_CHARS] + "\n[truncated]"


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
