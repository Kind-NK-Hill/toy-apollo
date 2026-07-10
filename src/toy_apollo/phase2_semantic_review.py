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


SEMANTIC_REVIEW_PROMPT_VERSION = 9
SEMANTIC_REVIEW_RUBRIC_VERSION = 9
SEMANTIC_REVIEW_INPUT_SCHEMA_VERSION = "phase2.semantic_review.input.v3"
SEMANTIC_REVIEW_REQUIRED_FIELDS = {
    "verdict",
    "confidence",
    "summary",
    "proof_class",
    "completion_class",
    "reviewer_independence",
    "source_claims",
    "claim_mapping",
    "route_inspection",
    "spine_alignment",
    "obligation_review",
    "evidence_review",
    "interface_contract",
    "downstream_adequacy",
    "forbidden_weakenings",
    "findings",
    "recommended_disposition",
}
EVIDENCE_REVIEW_STATUS_VALUES = {"covered", "partial", "missing", "violated", "unclear", "not_applicable"}
EVIDENCE_REVIEW_PASS_VALUES = {"covered", "not_applicable"}
ROUTE_INSPECTION_STATUS_VALUES = {"covered", "partial", "missing", "violated", "unclear", "not_applicable"}
ROUTE_INSPECTION_PASS_VALUES = {"covered", "not_applicable"}
ROUTE_INSPECTION_STOP_GO_VALUES = {
    "go",
    "stop",
    "needs_reassembly",
    "needs_route_redesign",
    "unclear",
    "not_applicable",
}
ROUTE_INSPECTION_REQUIRED_FIELDS = [
    "source_route",
    "expected_answer_or_statement",
    "local_mathlib_search",
    "public_interface_check",
    "support_or_reassembly_decision",
    "stop_go_verdict",
]
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


def _matches_version(value: Any, expected: int) -> bool:
    if isinstance(value, bool):
        return False
    try:
        return int(value) == expected
    except (TypeError, ValueError):
        return False


def _object_field(payload: Any, field: str) -> dict[str, Any]:
    if not isinstance(payload, dict):
        return {}
    value = payload.get(field, {})
    return value if isinstance(value, dict) else {}


def _validate_review_input_internal_binding(review_input: dict[str, Any]) -> str:
    if str(review_input.get("schema_version", "") or "") != SEMANTIC_REVIEW_INPUT_SCHEMA_VERSION:
        return f"review input schema_version must be {SEMANTIC_REVIEW_INPUT_SCHEMA_VERSION}"
    if not _matches_version(review_input.get("prompt_version"), SEMANTIC_REVIEW_PROMPT_VERSION):
        return "review input prompt_version does not match current semantic review prompt version"
    if not _matches_version(review_input.get("rubric_version"), SEMANTIC_REVIEW_RUBRIC_VERSION):
        return "review input rubric_version does not match current semantic review rubric version"

    task_payload = _object_field(review_input, "task")
    candidate_payload = _object_field(review_input, "candidate")
    review_basis = _object_field(review_input, "review_basis")
    basis_task = _object_field(review_basis, "task")
    review_basis_hash = str(review_input.get("review_basis_hash", "") or "")
    if not review_basis_hash or _hash_json(review_basis) != review_basis_hash:
        return "review input review_basis does not match review_basis_hash"
    if task_payload != basis_task:
        return "review input task payload does not match review_basis.task"

    review_subject_kind = str(review_input.get("review_subject_kind", "") or "")
    if review_subject_kind not in {"candidate", "official_output", "existing_support"}:
        return "review input review_subject_kind is invalid"
    recorded_subject_hash = str(review_input.get("review_subject_hash", "") or "")
    candidate_hash = str(candidate_payload.get("hash", "") or "")
    if not recorded_subject_hash or candidate_hash != recorded_subject_hash:
        return "review input candidate.hash does not match review_subject_hash"
    candidate_lean = candidate_payload.get("lean")
    if not isinstance(candidate_lean, str) or _hash_text(candidate_lean) != recorded_subject_hash:
        return "review input inline candidate Lean does not match review_subject_hash"
    review_subject_file = str(review_input.get("review_subject_file", "") or "").strip()
    candidate_file = str(candidate_payload.get("file", "") or "").strip()
    if not review_subject_file or candidate_file != review_subject_file:
        return "review input candidate.file does not match review_subject_file"

    context_markdown = review_input.get("review_context_markdown")
    context_hash = str(review_input.get("review_context_hash", "") or "")
    if not isinstance(context_markdown, str) or not context_hash or _hash_text(context_markdown) != context_hash:
        return "review input review_context_markdown does not match review_context_hash"
    return ""


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
    if not isinstance(review_basis, dict):
        review_basis = {}
    basis_task = review_basis.get("task", {})
    if not isinstance(basis_task, dict):
        basis_task = {}
    task_payload = {
        "block_id": task.get("block_id", ""),
        "type": task.get("type", ""),
        "title": task.get("title", ""),
        "content": task.get("content", ""),
        "source_plan": task.get("source_plan", ""),
        "dependencies": task.get("dependencies", []),
        "soft_imports": task.get("soft_imports", []),
        "soft_imports_confirmed_at": task.get("soft_imports_confirmed_at", "")
        or basis_task.get("soft_imports_confirmed_at", ""),
    }
    dependency_summary_hash = _hash_json(dependency_summary)
    task_source_hash = _hash_json(task_payload)
    candidate_hash = _hash_text(candidate_code)
    if review_subject_kind == "candidate":
        build_precondition_kind = "candidate_build_ready"
    elif review_subject_kind == "existing_support":
        build_precondition_kind = "existing_support_sanity"
    else:
        build_precondition_kind = "official_output_sanity"
    build_precondition = {
        "kind": build_precondition_kind,
        "build_result_file": build_result_file,
        "build_candidate_file": build_candidate_file,
        "build_candidate_hash": build_candidate_hash,
        "sanity_build_module": sanity_build_module,
        "sanity_build_passed": bool(sanity_build_passed),
    }
    reviewer_role_contract = {
        "required_role": "independent_read_only_reviewer",
        "read_only": True,
        "may_edit_candidate": False,
        "may_author_same_candidate": False,
        "must_use_current_review_request": True,
    }
    resolved_review_basis_hash = review_basis_hash or (_hash_json(review_basis) if review_basis else "")
    cache_basis = {
        "task_source_hash": task_source_hash,
        "candidate_hash": candidate_hash,
        "imports_hash": _hash_json(import_lines),
        "dependency_summary_hash": dependency_summary_hash,
        "search_summary_hash": _hash_json(search_summary),
        "build_summary_hash": _hash_json(build_summary),
        "build_precondition_hash": _hash_json(build_precondition),
        "reviewer_role_contract_hash": _hash_json(reviewer_role_contract),
        "review_basis_hash": resolved_review_basis_hash,
        "review_context_hash": review_context_hash,
        "review_subject_kind": review_subject_kind,
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "backend_id": backend_id,
        "reviewer_argv_hash": reviewer_argv_hash,
    }
    return {
        "schema_version": SEMANTIC_REVIEW_INPUT_SCHEMA_VERSION,
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
        "reviewer_role_contract": reviewer_role_contract,
        "reviewer_backend_id": backend_id,
        "reviewer_argv_hash": reviewer_argv_hash,
        "cache_basis": cache_basis,
        "cache_key": _hash_json(cache_basis),
        "rubric": [
            "Extract the source TeX's main mathematical claims.",
            "Map each source claim to the Lean candidate's declaration, assumptions, and conclusion.",
            "Fail or mark inconclusive if a claim is missing, weakened, converted into an assumption, or hidden behind a placeholder.",
            "When the source TeX contains an essential proof, construction, partition argument, or contradiction argument, preserve that proof spine at an appropriate abstraction level instead of replacing it with a theorem-specific wrapper.",
            "Use the textbook-first, bridge-then-Mathlib policy for shared mathematical interfaces: first identify the textbook object, then accept Mathlib use only through a reviewed source-step landing or reusable equivalence bridge.",
            "A reviewed equivalence bridge may use Mathlib infrastructure, but an adapter-only shortcut that skips the source proof spine cannot cleanly complete a proof-bearing task.",
            "When proof_obligations are present in the review basis, judge each blocking obligation explicitly in obligation_review.items.",
            "For a covered proof obligation, verify that the Lean landing is a theorem/lemma with the expected theorem signature, does not simply re-assume the same source step in its body, and does not move the obligation into a public theorem premise.",
            "Read the full semantic review context markdown before judging the candidate.",
            "Do not accept a pass verdict without non-empty source_claims, claim_mapping, obligation_review, interface_contract, downstream_adequacy, and forbidden_weakenings.",
            "A theorem that cannot honestly support its direct downstream consumers does not pass semantic review.",
            "Fail any theorem whose direct downstream textbook consumer would need a fresh theorem-level hypothesis that is absent from the source downstream task.",
            "For definitions, fail if divergence or undefinedness is hidden behind an arbitrary fallback value such as `0`, `default`, or an unconditional witness.",
            "For definitions that split convergence and value, fail if the exported value can be consumed downstream without an explicit convergence proof or equivalent guard.",
            "Lean build success is necessary but not sufficient for semantic faithfulness.",
            "The semantic reviewer must be independent and read-only: the author of the candidate must not self-review the same candidate.",
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
            "## Reviewer Role Contract",
            "",
            "This prompt is for an independent read-only reviewer subagent or a configured external reviewer runner.",
            "If you authored or edited this candidate in the current repair attempt, do not fill the result; hand it to an independent reviewer.",
            "Do not edit Lean files, prompt-pack files, obligations, classification, or ledger state while reviewing.",
            "The result must include a `reviewer_independence` object attesting that the review was read-only and independent.",
            "",
            "## Textbook / Mathlib Bridge Policy",
            "",
            "Use the textbook-first, bridge-then-Mathlib policy for shared mathematical interfaces.",
            "Textbook fidelity does not forbid Mathlib. A reviewed equivalence bridge may use Mathlib infrastructure when it maps to a specific source proof step and is reusable beyond the current task.",
            "Reject adapter-only shortcut routes: if the candidate merely applies a stronger Mathlib theorem or task-shaped bridge without landing the source proof spine, the verdict must be fail or inconclusive for proof-bearing tasks.",
            "For theorem/problem/exercise tasks, `interface_bridge_completed` by itself is not a clean proof class; the review must classify the final task route as source-route proof completion if the bridge genuinely discharges source steps.",
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
            "Fill these semantic review fields: verdict, confidence, summary, proof_class, completion_class, reviewer_independence, source_claims, claim_mapping, route_inspection, spine_alignment, obligation_review, evidence_review, interface_contract, downstream_adequacy, forbidden_weakenings, findings, recommended_disposition.",
            "The `reviewer_independence` object must be shaped as {\"role\": \"independent_read_only_reviewer\", \"read_only\": true, \"did_edit_candidate\": false, \"used_current_review_request\": true, \"attestation\": \"<short statement>\"}.",
            "Allowed verdict values: pass, fail, inconclusive.",
            "Status enum fields `spine_alignment.status`, `obligation_review.status`, `evidence_review.status`, `interface_contract.status`, and `downstream_adequacy.status` must use covered/partial/missing/violated/unclear; evidence_review may also use not_applicable for individual items.",
            "The route_inspection object is review context only, not completion authority. Fill source_route, expected_answer_or_statement, local_mathlib_search, public_interface_check, support_or_reassembly_decision, and stop_go_verdict.",
            "A pass requires route_inspection.status covered or not_applicable, stop_go_verdict go, and a public_interface_check that rules out public-premise relocation.",
            "The review basis lists required_evidence_classes. evidence_review.items must include one object per required class: source_tex, lean_subject, proof_obligations, audit, classification, dependency_status, downstream, ledger_status, hashes.",
            "For audit, classification, dependency_status, downstream, ledger_status, and hashes, explain conflicts or stale evidence instead of letting any single artifact decide completion.",
            "For obligation_review.items, each status must use covered/partial/missing/violated/unclear/not_applicable/accepted_as_proof_debt.",
            "For each covered obligation_review.items entry, include expected_theorem_signature, lean_landing, landing_kind, proof_contract_status, body_reassumption_check, signature_match, public_premise_check, and proof_contract_notes.",
            "A pass requires non-empty source_claims and claim_mapping that explicitly connect source claims to Lean declarations, assumptions, and conclusions.",
            "A pass also requires spine_alignment.status = covered with non-empty obligations_checked, obligation_review.status = covered with every blocking proof obligation covered, not_applicable, or explicitly accepted_as_proof_debt, evidence_review.status = covered with every required evidence class covered/not_applicable and no blocking_issues, plus interface_contract.status = covered and downstream_adequacy.status = covered.",
            "A covered proof obligation is eligible for pass only when proof_contract_status = verified and signature_match, body_reassumption_check, and public_premise_check are all passed.",
            "If the source text relies on a proof, construction, reduction, interface translation, proof-debt support, case split, contradiction, partition argument, or other intermediate obligation, a pass must explain in spine_alignment.obligations_checked where that source spine lands in Lean.",
            "If the review context lists proof_obligations, obligation_review.items must cite each obligation_id, status, and Lean evidence; use accepted_as_proof_debt only for explicit proof_debt_support assumptions that the project is intentionally carrying forward. Open blockers, scaffold hypotheses without a discharge plan, public-premise relocation, adapter-only landings for textbook targets, or unverified proof contracts rule out pass.",
            "Classify each obligation route as source-route theorem/lemma, Mathlib-backed adapter, interface bridge, open math debt, or beyond-book exception; do not report an adapter-only shortcut as textbook proof completion.",
            "A reusable bridge may support a proof-bearing task only when the review maps it to source proof steps and the final proof_class is a source-route completion class rather than `interface_bridge_completed` alone.",
            "If the reviewer cannot point to the Lean landing place of the source spine and can only describe a shortcut or black-box replacement, the verdict must be fail or inconclusive rather than pass.",
            "When the review basis lists direct downstream consumers, a pass must include one consumers_checked entry per consumer with status covered/not_applicable and no blocking_issues.",
            "downstream_adequacy.consumers_checked entries must be objects shaped as {\"block_id\": \"<direct downstream block_id>\", \"status\": \"covered | not_applicable | blocked\", \"evidence\": \"<why>\"}.",
            "Every forbidden weakening listed in the context must be judged explicitly in forbidden_weakenings.",
            "forbidden_weakenings entries use status not_present/present/not_applicable; pass cannot include a present forbidden weakening.",
            "If a theorem is only locally correct but its direct downstream consumer would need new theorem-level assumptions, the verdict must be fail rather than pass.",
            "If a definition uses a fallback value to mask divergence or undefinedness, the verdict must be fail rather than pass.",
        ]
    ).rstrip() + "\n"


def _validate_reviewer_independence(result: dict[str, Any]) -> str:
    reviewer = result.get("reviewer_independence")
    if not isinstance(reviewer, dict):
        return "reviewer result reviewer_independence must be an object"
    if str(reviewer.get("role", "") or "") != "independent_read_only_reviewer":
        return "reviewer result reviewer_independence.role must be independent_read_only_reviewer"
    if reviewer.get("read_only") is not True:
        return "reviewer result reviewer_independence.read_only must be true"
    if reviewer.get("did_edit_candidate") is not False:
        return "reviewer result reviewer_independence.did_edit_candidate must be false"
    if reviewer.get("used_current_review_request") is not True:
        return "reviewer result reviewer_independence.used_current_review_request must be true"
    if not str(reviewer.get("attestation", "") or "").strip():
        return "reviewer result reviewer_independence.attestation must be non-empty"
    return ""


def _validate_evidence_review(result: dict[str, Any], *, review_input: dict[str, Any], verdict: str) -> str:
    evidence_review = result.get("evidence_review")
    if not isinstance(evidence_review, dict):
        return "reviewer field evidence_review must be an object"
    status = str(evidence_review.get("status", "")).strip().lower()
    if status not in EVIDENCE_REVIEW_STATUS_VALUES:
        return "reviewer field evidence_review.status must be one of covered/partial/missing/violated/unclear/not_applicable"
    items = evidence_review.get("items", [])
    if not isinstance(items, list):
        return "reviewer field evidence_review.items must be a list"
    blocking_issues = evidence_review.get("blocking_issues", [])
    if not isinstance(blocking_issues, list):
        return "reviewer field evidence_review.blocking_issues must be a list"
    covered: dict[str, str] = {}
    for item in items:
        if not isinstance(item, dict):
            return "reviewer field evidence_review.items entries must be objects"
        evidence_class = str(item.get("evidence_class", "") or "").strip()
        item_status = str(item.get("status", "") or "").strip().lower()
        if not evidence_class:
            return "reviewer field evidence_review.items entries must include evidence_class"
        if item_status not in EVIDENCE_REVIEW_STATUS_VALUES:
            return "reviewer field evidence_review.items status must be one of covered/partial/missing/violated/unclear/not_applicable"
        covered[evidence_class] = item_status
    if verdict == "pass":
        review_basis = review_input.get("review_basis", {})
        required = review_basis.get("required_evidence_classes", []) if isinstance(review_basis, dict) else []
        if not isinstance(required, list):
            required = []
        missing = [
            str(evidence_class)
            for evidence_class in required
            if covered.get(str(evidence_class)) not in EVIDENCE_REVIEW_PASS_VALUES
        ]
        if status != "covered" or blocking_issues or missing:
            return (
                "invalid reviewer output: pass verdict requires evidence_review.status = covered, "
                "no evidence_review.blocking_issues, and covered/not_applicable items for every required evidence class"
            )
    return ""


def _validate_route_inspection(result: dict[str, Any], *, verdict: str) -> str:
    route = result.get("route_inspection")
    if not isinstance(route, dict):
        return "reviewer field route_inspection must be an object"
    status = str(route.get("status", "") or "").strip().lower()
    if status not in ROUTE_INSPECTION_STATUS_VALUES:
        return "reviewer field route_inspection.status must be one of covered/partial/missing/violated/unclear/not_applicable"
    stop_go = str(route.get("stop_go_verdict", "") or "").strip().lower()
    if stop_go not in ROUTE_INSPECTION_STOP_GO_VALUES:
        return "reviewer field route_inspection.stop_go_verdict must be one of go/stop/needs_reassembly/needs_route_redesign/unclear/not_applicable"
    missing = [
        field
        for field in ROUTE_INSPECTION_REQUIRED_FIELDS
        if field not in route or not str(route.get(field, "") or "").strip()
    ]
    if verdict == "pass":
        if status not in ROUTE_INSPECTION_PASS_VALUES or stop_go != "go" or missing:
            return (
                "invalid reviewer output: pass verdict requires route_inspection.status = covered or not_applicable, "
                "route_inspection.stop_go_verdict = go, and non-empty route inspection fields"
            )
    return ""


def normalize_reviewer_result(raw: Any, *, review_input: dict[str, Any], runner_metadata: dict[str, Any]) -> dict[str, Any]:
    review_input_payload = review_input if isinstance(review_input, dict) else {}
    task_payload = _object_field(review_input_payload, "task")
    candidate_payload = _object_field(review_input_payload, "candidate")
    base = {
        "schema_version": "phase2.semantic_review.result.v7",
        "task_id": task_payload.get("block_id", ""),
        "mode": review_input_payload.get("mode", ""),
        "attempt": review_input_payload.get("attempt"),
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "review_input_hash": _hash_json(review_input),
        "cache_key": review_input_payload.get("cache_key", ""),
        "reviewer_backend_id": review_input_payload.get("reviewer_backend_id", ""),
        "runner": runner_metadata,
    }
    if not isinstance(review_input, dict):
        return _inconclusive_result(
            base,
            "review input must be a JSON object",
            raw=raw,
            cache_class="operational_failure",
        )
    malformed_nested_fields = [
        field
        for field in ("task", "candidate")
        if not isinstance(review_input.get(field), dict)
    ]
    if malformed_nested_fields:
        return _inconclusive_result(
            base,
            "review input fields must be JSON objects: " + ", ".join(malformed_nested_fields),
            raw=raw,
            cache_class="operational_failure",
        )
    attempt_value = review_input.get("attempt")
    if isinstance(attempt_value, bool):
        valid_attempt = False
    else:
        try:
            valid_attempt = int(attempt_value) > 0
        except (TypeError, ValueError):
            valid_attempt = False
    if not valid_attempt:
        return _inconclusive_result(
            base,
            "review input attempt must be a positive integer",
            raw=raw,
            cache_class="operational_failure",
        )
    input_binding_error = _validate_review_input_internal_binding(review_input)
    if input_binding_error:
        return _inconclusive_result(
            base,
            input_binding_error,
            raw=raw,
            cache_class="operational_failure",
        )
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
    invalid_completion_fields = [
        field
        for field in ("proof_class", "completion_class")
        if not isinstance(raw.get(field), str) or not raw.get(field, "").strip()
    ]
    if invalid_completion_fields:
        return _inconclusive_result(
            base,
            "reviewer result fields must be non-empty strings: " + ", ".join(invalid_completion_fields),
            raw=raw,
            cache_class="operational_failure",
        )
    result = {**raw, **base}
    independence_error = _validate_reviewer_independence(result)
    if independence_error:
        return _inconclusive_result(base, independence_error, raw=raw, cache_class="operational_failure")
    expected_task_id = canonicalize_block_id(str(task_payload.get("block_id", "") or ""))
    result_task_id = canonicalize_block_id(str(raw.get("task_id", "") or ""))
    if result_task_id != expected_task_id:
        return _inconclusive_result(
            base,
            f"reviewer result task id mismatch: expected {expected_task_id}, got {result_task_id or '(missing)'}",
            raw=raw,
            cache_class="operational_failure",
        )
    if not _matches_version(raw.get("prompt_version"), SEMANTIC_REVIEW_PROMPT_VERSION):
        return _inconclusive_result(
            base,
            "reviewer result prompt_version does not match current semantic review prompt version",
            raw=raw,
            cache_class="operational_failure",
        )
    if not _matches_version(raw.get("rubric_version"), SEMANTIC_REVIEW_RUBRIC_VERSION):
        return _inconclusive_result(
            base,
            "reviewer result rubric_version does not match current semantic review rubric version",
            raw=raw,
            cache_class="operational_failure",
        )
    if str(raw.get("review_input_hash", "") or "") != str(base["review_input_hash"]):
        return _inconclusive_result(
            base,
            "reviewer result review_input_hash does not match current semantic review input",
            raw=raw,
            cache_class="operational_failure",
        )
    expected_review_input_path = _expected_review_input_path(review_input)
    raw_review_input_file = str(raw.get("review_input_file", "") or "").strip()
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
    expected_candidate_hash = str(candidate_payload.get("hash", "") or "")
    if str(raw.get("candidate_hash", "") or "") != expected_candidate_hash:
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
    _normalize_completion_class_fields(result, verdict=verdict)
    review_basis = review_input.get("review_basis", {}) if isinstance(review_input.get("review_basis", {}), dict) else {}
    source_evidence = review_basis.get("source_evidence", {}) if isinstance(review_basis.get("source_evidence", {}), dict) else {}
    if (
        verdict == "pass"
        and str(source_evidence.get("source_kind", "") or "") == "source_tex"
        and str(source_evidence.get("tex_status", "") or "") != "present"
    ):
        return _inconclusive_result(
            base,
            "invalid reviewer output: pass verdict requires the bound source TeX to be present",
            raw=raw,
            cache_class="operational_failure",
        )
    route_error = _validate_route_inspection(result, verdict=verdict)
    if route_error:
        return _inconclusive_result(base, route_error, raw=raw, cache_class="operational_failure")
    evidence_error = _validate_evidence_review(result, review_input=review_input, verdict=verdict)
    if evidence_error:
        return _inconclusive_result(base, evidence_error, raw=raw, cache_class="operational_failure")
    if verdict == "pass" and str(source_evidence.get("source_kind", "") or "") == "source_tex":
        evidence_items = result.get("evidence_review", {}).get("items", [])
        source_items = [
            item
            for item in evidence_items
            if isinstance(item, dict) and str(item.get("evidence_class", "") or "") == "source_tex"
        ]
        if source_items and any(str(item.get("status", "") or "").strip().lower() != "covered" for item in source_items):
            return _inconclusive_result(
                base,
                "invalid reviewer output: source-backed pass requires source_tex evidence status covered",
                raw=raw,
                cache_class="operational_failure",
            )
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


def _normalize_completion_class_fields(result: dict[str, Any], *, verdict: str) -> None:
    proof_class = str(result.get("proof_class", "") or "").strip().lower().replace("-", "_").replace(" ", "_")
    completion_class = str(result.get("completion_class", "") or "").strip().lower().replace("-", "_").replace(" ", "_")
    if not proof_class and completion_class:
        proof_class = completion_class
    if not completion_class and proof_class:
        completion_class = proof_class
    result["proof_class"] = proof_class
    result["completion_class"] = completion_class
    result["needs_class_normalization"] = verdict == "pass" and not proof_class


def _expected_review_input_path(review_input: dict[str, Any]) -> Path | None:
    if not isinstance(review_input, dict):
        return None
    try:
        attempt = int(review_input.get("attempt") or 0)
    except (TypeError, ValueError):
        return None
    if attempt <= 0:
        return None
    review_context_file = str(review_input.get("review_context_file", "") or "").strip()
    if review_context_file:
        base_path = Path(review_context_file).expanduser()
        if not base_path.is_absolute():
            base_path = (Path.cwd() / base_path).resolve()
        return (base_path.parent / f"{SEMANTIC_REVIEW_INPUT_PREFIX}_v{attempt}.json").resolve()
    candidate_payload = _object_field(review_input, "candidate")
    review_subject_file = str(
        review_input.get("review_subject_file", "")
        or candidate_payload.get("file", "")
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
        "reviewer_independence": {
            "role": "independent_read_only_reviewer",
            "read_only": True,
            "did_edit_candidate": False,
            "used_current_review_request": False,
            "attestation": f"Normalizer-generated inconclusive result: {reason}",
        },
        "source_claims": [],
        "claim_mapping": [],
        "route_inspection": {
            "status": "unclear",
            "source_route": "",
            "expected_answer_or_statement": "",
            "local_mathlib_search": "",
            "public_interface_check": "",
            "support_or_reassembly_decision": "",
            "stop_go_verdict": "unclear",
            "notes": reason,
        },
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
        "evidence_review": {
            "status": "unclear",
            "summary": reason,
            "items": [],
            "blocking_issues": [{"evidence_class": "reviewer_runner", "issue": reason}],
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
        "proof_class": "",
        "completion_class": "",
        "needs_class_normalization": False,
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
        cached_raw = {
            key: cached[key]
            for key in SEMANTIC_REVIEW_REQUIRED_FIELDS
            if key in cached
        }
        cached_raw.update(
            {
                "task_id": review_input.get("task", {}).get("block_id", ""),
                "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
                "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
                "review_input_hash": _hash_json(review_input),
                "review_input_file": str(paths["input"]),
                "candidate_hash": review_input.get("candidate", {}).get("hash", ""),
            }
        )
        result = normalize_reviewer_result(
            cached_raw,
            review_input=review_input,
            runner_metadata={
                "status": "cache_hit_revalidated",
                "cached_from": str(cached.get("_cache_source_file", "") or cached.get("review_result_file", "") or ""),
            },
        )
        if str(result.get("cache_class", "") or "") == "semantic_verdict":
            result["cache_hit"] = True
            result["cached_from"] = str(cached.get("_cache_source_file", "") or cached.get("review_result_file", "") or "")
        else:
            result = _run_or_inconclusive(paths, review_input, config, allow_missing_config)
            result["cache_hit"] = False
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
    review_input_payload = review_input if isinstance(review_input, dict) else {}
    task_payload = _object_field(review_input_payload, "task")
    return {
        "schema_version": "phase2.semantic_review.result.v7",
        "task_id": task_payload.get("block_id", ""),
        "mode": review_input_payload.get("mode", ""),
        "attempt": review_input_payload.get("attempt"),
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "review_input_hash": _hash_json(review_input),
        "cache_key": review_input_payload.get("cache_key", ""),
        "reviewer_backend_id": review_input_payload.get("reviewer_backend_id", ""),
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
            raw_input_file = str(payload.get("review_input_file", "") or "").strip()
            if not raw_input_file:
                continue
            input_path = Path(raw_input_file).expanduser()
            if not input_path.is_absolute():
                input_path = (path.parent / input_path).resolve()
            try:
                cached_input = json.loads(input_path.read_text(encoding="utf-8"))
            except Exception:
                continue
            if not isinstance(cached_input, dict):
                continue
            if str(cached_input.get("cache_key", "") or "") != cache_key:
                continue
            if str(payload.get("review_input_hash", "") or "") != _hash_json(cached_input):
                continue
            rebound = dict(payload)
            rebound["_cache_source_file"] = str(path)
            return rebound
    return None


def render_semantic_review_report(result: dict[str, Any]) -> str:
    findings = result.get("findings", [])
    interface_contract = result.get("interface_contract", {})
    downstream_adequacy = result.get("downstream_adequacy", {})
    obligation_review = result.get("obligation_review", {})
    forbidden_weakenings = result.get("forbidden_weakenings", [])
    reviewer_independence = result.get("reviewer_independence", {})
    lines = [
        f"# Semantic Review Report for {result.get('task_id', '')}",
        "",
        f"- Verdict: `{result.get('verdict', 'inconclusive')}`",
        f"- Proof class: `{result.get('proof_class', '')}`",
        f"- Completion class: `{result.get('completion_class', '')}`",
        f"- Needs class normalization: `{bool(result.get('needs_class_normalization', False))}`",
        f"- Task status: `{result.get('task_status', '')}`",
        f"- Confidence: `{result.get('confidence', '')}`",
        f"- Recommended disposition: `{result.get('recommended_disposition', '')}`",
        f"- Cache hit: `{bool(result.get('cache_hit', False))}`",
        "",
        "## Summary",
        "",
        str(result.get("summary", "")).strip() or "(no summary)",
        "",
        "## Reviewer Independence",
        "",
        f"- Role: `{reviewer_independence.get('role', 'unknown') if isinstance(reviewer_independence, dict) else 'unknown'}`",
        f"- Read-only: `{bool(reviewer_independence.get('read_only', False)) if isinstance(reviewer_independence, dict) else False}`",
        f"- Edited candidate: `{bool(reviewer_independence.get('did_edit_candidate', True)) if isinstance(reviewer_independence, dict) else True}`",
        f"- Used current request: `{bool(reviewer_independence.get('used_current_review_request', False)) if isinstance(reviewer_independence, dict) else False}`",
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
