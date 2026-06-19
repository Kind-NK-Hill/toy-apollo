from __future__ import annotations

import json
import re
import shutil
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from .phase2_pack_shared.io import read_file_safely, read_json_safely, sha256_text, write_json


SCHEMA_VERSION = "phase2.semantic_fail_triage.v1"
TRIAGE_PREFIX = "semantic_fail_triage"
TRIAGE_ALIAS = "semantic_fail_triage.json"
DIAGNOSER_PROMPT_PREFIX = "prepared_diagnoser_prompt"
DIAGNOSER_PROMPT_ALIAS = "prepared_diagnoser_prompt.txt"
MAX_PROMPT_SECTION_CHARS = 12_000
MAX_COMPACT_TEXT_CHARS = 4_000


def _compact(text: Any, limit: int = MAX_COMPACT_TEXT_CHARS) -> str:
    value = str(text or "").strip()
    if len(value) <= limit:
        return value
    return value[:limit].rstrip() + "\n[truncated]"


def _as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    try:
        return json.dumps(value, ensure_ascii=False, sort_keys=True)
    except TypeError:
        return str(value)


def _collect_review_text(review_result: dict[str, Any]) -> str:
    chunks: list[str] = []
    for key in (
        "verdict",
        "summary",
        "proof_class",
        "completion_class",
        "recommended_disposition",
        "normalization_reason",
    ):
        value = review_result.get(key)
        if value:
            chunks.append(f"{key}: {_as_text(value)}")
    for key in (
        "findings",
        "spine_alignment",
        "interface_contract",
        "obligation_review",
        "evidence_review",
        "downstream_adequacy",
        "forbidden_weakenings",
    ):
        value = review_result.get(key)
        if value:
            chunks.append(f"{key}: {_as_text(value)}")
    return "\n".join(chunks).lower()


def _contains_any(text: str, patterns: tuple[str, ...]) -> bool:
    return any(pattern in text for pattern in patterns)


def classify_semantic_failure(review_result: dict[str, Any]) -> tuple[str, str, bool]:
    """Return (category, reason, route_diagnosis_needed_before_state_gate)."""

    text = _collect_review_text(review_result)
    verdict = str(review_result.get("verdict", "") or "").strip().lower()
    proof_class = str(review_result.get("proof_class", "") or "").strip().lower()
    completion_class = str(review_result.get("completion_class", "") or "").strip().lower()
    class_text = f"{proof_class} {completion_class}"

    lean_engineering_patterns = (
        "syntax error",
        "unknown identifier",
        "missing import",
        "import error",
        "type mismatch",
        "typeclass",
        "type class",
        "api mismatch",
        "wrong number of arguments",
        "application type mismatch",
        "failed to synthesize",
    )
    if _contains_any(text, lean_engineering_patterns):
        return "lean_engineering", "Review failure reads as a Lean/API/build repair issue.", False

    accepted_route_missing_step = (
        ("accepted route" in text or "route accepted" in text or "within an accepted route" in text)
        and _contains_any(
            text,
            (
                "medium lemma",
                "medium step",
                "small lemma",
                "missing lemma",
                "remaining lemma",
                "missing step",
            ),
        )
    )
    if accepted_route_missing_step:
        return "missing_step", "Reviewer reports a missing small/medium step inside an accepted route.", False

    if _contains_any(
        class_text + "\n" + text,
        (
            "statement_mismatch",
            "source_mismatch",
            "statement mismatch",
            "source mismatch",
            "stronger than the textbook",
            "weaker than the textbook",
            "wrong statement",
            "source statement",
            "not source-faithful",
            "not textbook loyal",
        ),
    ):
        return "statement_or_source_mismatch", "Review indicates source or public statement mismatch.", True

    if _contains_any(
        class_text + "\n" + text,
        (
            "mathlib_backed_adapter",
            "adapter-only",
            "adapter only",
            "source_route_mismatch_adapter",
            "mathlib adapter",
            "adapter route",
        ),
    ):
        return "mathlib_adapter", "Review indicates a Mathlib-backed adapter/source-route mismatch.", True

    if _contains_any(
        class_text + "\n" + text,
        (
            "public-premise relocation",
            "public premise relocation",
            "premise relocation",
            "relocated to a public premise",
            "new public premise",
            "public setup field",
            "public setup fields",
            "caller-supplied public field",
            "caller supplied public field",
        ),
    ):
        return "public_premise", "Review indicates a core obligation was moved into a public premise.", True

    if _contains_any(
        class_text + "\n" + text,
        (
            "private axiom",
            "private_axiom",
            "open_math_debt",
            "open math debt",
            "hidden debt",
            "proof debt",
            "core proof burden",
        ),
    ):
        return "private_axiom_or_open_math_debt", "Review indicates private axiom, hidden debt, or open math debt.", True

    if _contains_any(
        text,
        (
            "wrong route",
            "route is wrong",
            "route still wrong",
            "not the textbook route",
            "not a textbook route",
            "not the source route",
            "proof spine is wrong",
            "cannot continue this route",
            "route problem",
        ),
    ):
        return "wrong_route", "Review says the proof route itself is wrong.", True

    if verdict in {"fail", "inconclusive"}:
        return "unclear_semantic_failure", "Semantic failure is not clearly ordinary Lean repair; default to one diagnosis.", True
    return "not_a_semantic_failure", "Review verdict is not fail/inconclusive.", False


def _list_previous_triages(pack_dir: Path) -> list[dict[str, Any]]:
    triages: list[dict[str, Any]] = []
    for path in sorted(pack_dir.glob(f"{TRIAGE_PREFIX}_v*.json")):
        payload = read_json_safely(path, {})
        if isinstance(payload, dict):
            triages.append(payload)
    return triages


def _second_diagnoser_override_reason(review_result: dict[str, Any]) -> str:
    text = _collect_review_text(review_result)
    if _contains_any(
        text,
        (
            "post-diagnosis route still wrong",
            "post diagnosis route still wrong",
            "new route still wrong",
            "diagnosed route still wrong",
            "route still wrong",
        ),
    ):
        return "reviewer_says_post_diagnosis_route_still_wrong"
    if _contains_any(
        text,
        (
            "local verification disproves",
            "local verification disproved",
            "rg disproves",
            "#check disproves",
            "diagnosis disproved",
            "diagnoser was wrong",
        ),
    ):
        return "local_verification_disproves_first_diagnosis"
    return ""


def _diagnoser_state(
    *,
    category: str,
    base_needs_diagnoser: bool,
    previous_triages: list[dict[str, Any]],
    review_result: dict[str, Any],
) -> tuple[bool, bool, str, str, list[str]]:
    previous_diagnoser_triages = [
        item for item in previous_triages if bool(item.get("needs_diagnoser", False))
    ]
    previous_categories = [
        str(item.get("category", "") or "").strip()
        for item in previous_diagnoser_triages
        if str(item.get("category", "") or "").strip()
    ]
    if not base_needs_diagnoser:
        state = "not_required_missing_step" if category == "missing_step" else "not_required_lean_repair"
        return False, False, state, "", previous_categories
    if not previous_diagnoser_triages:
        return True, False, "prompt_generated", "", previous_categories
    override = _second_diagnoser_override_reason(review_result)
    if category and category not in set(previous_categories):
        return True, True, "second_prompt_generated_new_category", "new_failure_category", previous_categories
    if override:
        return True, True, "second_prompt_generated_route_recheck", override, previous_categories
    return False, False, "already_diagnosed_continue_repair", "", previous_categories


def _candidate_declarations(candidate_code: str) -> str:
    decl_re = re.compile(
        r"(?ms)^\s*(?:@[^\n]+\n\s*)*(?:noncomputable\s+)?(?:theorem|lemma|def|axiom)\s+[^\n]*?(?=\s*:=|\s*\bwhere\b)"
    )
    snippets = [match.group(0).strip() for match in decl_re.finditer(candidate_code)]
    if not snippets:
        return "(no declaration headers found)"
    return _compact("\n\n".join(snippets), MAX_PROMPT_SECTION_CHARS)


def _safe_pack_file(pack_dir: Path, name: str, limit: int = MAX_PROMPT_SECTION_CHARS) -> str:
    path = pack_dir / name
    if not path.exists():
        return ""
    return _compact(read_file_safely(path), limit)


def _render_diagnoser_prompt(
    *,
    task: dict[str, Any],
    pack_dir: Path,
    triage_result: dict[str, Any],
    review_input: dict[str, Any],
    review_result: dict[str, Any],
    repair_request: dict[str, Any],
    failed_review_subject_file: Path,
) -> str:
    candidate_code = read_file_safely(failed_review_subject_file)
    search_notes = _safe_pack_file(pack_dir, "search_notes.md")
    dependency_context = _safe_pack_file(pack_dir, "dependency_decision_context.md")
    proof_obligations = _safe_pack_file(pack_dir, "proof_obligations.json")
    review_basis = review_input.get("review_basis", {}) if isinstance(review_input.get("review_basis", {}), dict) else {}
    lines = [
        f"# Phase2 Semantic-Fail Diagnoser Prompt for {task.get('block_id', '')}",
        "",
        "You are an independent read-only Phase2 route/source/statement diagnoser.",
        "",
        "## Hard Rules",
        "",
        "- Do not edit Lean files, ToyApollo/Output, project_ledger.json, or review artifacts.",
        "- Do not run review-apply.",
        "- Diagnose the proof route/source statement only; do not act as the semantic reviewer.",
        "- Do not hallucinate Mathlib theorem names. If a theorem/API is not in the provided local evidence, mark it as needing local `rg`/`#check` verification.",
        "- Distinguish ordinary missing lemmas from wrong route, source mismatch, public-premise relocation, private axiom, or Mathlib adapter debt.",
        "",
        "## Requested Output",
        "",
        "Return JSON with fields:",
        "`diagnosis_verdict`, `route_wrong`, `statement_mismatch`, `local_repair_allowed`, "
        "`recommended_next_action`, `forbidden_shortcuts`, `required_local_checks`, and `rationale`.",
        "",
        "## Triage Result",
        "",
        "```json",
        json.dumps(triage_result, indent=2, ensure_ascii=False),
        "```",
        "",
        "## Textbook/Source Statement",
        "",
        _compact(task.get("content", ""), MAX_PROMPT_SECTION_CHARS) or "(no source content found)",
        "",
        "## Current Lean Subject",
        "",
        f"- File: `{failed_review_subject_file}`",
        f"- Hash: `{review_input.get('review_subject_hash', '') or review_input.get('candidate', {}).get('hash', '')}`",
        "",
        "### Declaration Headers",
        "",
        "```lean",
        _candidate_declarations(candidate_code),
        "```",
        "",
        "### Candidate Excerpt",
        "",
        "```lean",
        _compact(candidate_code, MAX_PROMPT_SECTION_CHARS),
        "```",
        "",
        "## Review Failure Detail",
        "",
        "```json",
        _compact(review_result, MAX_PROMPT_SECTION_CHARS),
        "```",
        "",
        "## Current Repair Contract",
        "",
        "```json",
        _compact(repair_request, MAX_PROMPT_SECTION_CHARS),
        "```",
        "",
        "## Review Basis Summary",
        "",
        "```json",
        _compact(
            {
                "review_subject_kind": review_input.get("review_subject_kind", ""),
                "review_basis_hash": review_input.get("review_basis_hash", ""),
                "allowed_abstractions": review_basis.get("allowed_abstractions", []),
                "forbidden_weakenings": review_basis.get("forbidden_weakenings", []),
                "direct_downstream_consumers": review_basis.get("direct_downstream_consumers", []),
            },
            MAX_PROMPT_SECTION_CHARS,
        ),
        "```",
    ]
    if dependency_context:
        lines.extend(["", "## Dependency Decision Context", "", dependency_context])
    if proof_obligations:
        lines.extend(["", "## Proof Obligations", "", "```json", proof_obligations, "```"])
    if search_notes:
        lines.extend(["", "## Local Search Notes", "", search_notes])
    lines.extend(
        [
            "",
            "## Decision Boundary",
            "",
            "- If this is only a missing small/medium lemma inside an accepted route, say `local_repair_allowed=true`.",
            "- If the public theorem statement is wrong, stronger/weaker than source, or the proof route hides the core task in Mathlib/public premises/private axioms, say `local_repair_allowed=false`.",
            "- If you need a Mathlib theorem that is not in the supplied evidence, list it under `required_local_checks`; do not assert it exists.",
        ]
    )
    return "\n".join(lines).rstrip() + "\n"


def write_semantic_fail_triage_artifacts(
    *,
    task: dict[str, Any],
    pack_dir: Path,
    review_input: dict[str, Any],
    review_result: dict[str, Any],
    repair_request: dict[str, Any],
    failed_review_subject_file: Path,
    attempt: int,
) -> dict[str, Any]:
    category, reason, base_needs = classify_semantic_failure(review_result)
    previous_triages = _list_previous_triages(pack_dir)
    needs_diagnoser, second_allowed, diagnosis_state, second_reason, previous_categories = _diagnoser_state(
        category=category,
        base_needs_diagnoser=base_needs,
        previous_triages=previous_triages,
        review_result=review_result,
    )
    triage_path = pack_dir / f"{TRIAGE_PREFIX}_v{attempt}.json"
    prompt_path = pack_dir / f"{DIAGNOSER_PROMPT_PREFIX}_v{attempt}.txt"
    triage_result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "task_id": task["block_id"],
        "created_at": datetime.now(UTC).isoformat(),
        "origin_review_attempt": int(review_input.get("attempt") or attempt),
        "review_verdict": str(review_result.get("verdict", "inconclusive") or "inconclusive"),
        "category": category,
        "reason": reason,
        "needs_diagnoser": needs_diagnoser,
        "local_repair_allowed": not needs_diagnoser,
        "second_diagnoser_allowed": second_allowed,
        "second_diagnoser_reason": second_reason,
        "diagnosis_state": diagnosis_state,
        "previous_diagnoser_count": len([item for item in previous_triages if bool(item.get("needs_diagnoser", False))]),
        "previous_diagnoser_categories": previous_categories,
        "review_result_file": str(review_result.get("review_result_file", "") or repair_request.get("failed_review_result_file", "")),
        "review_subject_file": str(failed_review_subject_file),
        "review_subject_hash": str(
            review_input.get("review_subject_hash", "")
            or review_input.get("candidate", {}).get("hash", "")
            or sha256_text(read_file_safely(failed_review_subject_file))
        ),
        "triage_path": str(triage_path),
        "prompt_path": str(prompt_path) if needs_diagnoser else "",
    }
    if needs_diagnoser:
        prompt_path.write_text(
            _render_diagnoser_prompt(
                task=task,
                pack_dir=pack_dir,
                triage_result=triage_result,
                review_input=review_input,
                review_result=review_result,
                repair_request=repair_request,
                failed_review_subject_file=failed_review_subject_file,
            ),
            encoding="utf-8",
        )
        alias_prompt = pack_dir / DIAGNOSER_PROMPT_ALIAS
        if alias_prompt.exists():
            alias_prompt.unlink()
        shutil.copyfile(prompt_path, alias_prompt)
        triage_result["prompt_alias_path"] = str(alias_prompt)
    write_json(triage_path, triage_result)
    alias_triage = pack_dir / TRIAGE_ALIAS
    if alias_triage.exists():
        alias_triage.unlink()
    shutil.copyfile(triage_path, alias_triage)
    triage_result["triage_alias_path"] = str(alias_triage)
    write_json(triage_path, triage_result)
    shutil.copyfile(triage_path, alias_triage)
    return triage_result
