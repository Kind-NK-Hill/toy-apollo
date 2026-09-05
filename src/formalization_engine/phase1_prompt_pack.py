"""Phase 1 operator-driven prompt-pack workflow.

This module replaces the old inline LLM call with an agent-driven
operator-driven workflow:

  1. ``write_phase1_pack`` — reads a ``.tex`` file and generates a prompt-pack
     directory containing the raw input, an operator prompt, and an empty
     ``draft_plan.json``.

  2. agent decompose — a Codex/agent step reads ``input.tex`` and fills
     ``draft_plan.json`` with formalization tasks.

  3. ``apply_phase1_pack`` — reads back the agent-authored ``draft_plan.json``,
     validates and normalises it (block-id canonicalisation, ``is_renowned``
     tagging, etc.), registers the tasks in the project ledger, and writes the
     final ``plans/*_plan.json``.
"""

from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any

from formalization_engine.block_id_naming import (
    canonicalize_block_id,
    canonicalize_task_dict,
    is_canonical_block_id,
)
from formalization_engine.phase1_plan_audit import (
    normalize_phase1_task_type,
    validate_phase1_plan_structure,
)
from formalization_engine.dependency_decisions import DependencyDecision, record_dependency_decision

from .core import LedgerManager, Settings

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_RENOWNED_KEYWORDS: list[str] = [
    "Hahn-Kolmogorov",
    "Heine-Borel",
    "Caratheodory",
    "Pi-Lambda",
    "Dynkin",
    "Monotone Class",
    "Lebesgue-Stieltjes",
    "Fatou",
    "Monotone Convergence",
    "Dominated Convergence",
    "Borel-Cantelli",
]

_SUBSECTION_RE = re.compile(r"\\subsection\*?\{([^}]*)\}")

_OPERATOR_PROMPT_TEMPLATE = r"""# Phase 1 Operator Prompt

## Purpose

You are decomposing a section of a mathematics textbook (LaTeX) into a
strictly sequential list of Lean 4 formalization tasks.

## Workflow

Phase 1 pack has already prepared this directory. It does not mean the
LaTeX has already been decomposed.

Your current step is agent decompose:

1. Read `input.tex`.
2. Split the textbook content into formalization task blocks.
3. Write those task blocks to `draft_plan.json`.

Phase 1 apply will run later. It only validates and registers the
agent-authored `draft_plan.json`; it does not perform decomposition.

## Input

The raw LaTeX source is in `input.tex` inside this pack directory.

## Source Unit Rule

Each Phase 1 input must be one source unit:

- one numbered textbook subsection, optionally preceded by chapter intro text; or
- one problems section.

Do not decompose a whole chapter or multiple numbered subsections into one
`draft_plan.json`.  Use separate input files and separate Phase 1 plans instead.

## Output

Edit `draft_plan.json` in this directory.  It must be a strictly valid JSON
list of objects.  Each object MUST have:

- `"block_id"`: A unique string ID following canonical grammar:
  `intro_<ch>`, `intro_<ch>_<sec>`, `rem_<ch>_<sec>_<slug>`,
  `def_<ch>_<num>`, `def_<ch>_<sec>_<slug>`, `thm_<ch>_<num>`,
  `ex_<ch>_<sec>_<num>`, `ex_<ch>_<sec>_<slug>`, `prob_<ch>_<num>`.
- `"type"`: One of: `Definition`, `Theorem_Statement`, `Theorem_with_Proof`,
  `Lemma`, `Corollary`, `Example_Proof`, `Problem`, `Remark`.
- `"title"`: A short human-readable title.
- `"content"`: The EXACT LaTeX text corresponding to this block.
- `"dependencies"`: A list of `block_id` strings that this block
  explicitly references or relies on.

## Categories

1. **Definition** — Mathematical definitions.
2. **Theorem_Statement** — Major theorems that DO NOT have a proof in the
   text, OR a theorem statement whose proof appears much later.
3. **Theorem_with_Proof** — A theorem or lemma immediately followed by its
   proof.  Combine them into a SINGLE block.
4. **Lemma** — A numbered lemma, including its immediately following proof.
5. **Corollary** — A numbered corollary, including its immediately following proof.
6. **Example_Proof** — Specific examples, calculations, or a "Delayed Proof"
   (e.g., "Proof of Theorem 3.3") that appears long after its statement.
7. **Problem** — Exercises.
8. **Remark** — Conversational text.

## Critical Dependency Rules for Delayed Proofs

If you encounter a proof for a theorem stated earlier (e.g., "Proof of
Theorem 3.3" appearing after Def 3.6, Thm 3.4, etc.):

- Classify it as `Example_Proof`.
- Its `dependencies` MUST include the `block_id` of the original
  `Theorem_Statement`.
- Its `dependencies` MUST also include any intermediate lemmas/definitions
  used in the proof.

## JSON Escaping

Because the `content` field contains LaTeX, you MUST double-escape all
backslashes in the JSON string.  For example, `\mathbb{R}` MUST be written
as `\\mathbb{R}` in the JSON output.

## Ordering

Tasks must appear in strict textbook order (top-down dependency order for
Lean 4).

## Existing Plan Reference

{existing_plan_note}
"""

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _clean_json_string(raw_text: str) -> str:
    """Strip markdown fences and fix common LLM JSON escaping issues."""
    if "```json" in raw_text:
        raw_text = raw_text.split("```json")[1].split("```")[0]
    elif "```" in raw_text:
        raw_text = raw_text.replace("```", "")
    fixed_text = re.sub(r'(?<!\\)\\(?!["\\/bfnrt])', r"\\\\", raw_text)
    return fixed_text.strip()


def _tag_renowned(block: dict[str, Any]) -> None:
    """Set ``is_renowned`` flag based on keyword matching."""
    content = block.get("content", "")
    title = block.get("title", "")
    if any(
        kw.lower() in content.lower() or kw.lower() in title.lower()
        for kw in _RENOWNED_KEYWORDS
    ):
        block["is_renowned"] = True
    else:
        block["is_renowned"] = False


def _inject_cross_references(blocks: list[dict[str, Any]]) -> dict[str, dict[str, str]]:
    """Scan block content for standard textbook references and inject as explicit dependencies."""
    patterns = [
        (re.compile(r"(?:Theorem|Lemma)\s+(\d+)\.(\d+)"), "thm_{0}_{1}"),
        (re.compile(r"(?:Definition|Def\.|Def)\s+(\d+)\.(\d+)"), "def_{0}_{1}"),
        (re.compile(r"Example\s+(\d+)\.(\d+)\.(\d+)"), "ex_{0}_{1}_{2}"),
        (re.compile(r"Example\s+(\d+)\.(\d+)(?!\.)"), "ex_{0}_{1}"),
        (re.compile(r"Problem\s+(\d+)\.(\d+)"), "prob_{0}_{1}"),
    ]
    injected_evidence: dict[str, dict[str, str]] = {}

    for block in blocks:
        task_type = str(block.get("type", "")).strip()
        if task_type not in (
            "Problem",
            "Theorem_Statement",
            "Theorem_with_Proof",
            "Lemma",
            "Corollary",
            "Definition",
            "Example_Proof",
        ):
            continue

        content = block.get("content", "")
        if not content:
            continue

        current_id = block.get("block_id", "")
        deps = list(block.get("dependencies") or [])

        injected: dict[str, str] = {}
        for pattern, fmt in patterns:
            for match in pattern.finditer(content):
                target_id = fmt.format(*match.groups())
                if current_id.startswith(target_id):
                    continue
                if target_id not in deps and target_id not in injected:
                    injected[target_id] = match.group(0)

        if injected:
            for dep_id in sorted(injected):
                deps.append(dep_id)
            injected_evidence[current_id] = {dep_id: injected[dep_id] for dep_id in sorted(injected)}
            block["dependencies"] = deps
    return injected_evidence


def _record_phase1_dependency_decisions(
    blocks: list[dict[str, Any]],
    injected_evidence: dict[str, dict[str, str]],
    settings: Settings,
    plan_file: Path,
    source_plan: str,
) -> None:
    profile = str(getattr(settings, "profile", "mat") or "mat")
    for block in blocks:
        task_id = canonicalize_block_id(str(block.get("block_id", "")), profile)
        if not task_id:
            continue
        injected_for_task = injected_evidence.get(task_id, {})
        for dep_id in block.get("dependencies") or []:
            canonical_dep = canonicalize_block_id(str(dep_id), profile)
            if not canonical_dep:
                continue
            if canonical_dep in injected_for_task:
                criterion = "explicit_text_reference"
                evidence = injected_for_task[canonical_dep]
            else:
                criterion = "operator_declared_reliance"
                evidence = "Declared in draft_plan.json dependencies"
            record_dependency_decision(
                settings,
                DependencyDecision(
                    task_id=task_id,
                    dep_id=canonical_dep,
                    kind="hard",
                    phase="phase1_apply",
                    criterion=criterion,
                    evidence=evidence,
                    source_plan=source_plan,
                    source_file=str(plan_file),
                ),
            )


def _base_name(tex_path: Path) -> str:
    return os.path.splitext(tex_path.name)[0]


def _phase1_source_unit_error(tex_content: str) -> str:
    subsection_titles = [match.group(1).strip() for match in _SUBSECTION_RE.finditer(tex_content)]
    numbered = [title for title in subsection_titles if re.match(r"^\d+\.\d+(?:\b|\s)", title)]
    problems = [title for title in subsection_titles if title.strip().lower() == "problems"]

    if len(numbered) > 1:
        return (
            "Phase 1 expects one subsection per Phase 1 input; found multiple "
            f"numbered subsections: {', '.join(numbered)}"
        )
    if numbered and problems:
        return (
            "Phase 1 expects problems to be a separate source unit; found a "
            "numbered subsection and a Problems section in the same input."
        )
    return ""


def _validate_phase1_source_unit(tex_content: str, tex_file: Path) -> None:
    error = _phase1_source_unit_error(tex_content)
    if error:
        raise ValueError(f"{tex_file}: {error}")


def _load_phase1_input_tex(pack_dir: Path, tex_file: Path) -> tuple[bool, str]:
    candidates = [pack_dir / "input.tex", tex_file]
    for candidate in candidates:
        if candidate.exists():
            with open(candidate, "r", encoding="utf-8") as handle:
                return True, handle.read()
    return False, ""


def _format_apply_failure(
    source_plan: str,
    messages: list[str],
) -> str:
    details = "; ".join(messages)
    return (
        f"{source_plan}: {details} "
        "Please fix draft_plan.json in the phase1 prompt pack and re-apply."
    )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def write_phase1_pack(
    tex_file: Path,
    settings: Settings,
) -> Path:
    """Generate a Phase 1 prompt-pack directory for *tex_file*.

    Returns the path to the generated pack directory.
    """
    packs_root = settings.phase1_prompt_packs_dir
    assert packs_root is not None
    base = _base_name(tex_file)

    with open(tex_file, "r", encoding="utf-8") as f:
        latex_content = f.read()
    _validate_phase1_source_unit(latex_content, tex_file)

    pack_dir = packs_root / base
    pack_dir.mkdir(parents=True, exist_ok=True)

    # 1. Copy the raw input
    input_dst = pack_dir / "input.tex"
    with open(input_dst, "w", encoding="utf-8") as f:
        f.write(latex_content)

    # 2. Check for an existing plan to use as reference
    plan_file = settings.plans_dir / f"{base}_plan.json"
    if plan_file.exists():
        existing_plan_note = (
            f"An existing plan for this file is available at:\n"
            f"  `{plan_file}`\n\n"
            f"You may use it as a reference, but your `draft_plan.json` will\n"
            f"be validated and normalised independently."
        )
    else:
        existing_plan_note = "No existing plan found for this file."

    # 3. Write operator prompt
    prompt_text = _OPERATOR_PROMPT_TEMPLATE.replace(
        "{existing_plan_note}", existing_plan_note
    )
    with open(pack_dir / "operator_prompt.md", "w", encoding="utf-8") as f:
        f.write(prompt_text)

    # 4. Write empty draft if it does not already exist (preserve operator edits)
    draft_path = pack_dir / "draft_plan.json"
    if not draft_path.exists():
        with open(draft_path, "w", encoding="utf-8") as f:
            f.write("[]\n")

    print(f"📦 [Phase 1] Prompt pack generated: {pack_dir}")
    return pack_dir


def apply_phase1_pack(
    tex_file: Path,
    ledger: LedgerManager,
    settings: Settings,
) -> tuple[bool, str, list[str]]:
    """Validate and apply an agent-authored ``draft_plan.json``.

    Returns ``(success, detail_message, found_block_ids)``.
    """
    packs_root = settings.phase1_prompt_packs_dir
    assert packs_root is not None
    base = _base_name(tex_file)
    pack_dir = packs_root / base

    draft_path = pack_dir / "draft_plan.json"
    if not draft_path.exists():
        return False, f"draft_plan.json not found at {draft_path}", []

    # ---- Read & clean ----
    with open(draft_path, "r", encoding="utf-8") as f:
        raw_text = f.read()

    clean_text = _clean_json_string(raw_text)
    try:
        blocks = json.loads(clean_text)
    except json.JSONDecodeError as e:
        return False, f"JSON parse error in draft_plan.json: {e}", []

    if not isinstance(blocks, list):
        return False, "draft_plan.json must be a JSON list.", []

    input_ok, tex_content = _load_phase1_input_tex(pack_dir, tex_file)
    if not input_ok:
        return (
            False,
            f"{base}: input.tex not found in prompt pack and source tex file is missing. Please regenerate the phase1 pack.",
            [],
        )
    try:
        _validate_phase1_source_unit(tex_content, tex_file)
    except ValueError as exc:
        return False, str(exc), []

    # ---- Normalise ----
    profile = str(getattr(settings, "profile", "mat") or "mat")
    normalized_blocks: list[dict[str, Any]] = []
    normalization_notes: list[str] = []
    for index, b in enumerate(blocks, start=1):
        if not isinstance(b, dict):
            return (
                False,
                _format_apply_failure(
                    base,
                    [f"plan entry {index} is not a JSON object"],
                ),
                [],
            )
        b = canonicalize_task_dict(b, profile)
        normalized_type, note = normalize_phase1_task_type(b.get("type", ""), profile)
        bid = b.get("block_id", "")
        if normalized_type is None:
            return (
                False,
                _format_apply_failure(
                    base,
                    [
                        f"block {bid or index} uses invalid task type {b.get('type', '')!r}",
                    ],
                ),
                [],
            )
        if note:
            normalization_notes.append(note)
        b["type"] = normalized_type
        if not is_canonical_block_id(bid, profile):
            print(f"   ⚠️ [Phase 1 Apply] Non-canonical block_id preserved: {bid}")
        _tag_renowned(b)
        b["source_plan"] = base
        normalized_blocks.append(b)

    if not normalized_blocks:
        return (
            False,
            _format_apply_failure(
                base,
                ["draft_plan.json produced zero valid blocks after normalization"],
            ),
            [],
        )

    _, structure_findings = validate_phase1_plan_structure(
        source_plan=base,
        blocks=normalized_blocks,
        tex_content=tex_content,
    )
    structure_errors = [
        finding["message"]
        for finding in structure_findings
        if finding.get("severity") == "error"
    ]
    if structure_errors:
        return False, _format_apply_failure(base, structure_errors), []

    for note in normalization_notes:
        print(f"   ℹ️ [Phase 1 Apply] {note}")

    # ---- Inject Cross References ----
    injected_evidence = _inject_cross_references(normalized_blocks)

    # ---- Register in ledger ----
    for task in normalized_blocks:
        ledger.add_or_update_task(task)

    # ---- Write final plan ----
    settings.plans_dir.mkdir(parents=True, exist_ok=True)
    plan_file = settings.plans_dir / f"{base}_plan.json"
    with open(plan_file, "w", encoding="utf-8") as f:
        json.dump(normalized_blocks, f, indent=4, ensure_ascii=False)
    _record_phase1_dependency_decisions(
        normalized_blocks,
        injected_evidence,
        settings,
        plan_file,
        base,
    )

    found_ids = [t["block_id"] for t in normalized_blocks]
    detail = (
        f"✅ [Phase 1 Apply] {len(normalized_blocks)} blocks validated and written to {plan_file}"
    )
    print(detail)
    return True, detail, found_ids
