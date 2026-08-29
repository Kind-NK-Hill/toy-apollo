from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any


AUDIT_DATE = "2026-05-19"
PROOF_DEBT_STATUS = "accepted_as_proof_debt"

DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
IGNORED_LANDING_TOKENS = {
    "Prop",
    "Type",
    "Sort",
    "True",
    "False",
    "Measure",
    "Set",
    "and",
    "applied",
    "to",
    "converts",
    "null",
    "the",
    "a",
    "an",
    "P",
    "X",
    "Y",
    "XT",
    "T",
    "Yn",
    "Xn",
    "mu",
    "nu",
    "c",
    "n",
    "i",
    "j",
    "x",
    "y",
    "z",
}


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    path: Path
    line: int


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def scan_output_declarations(output_dir: Path) -> dict[str, Declaration]:
    declarations: dict[str, Declaration] = {}
    for path in sorted(output_dir.glob("*.lean")):
        for index, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
            match = DECL_RE.match(line)
            if not match:
                continue
            name = match.group("name")
            declarations[name] = Declaration(name=name, kind=match.group("kind"), path=path, line=index)
    return declarations


def landing_names(raw: str, declarations: dict[str, Declaration]) -> list[str]:
    names: list[str] = []
    for chunk in re.split(r"[,;\n]+", raw or ""):
        chunk = chunk.strip()
        if not chunk:
            continue
        if ":" in chunk:
            left, right = chunk.split(":", 1)
            left_tokens = IDENT_RE.findall(left)
            if left_tokens:
                names.append(left_tokens[-1])
            right_tokens = IDENT_RE.findall(right)
            if right_tokens:
                names.append(right_tokens[0])
            continue
        for token in IDENT_RE.findall(chunk):
            if _ignore_landing_token(token, declarations):
                continue
            names.append(token)
    deduped: list[str] = []
    seen: set[str] = set()
    for name in names:
        if name in seen:
            continue
        seen.add(name)
        deduped.append(name)
    return deduped


def _ignore_landing_token(token: str, declarations: dict[str, Declaration]) -> bool:
    if token in IGNORED_LANDING_TOKENS:
        return True
    if len(token) == 1:
        return True
    if token in declarations:
        return False
    if token.startswith("h_") or (token.startswith("h") and len(token) > 1 and token[1].isupper()):
        return False
    if "." in token or "_" in token:
        return False
    if token[:1].islower():
        return True
    return False


def family_for(task_id: str, obligation: dict[str, Any]) -> str:
    text = " ".join(
        str(obligation.get(key, "") or "")
        for key in ("id", "title", "kind", "source_ref", "lean_landing", "notes")
    ).lower()
    combined = f"{task_id} {text}"
    if any(term in combined for term in ("quantile", "skorokhod", "inverse")):
        return "quantile/skorokhod"
    if any(term in combined for term in ("characteristic", "levy", "mgf", "gamma")):
        return "characteristic/levy/mgf"
    if any(term in combined for term in ("density", "radon", "nikodym", "total variation", "triangle")):
        return "tv/rn/density"
    if any(term in combined for term in ("tail", "moment", "variance", "covariance", "summability", "uniform")):
        return "tail/moment/ui"
    if any(term in combined for term in ("fubini", "dominated", "integral", "pi-lambda", "rectangle", "area")):
        return "measure/fubini/dct"
    if any(term in combined for term in ("cdf", "weak", "distribution", "law", "continuity point")):
        return "cdf/weak/law"
    if any(term in combined for term in ("clt", "lyapunov", "lindeberg", "triangular")):
        return "clt/triangular"
    if any(term in combined for term in ("martingale", "stopping")):
        return "martingale/stopping"
    return "other"


def next_action_for(audit_class: str) -> str:
    if audit_class == "A_existing_theorem_candidate":
        return "Check theorem hypotheses; retire the debt only if the declaration does not carry an equivalent support assumption."
    if audit_class == "B_partial_theorem_plus_support_interface":
        return "Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas."
    if audit_class == "B_partial_theorem_plus_missing_or_support":
        return "Use the existing theorem part; split or replace each missing support landing with a source lemma or interface translation."
    if audit_class in {"C_support_predicate_or_structure_only", "C_support_field_gap_no_decl"}:
        return "Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence."
    return "Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair."


def classify_alignment(names: list[str], declarations: dict[str, Declaration]) -> tuple[str, list[Declaration], list[str]]:
    existing: list[Declaration] = []
    missing: list[str] = []
    for name in names:
        declaration = declarations.get(name)
        if declaration is None:
            missing.append(name)
        else:
            existing.append(declaration)

    if not names:
        return "D_no_landing_search_required", existing, missing

    proof_like = [decl for decl in existing if decl.kind in {"theorem", "lemma"}]
    support_like = [decl for decl in existing if decl.kind in {"def", "abbrev", "structure", "inductive", "class"}]

    if existing and not missing and len(proof_like) == len(existing):
        return "A_existing_theorem_candidate", existing, missing
    if proof_like and support_like and not missing:
        return "B_partial_theorem_plus_support_interface", existing, missing
    if proof_like and (missing or support_like):
        return "B_partial_theorem_plus_missing_or_support", existing, missing
    if support_like and not missing:
        return "C_support_predicate_or_structure_only", existing, missing
    if missing:
        if any(name.startswith("h") or name.endswith("_support") or "." in name for name in missing):
            return "C_support_field_gap_no_decl", existing, missing
        return "D_landing_names_missing", existing, missing
    return "D_no_landing_search_required", existing, missing


def rel(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def alignment_payload(
    root: Path,
    task_id: str,
    obligation: dict[str, Any],
    declarations: dict[str, Declaration],
) -> dict[str, Any]:
    names = landing_names(str(obligation.get("lean_landing", "") or ""), declarations)
    audit_class, existing, missing = classify_alignment(names, declarations)
    return {
        "audited_at": AUDIT_DATE,
        "audit_class": audit_class,
        "family": family_for(task_id, obligation),
        "existing_local_declarations": [
            {
                "name": decl.name,
                "kind": decl.kind,
                "file": rel(decl.path, root),
                "line": decl.line,
            }
            for decl in existing
        ],
        "missing_landing_names": missing,
        "next_action": next_action_for(audit_class),
        "manual_review_required": audit_class.startswith("A_") or audit_class.startswith("B_"),
    }


def iter_proof_obligations(root: Path) -> list[Path]:
    return sorted((root / "phase2_prompt_packs").glob("*/proof_obligations.json"))


def collect_rows(root: Path, declarations: dict[str, Declaration]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in iter_proof_obligations(root):
        payload = read_json(path)
        if not isinstance(payload, dict):
            continue
        task_id = str(payload.get("task_id", "") or path.parent.name)
        for obligation in payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []:
            if not isinstance(obligation, dict):
                continue
            if str(obligation.get("status", "") or "").strip() != PROOF_DEBT_STATUS:
                continue
            alignment = alignment_payload(root, task_id, obligation, declarations)
            rows.append(
                {
                    "task_id": task_id,
                    "obligation_id": str(obligation.get("id", "") or ""),
                    "title": str(obligation.get("title", "") or ""),
                    "source_ref": str(obligation.get("source_ref", "") or ""),
                    "lean_landing": str(obligation.get("lean_landing", "") or ""),
                    "alignment": alignment,
                }
            )
    return rows


def apply_alignment_metadata(root: Path, declarations: dict[str, Declaration]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for path in iter_proof_obligations(root):
        payload = read_json(path)
        if not isinstance(payload, dict):
            continue
        task_id = str(payload.get("task_id", "") or path.parent.name)
        changed = False
        for obligation in payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []:
            if not isinstance(obligation, dict):
                continue
            if str(obligation.get("status", "") or "").strip() != PROOF_DEBT_STATUS:
                continue
            alignment = alignment_payload(root, task_id, obligation, declarations)
            obligation["source_output_alignment"] = alignment
            counts[alignment["audit_class"]] += 1
            changed = True
        if changed:
            payload["source_output_alignment_audit"] = {
                "audited_at": AUDIT_DATE,
                "accepted_debt_count": sum(1 for _ in _accepted_debt_items(payload)),
                "status": "metadata_attached",
            }
            write_json(path, payload)
    return counts


def _accepted_debt_items(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        item
        for item in payload.get("obligations", [])
        if isinstance(item, dict) and str(item.get("status", "") or "").strip() == PROOF_DEBT_STATUS
    ]


def format_decl_list(decls: list[dict[str, Any]]) -> str:
    if not decls:
        return "-"
    return "<br>".join(
        f"`{decl['name']}` ({decl['kind']}, `{decl['file']}:{decl['line']}`)" for decl in decls
    )


def render_markdown(root: Path, rows: list[dict[str, Any]]) -> str:
    class_counts = Counter(str(row["alignment"]["audit_class"]) for row in rows)
    family_counts = Counter(str(row["alignment"]["family"]) for row in rows)
    lines = [
        "# Phase 2 Source-Output Alignment Audit",
        "",
        f"Snapshot date: {AUDIT_DATE}.",
        "",
        "Purpose: convert every accepted proof-debt gap into one of four concrete actions: import an existing theorem, write a narrow interface translation, formalize the source proof step locally, or keep only a verified external/foundation gap.",
        "",
        "## Classification Rules",
        "",
        "- `A_existing_theorem_candidate`: all recorded landing names resolve to theorem/lemma declarations. These are the first candidates for import/rewrite and debt retirement, but their hypotheses still need review.",
        "- `B_partial_theorem_plus_support_interface`: at least one theorem/lemma exists, but the landing also contains definitions or structures. Use the theorem part, then formalize the remaining source step.",
        "- `B_partial_theorem_plus_missing_or_support`: at least one theorem/lemma exists, but another recorded landing name is missing, usually a support assumption or structure field. This is not clean until the missing part is replaced.",
        "- `C_support_predicate_or_structure_only`: the recorded landing is only a support predicate, structure, definition, or field. This is not a cleared proof; replace it by theorem-level evidence.",
        "- `D_no_landing_search_required` / `D_landing_names_missing`: no usable local landing is recorded or found. Re-open source/output search before accepting it as real debt.",
        "",
        "## Counts",
        "",
        f"- Total accepted debt items: {len(rows)}",
    ]
    for key in sorted(class_counts):
        lines.append(f"- {key}: {class_counts[key]}")
    lines.extend(["", "## Family Counts", ""])
    for key in sorted(family_counts):
        lines.append(f"- {key}: {family_counts[key]}")
    lines.extend(
        [
            "",
            "## Manual Follow-up Notes",
            "",
            "- `ex_13_6_5.optional_stopping_zero_gain` and `ex_13_6_5.expected_waiting_times` have theorem landings, but signature inspection shows they still carry model-specific hypotheses such as `hThirdCase`, `hInitialGainZero`, and terminal payoff integral identities. Treat them as interface/source-formalization work, not clean debt retirement.",
            "- `prob_10_10.constant_distribution_to_probability` can import `prob_10_3`, but `prob_10_3` itself still requires `h_constant_bridge`; this is a partial source-output alignment, not a completed proof.",
            "- `thm_10_8.quantile_law_preservation` already has the CDF-to-law bridge in `thm_10_8_quantile_law.lean`; the remaining work is the source event calculation and measurability needed to feed that bridge.",
            "",
            "## Audit Table",
            "",
            "| task.obligation | family | classification | existing local declarations | missing landing names | next action |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in sorted(rows, key=lambda item: (item["task_id"], item["obligation_id"])):
        alignment = row["alignment"]
        task_obligation = f"{row['task_id']}.{row['obligation_id']}"
        missing = ", ".join(f"`{name}`" for name in alignment["missing_landing_names"]) or "-"
        lines.append(
            f"| `{task_obligation}` | {alignment['family']} | `{alignment['audit_class']}` | "
            f"{format_decl_list(alignment['existing_local_declarations'])} | {missing} | {alignment['next_action']} |"
        )
    lines.extend(
        [
            "",
            "## Immediate Queue",
            "",
            "Start with `A_existing_theorem_candidate` and both `B_partial_*` classes, but do not mark any item proved merely because a symbol exists. The declaration must actually discharge the source obligation without carrying an equivalent support assumption.",
            "",
            "This audit is also attached back to each accepted debt item as `source_output_alignment`, so debt-fix prompts can act on every existing gap rather than rediscovering this classification manually.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit accepted Phase 2 proof debt against local output declarations.")
    parser.add_argument("--apply", action="store_true", help="Write source_output_alignment metadata into proof_obligations.json files.")
    parser.add_argument("--write-doc", action="store_true", help="Regenerate docs/phase2_source_output_alignment_audit.md.")
    args = parser.parse_args()

    root = repo_root()
    declarations = scan_output_declarations(root / "ToyApollo" / "Output")
    rows = collect_rows(root, declarations)
    if args.apply:
        apply_alignment_metadata(root, declarations)
    if args.write_doc:
        doc_path = root / "docs" / "phase2_source_output_alignment_audit.md"
        doc_path.write_text(render_markdown(root, rows), encoding="utf-8")
    class_counts = Counter(str(row["alignment"]["audit_class"]) for row in rows)
    print(json.dumps({"accepted_debt_count": len(rows), "class_counts": dict(sorted(class_counts.items()))}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
