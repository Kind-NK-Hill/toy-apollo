#!/usr/bin/env python3
"""Build read-only Chapter reconciliation evidence from plans, Lean, reviews, and state.

The script never changes SQLite, Git, Lean sources, plans, or review artifacts.  It
writes a JSON evidence ledger and a compact Markdown report to the explicit output
paths supplied by the operator.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.block_id_naming import canonicalize_block_id, extract_chapter
from src.toy_apollo.core.settings import get_settings
from src.toy_apollo.phase1_plan_audit import normalize_phase1_task_type
from src.toy_apollo.state_reconcile import discover_formal_plan_task_ids, task_id_from_path
from src.toy_apollo.state_store import WorkspaceStateStore, sha256_file, utc_now


IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_'.]+)\s*$")
DECL_RE = re.compile(
    r"(?m)^(?P<indent>\s*)(?P<private>private\s+)?"
    r"(?:(?:noncomputable|protected)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|structure|class|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
ROUTE_LINE_RE = re.compile(
    r"\b(exact|apply|refine|simpa|simp|rw|rfl|constructor|ext|funext|unfold|"
    r"change|convert|calc|measurability|positivity|linarith|nlinarith|omega)\b|:=",
    re.IGNORECASE,
)
TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_'])[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*(?![A-Za-z0-9_'])")
FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "axiom": re.compile(r"(?m)^\s*(?:private\s+)?axiom\b"),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
}
KEYWORDS = {
    "by", "fun", "let", "in", "if", "then", "else", "match", "with", "where",
    "theorem", "lemma", "def", "abbrev", "opaque", "structure", "class", "instance",
    "private", "protected", "noncomputable", "namespace", "end", "open", "variable",
    "variables", "section", "include", "omit", "set_option", "true", "false", "type",
    "prop", "forall", "exists", "show", "from", "at", "only", "using", "as", "have",
    "suffices", "case", "next", "all_goals", "any_goals", "first", "repeat", "try",
}
FORMAL_TYPES = {
    "Definition",
    "Theorem_Statement",
    "Theorem_with_Proof",
    "Example_Proof",
    "Problem",
}


# The automatic API comparison below deliberately errs on the side of surfacing
# differences.  These entries record the source/review adjudication for every
# comparison whose public API shape alone is insufficient to decide the result.
# They are evidence annotations only: the script never copies or changes Lean.
MANUAL_KENNETH_ADJUDICATIONS: dict[str, dict[str, Any]] = {
    "thm_2_1": {
        "final_category": "kenneth_additive_decomposition_api",
        "source_conflict": False,
        "resolution": "The final theorem statement agrees; Kenneth additionally exposes part1/part2 wrappers.",
        "action": "Preserve Kenneth's additive API; require a fresh MAT review only if those wrappers are ported.",
    },
    "thm_2_7": {
        "final_category": "source_equivalent_proof_variation",
        "source_conflict": False,
        "resolution": "The apparent signature delta is binder naming; the contradiction step is simp versus simpa.",
        "action": "Keep each repository's proof layout; no semantic migration is needed.",
    },
    "thm_2_9": {
        "final_category": "mat_reviewed_source_exact_kenneth_alternate_model",
        "source_conflict": False,
        "resolution": "MAT matches P([0,1]) -> NNReal and the reviewed choice/partition/mass route; Kenneth proves an alternate ENNReal axiom package.",
        "action": "Retain MAT as the reviewed task landing and preserve Kenneth's alternate model; review anew before any cross-repository adoption.",
    },
    "def_3_1": {
        "final_category": "kenneth_additive_bridge_api",
        "source_conflict": False,
        "resolution": "FieldOfSets and Premeasure agree; Kenneth adds SetRing/AddContent conversion helpers.",
        "action": "Preserve Kenneth's bridge API; review it independently before adding it to MAT.",
    },
    "def_3_10": {
        "final_category": "mat_source_exact_kenneth_additive_bridges",
        "source_conflict": False,
        "resolution": "Both core definitions cover the source laws; Kenneth's IsPiSystem bridge separately assumes empty-set membership.",
        "action": "Keep the source-facing MAT predicate and preserve Kenneth's optional bridges in Kenneth.",
    },
    "def_3_2": {
        "final_category": "mat_reviewed_source_interface_refinement",
        "source_conflict": False,
        "resolution": "The source premeasure is defined on a field; MAT preserves FieldOfSets/Premeasure in the type, while Kenneth uses a raw family/function.",
        "action": "Retain MAT's reviewed source interface; do not replace it with the weaker raw-family interface.",
    },
    "def_3_6": {
        "final_category": "mat_reviewed_chapter_context_resolution",
        "source_conflict": False,
        "resolution": "Kenneth preserves the literal closed-interval clause; the independent MAT review also accounts for the following arbitrary-set Heine-Borel theorem and keeps the interval as a proved subtype.",
        "action": "Retain the reviewed MAT general owner plus interval subtype; preserve Kenneth's literal local definition unless a separately reviewed integration is requested.",
    },
    "thm_3_1": {
        "final_category": "mat_reviewed_source_route_complete",
        "source_conflict": False,
        "resolution": "MAT covers extension existence and the sigma-finite uniqueness clause; Kenneth exposes a shorter Mathlib-backed existence result.",
        "action": "Retain MAT's reviewed theorem; preserve Kenneth's narrower adapter independently.",
    },
    "thm_3_2": {
        "final_category": "mat_reviewed_source_route_over_adapter",
        "source_conflict": False,
        "resolution": "MAT proves the distribution-function properties from the measure; Kenneth rewrites to Mathlib cdf and uses its API.",
        "action": "Retain the reviewed MAT source route; no cross-repository replacement is justified.",
    },
    "thm_3_3": {
        "final_category": "mat_reviewed_completion_over_kenneth_placeholder",
        "source_conflict": False,
        "resolution": "MAT contains the reviewed Lebesgue-Stieltjes construction; Kenneth's current file is a temporary/narrow landing.",
        "action": "Retain MAT; any Kenneth completion requires a fresh independent review.",
    },
    "thm_3_4": {
        "final_category": "mat_reviewed_canonical_integration",
        "source_conflict": False,
        "resolution": "MAT consumes the reviewed def_3_6/def_3_7 owners for the arbitrary-set Heine-Borel statement; Kenneth defines a local interval predicate.",
        "action": "Retain MAT's canonical integration and preserve Kenneth's local formulation.",
    },
    "thm_3_8": {
        "final_category": "mat_reviewed_source_route_kenneth_dual_api",
        "source_conflict": False,
        "resolution": "MAT makes the explicit pi-lambda proof the canonical theorem; Kenneth exposes both a short Mathlib theorem and a separate textbook route.",
        "action": "Keep both repository layouts; require review before changing either canonical landing.",
    },
    "def_4_4_polar_form": {
        "final_category": "mat_reviewed_source_partiality_fix",
        "source_conflict": False,
        "resolution": "The source says arg(0) is undefined and phase is modulo 2pi; MAT represents both explicitly, whereas Kenneth totalizes them.",
        "action": "Retain MAT's reviewed Option/Angle interface; preserve Kenneth until a separately reviewed correction is authorized.",
    },
    "thm_4_6": {
        "final_category": "mat_reviewed_source_route_complete",
        "source_conflict": False,
        "resolution": "MAT contains the later reviewed full source construction; Kenneth exposes only the smaller terminal theorem.",
        "action": "Retain MAT; do not replace it with the narrower Kenneth landing.",
    },
}


def read_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"Expected JSON object: {path}")
    return payload


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def git_bytes(repo: Path, ref: str, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(repo), "show", f"{ref}:{path}"],
        stderr=subprocess.DEVNULL,
    )


def git_file_history(repo: Path, ref: str, path: str) -> dict[str, str]:
    raw = subprocess.check_output(
        [
            "git", "-C", str(repo), "log", "-1",
            "--format=%H%x00%cI%x00%s", ref, "--", path,
        ],
        stderr=subprocess.DEVNULL,
    ).decode("utf-8", errors="replace").strip()
    parts = raw.split("\x00", 2) if raw else []
    return {
        "commit": parts[0] if len(parts) > 0 else "",
        "committed_at": parts[1] if len(parts) > 1 else "",
        "subject": parts[2] if len(parts) > 2 else "",
    }


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.DOTALL)
    return re.sub(r"(?m)--.*$", " ", text)


def normalize_lean(text: str, *, drop_imports_and_namespaces: bool = False) -> str:
    text = strip_comments(text.replace("\r\n", "\n"))
    if drop_imports_and_namespaces:
        text = re.sub(r"(?m)^\s*import\s+[^\n]+$", " ", text)
        text = re.sub(r"(?m)^\s*namespace\s+[^\n]+$", " ", text)
        text = re.sub(r"(?m)^\s*end(?:\s+[^\n]+)?$", " ", text)
    text = text.replace("ProbabilityTheory.", "")
    return re.sub(r"\s+", " ", text).strip()


def parse_import_task_ids(text: str, formal_task_ids: set[str]) -> list[str]:
    found: list[str] = []
    for module in IMPORT_RE.findall(text):
        task_id = canonicalize_block_id(module.rsplit(".", 1)[-1])
        if task_id in formal_task_ids and task_id not in found:
            found.append(task_id)
    return found


def declaration_blocks(text: str) -> list[dict[str, Any]]:
    clean = strip_comments(text)
    matches = list(DECL_RE.finditer(clean))
    names = {match.group("name").rsplit(".", 1)[-1] for match in matches}
    declarations: list[dict[str, Any]] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(clean)
        block = clean[match.start():end].strip()
        boundary = re.search(r"\s:=\s|\swhere\s*$", block, flags=re.MULTILINE)
        signature = block[: boundary.start()].strip() if boundary else block.splitlines()[0].strip()
        body = block[boundary.end():].strip() if boundary else ""
        tokens = [token for token in TOKEN_RE.findall(body) if token.lower() not in KEYWORDS]
        token_counts = Counter(tokens)
        local_refs = sorted({token for token in tokens if token.rsplit(".", 1)[-1] in names})
        constants = [
            token for token, _count in token_counts.most_common()
            if token not in local_refs and ("." in token or token[0].islower())
        ][:24]
        route_lines = [
            re.sub(r"\s+", " ", line).strip()
            for line in block.splitlines()
            if ROUTE_LINE_RE.search(line)
        ][:16]
        declarations.append(
            {
                "kind": match.group("kind"),
                "name": match.group("name"),
                "private": bool(match.group("private")),
                "signature": re.sub(r"\s+", " ", signature),
                "signature_normalized": normalize_lean(signature),
                "body_sha256": sha256_bytes(body.encode("utf-8")),
                "local_declaration_refs": local_refs,
                "principal_body_constants": constants,
                "route_lines": route_lines,
            }
        )
    return declarations


def public_api(text: str) -> list[dict[str, str]]:
    return [
        {
            "kind": declaration["kind"],
            "name": declaration["name"].rsplit(".", 1)[-1],
            "signature": declaration["signature_normalized"],
        }
        for declaration in declaration_blocks(text)
        if not declaration["private"]
    ]


def load_plan_entries(plans_dir: Path) -> dict[str, dict[str, Any]]:
    tasks: dict[str, dict[str, Any]] = {}
    for path in sorted(plans_dir.rglob("*_plan.json")):
        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, list):
            continue
        for raw in payload:
            if not isinstance(raw, dict):
                continue
            normalized_type, _note = normalize_phase1_task_type(raw.get("type", ""))
            if normalized_type not in FORMAL_TYPES:
                continue
            task_id = canonicalize_block_id(str(raw.get("block_id", "") or ""))
            if not task_id:
                continue
            tasks[task_id] = {
                **raw,
                "block_id": task_id,
                "type": normalized_type,
                "source_plan_file": str(path.resolve()),
            }
    return tasks


def decode_head(head: dict[str, Any] | None) -> dict[str, Any] | None:
    if not head:
        return None
    decoded = dict(head)
    for key in ("manifest_json", "detail_json"):
        raw = decoded.get(key)
        if isinstance(raw, str):
            try:
                decoded[key.removesuffix("_json")] = json.loads(raw)
            except json.JSONDecodeError:
                decoded[key.removesuffix("_json")] = raw
    return decoded


def review_evidence(latest_review: dict[str, Any] | None) -> dict[str, Any] | None:
    if not latest_review:
        return None
    result_path = Path(str(latest_review.get("evidence_path", "") or ""))
    result = read_json(result_path)
    if result.get("schema_version") == "toy-apollo.workspace-review-binding.v1":
        task_id = canonicalize_block_id(str(latest_review.get("task_id", "") or ""))
        entry = next(
            (
                item for item in result.get("tasks", [])
                if isinstance(item, dict)
                and canonicalize_block_id(str(item.get("task_id", "") or "")) == task_id
            ),
            None,
        )
        basis = entry.get("basis_review") if isinstance(entry, dict) else None
        if not isinstance(basis, dict) or not basis.get("evidence_path"):
            raise ValueError(f"{result_path}: {task_id} has no auditable basis review")
        resolved = review_evidence(
            {
                **latest_review,
                "evidence_path": basis.get("evidence_path", ""),
                "evidence_hash": basis.get("evidence_hash", ""),
                "review_id": basis.get("review_id", ""),
                "reviewed_at": basis.get("reviewed_at", ""),
                "primary_hash": basis.get("primary_hash", ""),
            }
        )
        if resolved is None:
            raise ValueError(f"{result_path}: {task_id} basis review did not resolve")
        resolved["latest_workspace_binding"] = {
            "path": str(result_path.resolve()),
            "sha256": sha256_file(result_path),
            "binding_kind": entry.get("binding_kind", "") if isinstance(entry, dict) else "",
        }
        return resolved
    refs: dict[str, Any] = {}
    for key in ("review_input_file", "review_prompt_file", "review_context_file"):
        raw = str(result.get(key, "") or "")
        if not raw:
            continue
        path = Path(raw).resolve()
        refs[key] = {
            "path": str(path),
            "sha256": sha256_file(path) if path.is_file() else "",
        }
    input_raw = str(result.get("review_input_file", "") or "")
    if input_raw:
        input_path = Path(input_raw)
        request_path = input_path.with_name(
            input_path.name.replace("semantic_review_input", "semantic_review_request")
        )
        if request_path.is_file():
            refs["review_request_file"] = {
                "path": str(request_path.resolve()),
                "sha256": sha256_file(request_path),
            }
    claim_mapping = result.get("claim_mapping", [])
    route_names = sorted(
        {
            token
            for token in re.findall(
                r"\b[A-Za-z_][A-Za-z0-9_']*\b",
                json.dumps(claim_mapping, ensure_ascii=False),
            )
            if token.startswith(("def_", "thm_", "ex_", "prob_"))
            or token[:1].islower()
        }
    )
    return {
        "result_file": str(result_path.resolve()),
        "result_sha256": sha256_file(result_path),
        "review_id": latest_review.get("review_id", ""),
        "reviewed_at": latest_review.get("reviewed_at", ""),
        "verdict": result.get("verdict", ""),
        "phase2_status": latest_review.get("phase2_status", result.get("phase2_status", "")),
        "proof_class": result.get("proof_class", latest_review.get("proof_class", "")),
        "completion_class": result.get("completion_class", latest_review.get("completion_class", "")),
        "candidate_hash": result.get("candidate_hash", latest_review.get("primary_hash", "")),
        "review_input_hash": result.get("review_input_hash", ""),
        "reviewer_independence": result.get("reviewer_independence", {}),
        "summary": result.get("summary", ""),
        "source_claims": result.get("source_claims", []),
        "claim_mapping": claim_mapping,
        "spine_alignment": result.get("spine_alignment", {}),
        "route_inspection": result.get("route_inspection", {}),
        "downstream_adequacy": result.get("downstream_adequacy", {}),
        "route_names_mentioned": route_names,
        "artifacts": refs,
    }


def graph_layers(task_ids: set[str], dependencies: dict[str, set[str]]) -> tuple[list[list[str]], list[str]]:
    in_scope = {task: {dep for dep in dependencies[task] if dep in task_ids} for task in task_ids}
    indegree = {task: len(deps) for task, deps in in_scope.items()}
    consumers: dict[str, set[str]] = defaultdict(set)
    for task, deps in in_scope.items():
        for dep in deps:
            consumers[dep].add(task)
    ready = deque(sorted(task for task, degree in indegree.items() if degree == 0))
    layers: list[list[str]] = []
    visited: set[str] = set()
    while ready:
        layer = list(ready)
        ready.clear()
        layers.append(layer)
        for task in layer:
            visited.add(task)
            for consumer in sorted(consumers.get(task, set())):
                indegree[consumer] -= 1
                if indegree[consumer] == 0:
                    ready.append(consumer)
    return layers, sorted(task_ids - visited)


def compare_subjects(
    task_id: str,
    mat_head: dict[str, Any] | None,
    kenneth_head: dict[str, Any] | None,
    *,
    mat_repo: Path,
    kenneth_repo: Path,
    mat_ref: str,
    kenneth_ref: str,
) -> dict[str, Any] | None:
    if not mat_head or not kenneth_head:
        return None
    mat_path = str(mat_head.get("primary_path", "") or "")
    kenneth_path = str(kenneth_head.get("primary_path", "") or "")
    mat_bytes = git_bytes(mat_repo, mat_ref, mat_path)
    kenneth_bytes = git_bytes(kenneth_repo, kenneth_ref, kenneth_path)
    mat_text = mat_bytes.decode("utf-8", errors="replace")
    kenneth_text = kenneth_bytes.decode("utf-8", errors="replace")
    mat_api = public_api(mat_text)
    kenneth_api = public_api(kenneth_text)
    mat_by_name = {item["name"]: item for item in mat_api}
    kenneth_by_name = {item["name"]: item for item in kenneth_api}
    common = sorted(set(mat_by_name) & set(kenneth_by_name))
    changed_signatures = [
        name for name in common
        if mat_by_name[name]["signature"] != kenneth_by_name[name]["signature"]
    ]
    if mat_bytes == kenneth_bytes:
        category = "byte_identical"
    elif normalize_lean(mat_text, drop_imports_and_namespaces=True) == normalize_lean(
        kenneth_text,
        drop_imports_and_namespaces=True,
    ):
        category = "mechanical_import_namespace_comment_only"
    elif set(mat_by_name) == set(kenneth_by_name) and not changed_signatures:
        category = "same_public_api_different_proof_or_layout"
    elif set(kenneth_by_name) < set(mat_by_name) and not changed_signatures:
        category = "mat_reviewed_api_superset"
    elif set(mat_by_name) < set(kenneth_by_name) and not changed_signatures:
        category = "kenneth_author_api_superset"
    else:
        category = "public_api_or_statement_difference"
    recommendation = {
        "byte_identical": "already_aligned",
        "mechanical_import_namespace_comment_only": "preserve_kenneth_layout_and_reuse_reviewed_mat_semantics",
        "same_public_api_different_proof_or_layout": "prefer_later_reviewed_mat_proof_while_preserving_kenneth_layout",
        "mat_reviewed_api_superset": "mat_is_reviewed_refinement;_candidate_for_later_kenneth_pr_only",
        "kenneth_author_api_superset": "preserve_kenneth_author_api;review_in_mat_before_any_adoption",
        "public_api_or_statement_difference": "manual_source_semantics_decision_required_before_cross_repo_change",
    }[category]
    adjudication = MANUAL_KENNETH_ADJUDICATIONS.get(task_id)
    return {
        "task_id": task_id,
        "category": category,
        "recommendation": recommendation,
        "requires_fresh_review_before_cross_repo_adoption": category
        in {"kenneth_author_api_superset", "public_api_or_statement_difference"},
        "manual_adjudication": adjudication,
        "final_category": (
            adjudication["final_category"] if adjudication else category
        ),
        "mat": {
            "commit": mat_head.get("source_commit", ""),
            "path": mat_path,
            "git_blob_sha": mat_head.get("primary_git_sha", ""),
            "sha256": sha256_bytes(mat_bytes),
            "history": git_file_history(mat_repo, mat_ref, mat_path),
            "public_api": mat_api,
        },
        "kenneth": {
            "commit": kenneth_head.get("source_commit", ""),
            "path": kenneth_path,
            "git_blob_sha": kenneth_head.get("primary_git_sha", ""),
            "sha256": sha256_bytes(kenneth_bytes),
            "history": git_file_history(kenneth_repo, kenneth_ref, kenneth_path),
            "public_api": kenneth_api,
        },
        "api_delta": {
            "mat_only": sorted(set(mat_by_name) - set(kenneth_by_name)),
            "kenneth_only": sorted(set(kenneth_by_name) - set(mat_by_name)),
            "changed_signatures": changed_signatures,
        },
    }


def compact_route(row: dict[str, Any]) -> str:
    review = row.get("review") or {}
    spine = review.get("spine_alignment") or {}
    summary = str(spine.get("summary", "") or review.get("summary", "") or "")
    summary = re.sub(r"\s+", " ", summary).strip()
    declarations = row["actual_lean_route"]["declarations"]
    names = ", ".join(item["name"] for item in declarations[:4])
    if len(declarations) > 4:
        names += f" (+{len(declarations) - 4})"
    return f"{names}: {summary[:220]}" if summary else names


def render_markdown(payload: dict[str, Any]) -> str:
    counts = payload["summary"]["chapter_counts"]
    comparison_counts = payload["summary"]["kenneth_comparison_categories"]
    lines = [
        "# Chapter 2–4 状态重绑定与 Kenneth 调和证据",
        "",
        f"生成时间：{payload['generated_at']}",
        "",
        "## 摘要",
        "",
        f"- 正式任务：{payload['summary']['task_count']}（Chapter 2/3/4 = {counts.get('2', 0)}/{counts.get('3', 0)}/{counts.get('4', 0)}）",
        f"- primary 与旧 applied pass 完全一致：{payload['summary']['review_primary_match_count']}",
        f"- 当前 bundle 仅含 primary：{payload['summary']['primary_only_bundle_count']}",
        f"- MAT 与 Kenneth 同时有 head：{payload['summary']['mat_kenneth_both_count']}；内容不同：{payload['summary']['mat_kenneth_different_count']}",
        f"- Kenneth 分类：{json.dumps(comparison_counts, ensure_ascii=False, sort_keys=True)}",
        f"- 人工证据裁决：{payload['summary']['manual_adjudication_count']}；未决来源阻塞：{payload['summary']['unresolved_source_decision_count']}",
        "",
        "## 跨章依赖边",
        "",
    ]
    for edge in payload["dependency_graph"]["cross_chapter_edges"]:
        lines.append(f"- `{edge['consumer']}` → `{edge['dependency']}`（{'+'.join(edge['sources'])}）")
    if not payload["dependency_graph"]["cross_chapter_edges"]:
        lines.append("- 无")
    lines.extend(
        [
            "",
            "## 114 项 evidence rows",
            "",
            "| task | type | deps(plan/import) | old review | bundle | actual route | Kenneth |",
            "|---|---|---|---|---|---|---|",
        ]
    )
    for row in payload["tasks"]:
        deps = f"{len(row['dependencies']['plan'])}/{len(row['dependencies']['lean_imports'])}"
        review = row.get("review") or {}
        review_cell = f"{review.get('verdict', '')}/{review.get('proof_class', '')}"
        bundle = "primary-only" if row["bundle_assessment"]["current_bundle_primary_only"] else "has-support"
        comparison = row.get("kenneth_comparison") or {}
        kenneth = comparison.get("final_category", comparison.get("category", "no-both-head"))
        route = compact_route(row).replace("|", "\\|")
        lines.append(
            f"| `{row['task_id']}` | {row['type']} | {deps} | {review_cell} | {bundle} | {route} | {kenneth} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chapters", default="2,3,4")
    parser.add_argument("--kenneth-repo", type=Path, required=True)
    parser.add_argument("--kenneth-ref", default="origin/main")
    parser.add_argument("--mat-repo", type=Path, required=True)
    parser.add_argument("--mat-ref", default="origin/main")
    parser.add_argument("--json-output", type=Path, required=True)
    parser.add_argument("--markdown-output", type=Path, required=True)
    args = parser.parse_args()

    chapters = tuple(int(item) for item in args.chapters.split(",") if item.strip())
    settings = get_settings()
    runtime_root = Path(settings.runtime_root).resolve()
    plans_dir = runtime_root / "plans"
    output_dir = runtime_root / "ToyApollo" / "Output"
    store = WorkspaceStateStore(settings.state_db_file)
    store.assert_integrity()
    formal_ids = discover_formal_plan_task_ids(plans_dir, chapters=chapters)
    all_formal_ids = discover_formal_plan_task_ids(plans_dir)
    plans = load_plan_entries(plans_dir)

    plan_dependencies: dict[str, set[str]] = {}
    import_dependencies: dict[str, set[str]] = {}
    reverse_imports: dict[str, set[str]] = defaultdict(set)
    reverse_plans: dict[str, set[str]] = defaultdict(set)
    for task_id in all_formal_ids:
        plan_dependencies[task_id] = {
            canonicalize_block_id(str(dep))
            for dep in plans.get(task_id, {}).get("dependencies", [])
            if canonicalize_block_id(str(dep))
        }
        for dep in plan_dependencies[task_id]:
            reverse_plans[dep].add(task_id)
        path = output_dir / f"{task_id}.lean"
        text = path.read_text(encoding="utf-8") if path.is_file() else ""
        import_dependencies[task_id] = set(parse_import_task_ids(text, all_formal_ids))
        for dep in import_dependencies[task_id]:
            reverse_imports[dep].add(task_id)

    combined_dependencies = {
        task_id: plan_dependencies.get(task_id, set()) | import_dependencies.get(task_id, set())
        for task_id in formal_ids
    }
    layers, cycles = graph_layers(formal_ids, combined_dependencies)
    cross_chapter: list[dict[str, Any]] = []
    for consumer, deps in combined_dependencies.items():
        for dependency in deps:
            dep_chapter = extract_chapter(dependency)
            if dep_chapter is None or dep_chapter == extract_chapter(consumer):
                continue
            sources: list[str] = []
            if dependency in plan_dependencies.get(consumer, set()):
                sources.append("plan")
            if dependency in import_dependencies.get(consumer, set()):
                sources.append("lean_import")
            cross_chapter.append(
                {"consumer": consumer, "dependency": dependency, "sources": sources}
            )

    rows: list[dict[str, Any]] = []
    comparison_counts: Counter[str] = Counter()
    final_comparison_counts: Counter[str] = Counter()
    review_match_count = 0
    primary_only_count = 0
    both_count = 0
    different_count = 0
    chapter_counts: Counter[int] = Counter()
    for task_id in sorted(formal_ids, key=lambda item: (extract_chapter(item) or 0, item)):
        plan = plans[task_id]
        report = store.task_report(task_id)
        heads = {role: decode_head(head) for role, head in report.get("heads", {}).items()}
        toy_head = heads.get("toy_current")
        mat_head = heads.get("mat_main")
        kenneth_head = heads.get("kenneth_main")
        source_path = output_dir / f"{task_id}.lean"
        source_text = source_path.read_text(encoding="utf-8")
        declarations = declaration_blocks(source_text)
        review = review_evidence(report.get("latest_review"))
        primary_matches_review = bool(
            review and toy_head and review.get("candidate_hash") == toy_head.get("primary_hash")
        )
        if primary_matches_review:
            review_match_count += 1
        manifest = list((toy_head or {}).get("manifest", []) or [])
        primary_only = len(manifest) == 1 and manifest[0].get("path") == (toy_head or {}).get("primary_path")
        if primary_only:
            primary_only_count += 1
        forbidden_findings = {
            name: [match.start() for match in pattern.finditer(source_text)]
            for name, pattern in FORBIDDEN_PATTERNS.items()
            if pattern.search(source_text)
        }
        comparison = compare_subjects(
            task_id,
            mat_head,
            kenneth_head,
            mat_repo=args.mat_repo.resolve(),
            kenneth_repo=args.kenneth_repo.resolve(),
            mat_ref=args.mat_ref,
            kenneth_ref=args.kenneth_ref,
        )
        if comparison:
            both_count += 1
            category = comparison["category"]
            comparison_counts[category] += 1
            final_comparison_counts[comparison["final_category"]] += 1
            if category != "byte_identical":
                different_count += 1
        chapter = extract_chapter(task_id)
        if chapter is not None:
            chapter_counts[chapter] += 1
        rows.append(
            {
                "task_id": task_id,
                "chapter": chapter,
                "type": plan["type"],
                "title": plan.get("title", ""),
                "textbook_claim": plan.get("content", ""),
                "source_plan_file": plan["source_plan_file"],
                "dependencies": {
                    "plan": sorted(plan_dependencies.get(task_id, set())),
                    "lean_imports": sorted(import_dependencies.get(task_id, set())),
                    "combined": sorted(combined_dependencies[task_id]),
                    "plan_consumers": sorted(reverse_plans.get(task_id, set())),
                    "lean_import_consumers": sorted(reverse_imports.get(task_id, set())),
                },
                "review": review,
                "current_heads": heads,
                "bundle_assessment": {
                    "reviewed_primary_matches_current": primary_matches_review,
                    "current_bundle_primary_only": primary_only,
                    "support_files": [
                        item for item in manifest
                        if item.get("path") != (toy_head or {}).get("primary_path")
                    ],
                    "toy_mat_primary_byte_identical": bool(
                        toy_head and mat_head and toy_head.get("primary_hash") == mat_head.get("primary_hash")
                    ),
                    "provisional_rebind_class": (
                        "mechanical_scope_rebind"
                        if primary_matches_review and primary_only and not forbidden_findings
                        else "fresh_semantic_review_required"
                    ),
                },
                "actual_lean_route": {
                    "source_file": str(source_path.resolve()),
                    "source_sha256": sha256_file(source_path),
                    "imports": IMPORT_RE.findall(source_text),
                    "declarations": declarations,
                    "forbidden_findings": forbidden_findings,
                },
                "kenneth_comparison": comparison,
            }
        )

    payload = {
        "schema_version": "toy-apollo.chapter-state-reconciliation-evidence.v1",
        "generated_at": utc_now(),
        "state_database": str(Path(settings.state_db_file).resolve()),
        "state_database_sha256": sha256_file(Path(settings.state_db_file)),
        "chapters": list(chapters),
        "summary": {
            "task_count": len(rows),
            "chapter_counts": {str(key): value for key, value in sorted(chapter_counts.items())},
            "review_primary_match_count": review_match_count,
            "primary_only_bundle_count": primary_only_count,
            "mat_kenneth_both_count": both_count,
            "mat_kenneth_different_count": different_count,
            "kenneth_comparison_categories": dict(sorted(comparison_counts.items())),
            "kenneth_final_reconciliation_categories": dict(sorted(final_comparison_counts.items())),
            "manual_adjudication_count": sum(
                1 for row in rows
                if (row.get("kenneth_comparison") or {}).get("manual_adjudication")
            ),
            "unresolved_source_decision_count": sum(
                1 for row in rows
                if ((row.get("kenneth_comparison") or {}).get("manual_adjudication") or {}).get("source_conflict")
            ),
        },
        "dependency_graph": {
            "topological_layers": layers,
            "cycle_or_unresolved_nodes": cycles,
            "cross_chapter_edges": sorted(
                cross_chapter,
                key=lambda item: (item["consumer"], item["dependency"]),
            ),
        },
        "tasks": rows,
    }
    write_json(args.json_output.resolve(), payload)
    markdown_path = args.markdown_output.resolve()
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    print(json.dumps(payload["summary"], ensure_ascii=False, sort_keys=True))
    print(f"JSON={args.json_output.resolve()}")
    print(f"MARKDOWN={markdown_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
