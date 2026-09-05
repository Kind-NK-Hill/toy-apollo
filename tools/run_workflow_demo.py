"""Run production Phase 2 gates on an isolated, explicitly non-catalog fixture.

No build gate is mocked. The default semantic opinions are recorded teaching
reviews; rebinding them to a new temporary request is a replay, not a fresh
independent review. Live mode delegates to an explicitly configured runner.
"""
from __future__ import annotations

import argparse
import asyncio
import copy
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "src"))

from formalization_engine.core.settings import Settings
from formalization_engine.core.sqlite_ledger import SQLiteLedgerManager
from formalization_engine.phase2_prompt_pack import (
    build_check_prompt_pack_candidate,
    run_codex_review_now,
    write_prompt_pack,
)
from formalization_engine.phase2_review_apply import apply_codex_review_result_once
from formalization_engine.phase2_math_review_gate import math_review_gate_state
from formalization_engine.state_store import WorkspaceStateStore

FIXTURES = REPO_ROOT / "examples" / "workflow-demo"
TASK_ID = "def_demo_frequency"
SOURCE_PLAN = "workflow_demo"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                     separators=(",", ":")).encode("utf-8")).hexdigest()


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def snapshot(root: Path, excluded: set[Path] | None = None) -> dict[str, str]:
    excluded = excluded or set()
    return {p.relative_to(root).as_posix(): sha256(p) for p in sorted(root.rglob("*"))
            if p.is_file() and p.resolve() not in excluded}


def prepare(run_root: Path, repl_source: Path) -> tuple[Settings, SQLiteLedgerManager]:
    """Create an entirely new runtime; never accept an existing run directory."""
    if run_root.exists():
        raise ValueError(f"Refusing an existing output directory: {run_root}")
    if not (repl_source / "lakefile.toml").is_file():
        raise ValueError("Pinned REPL source is missing. Run 'lake update' first, or use --repl-source.")
    runtime, artifacts = run_root / "runtime", run_root / "artifacts"
    runtime.mkdir(parents=True)
    artifacts.mkdir()
    # REPL has no package dependencies. Copy its source and available build
    # cache so Lake never writes into the original package or live repository.
    shutil.copytree(repl_source, runtime / "vendor" / "repl",
                    ignore=shutil.ignore_patterns(".git", "tests", "test", "docs"))
    shutil.copyfile(REPO_ROOT / "lean-toolchain", runtime / "lean-toolchain")
    (runtime / "lakefile.toml").write_text(
        'name = "WorkflowDemo"\nversion = "0.1.0"\n'
        'defaultTargets = ["ProbabilityTheory"]\n\n'
        '[[require]]\nname = "REPL"\npath = "vendor/repl"\n\n'
        '[[lean_lib]]\nname = "ProbabilityTheory"\n'
        'srcDir = "."\nglobs = ["ProbabilityTheory.+"]\n', encoding="utf-8")
    (runtime / "ProbabilityTheory").mkdir()
    (runtime / "ProbabilityTheory.lean").write_text("-- Isolated teaching corpus.\n", encoding="utf-8")
    setup = subprocess.run(["lake", "build", "repl"], cwd=runtime, capture_output=True,
                           text=True, encoding="utf-8", errors="replace", timeout=300)
    (run_root / "setup.log").write_text(setup.stdout + setup.stderr, encoding="utf-8")
    if setup.returncode:
        raise RuntimeError(f"Isolated REPL setup failed; inspect {run_root / 'setup.log'}")
    settings = Settings(
        runtime_root=runtime, artifact_root=artifacts, plans_dir=artifacts / "plans",
        reports_dir=artifacts / "reports", formalized_chapters_dir=artifacts / "formalized_chapters",
        output_lean_files_dir=artifacts / "output_lean_files",
        phase2_prompt_packs_dir=artifacts / "phase2_prompt_packs",
        phase2_softdep_packs_dir=artifacts / "phase2_softdep_packs",
        error_logs_dir=artifacts / "error_logs", canonical_lean_dir=runtime / "ProbabilityTheory",
        aristotle_outbox_dir=artifacts / "legacy_unused_outbox",
        aristotle_archives_dir=artifacts / "legacy_unused_archives",
        mathlib_index_file=artifacts / "unused.faiss", mathlib_corpus_file=artifacts / "unused.json",
        project_ledger_file=artifacts / "project_ledger.json", lab_notebook_file=artifacts / "lab_notebook.json",
        mathlib_path=runtime / "no_mathlib_needed", workspace_root=run_root,
        state_db_file=artifacts / "state.sqlite3", canonical_manifest_required=False,
        dependency_decisions_dir=artifacts / "dependency_decisions",
    )
    # Bootstrap an empty *new* SQLite store, never import a live ledger.
    store = WorkspaceStateStore(settings.state_db_file)
    store.initialize()
    ledger = SQLiteLedgerManager(state_store=store, artifact_root=artifacts,
                                 legacy_ledger_path=settings.project_ledger_file)
    source = FIXTURES / "source.tex"
    (runtime / "inputs").mkdir()
    shutil.copyfile(source, runtime / "inputs" / f"{SOURCE_PLAN}.tex")
    task = {"block_id": TASK_ID, "type": "Definition", "title": "Teaching frequency interface",
            "content": source.read_text(encoding="utf-8"), "source_plan": SOURCE_PLAN, "dependencies": []}
    write_json(settings.plans_dir / f"{SOURCE_PLAN}_plan.json", [task])
    ledger.add_or_update_task(task)
    write_prompt_pack(TASK_ID, ledger, settings)
    return settings, ledger


def replay_review(review_input: dict[str, Any], input_path: Path, variant: str) -> dict[str, Any]:
    """Adapt a fixed teaching opinion, retaining original provenance explicitly.

    Runtime independence fields below belong to a simulated protocol envelope.
    They are deliberately labelled and confer no new semantic authority.
    """
    fixture_path = FIXTURES / f"{variant}.lean"
    if review_input["candidate"]["lean"] != fixture_path.read_text(encoding="utf-8"):
        raise ValueError("Replay refuses code other than the exact reviewed fixture.")
    recorded = read_json(FIXTURES / "teaching-review.json")
    for name in ("source.tex", "initial.lean", "interface-only.lean", "final.lean"):
        if recorded.get("reviewed_files", {}).get(name) != sha256(FIXTURES / name):
            raise ValueError(f"Fixture bytes differ from the independently recorded teaching review: {name}")
    opinion = copy.deepcopy(recorded["reviews"][variant])
    passed = opinion["verdict"] == "pass"
    opinion["route_inspection"]["status"] = "covered" if passed else "violated"
    for section in ("interface_contract", "downstream_adequacy"):
        if opinion[section]["status"] == "fail":
            opinion[section]["status"] = "violated"
    opinion["downstream_adequacy"]["consumers_checked"] = [
        {"block_id": "demo_two_of_four", "status": "covered" if passed else "blocked", "evidence": item}
        for item in opinion["downstream_adequacy"]["consumers_checked"]
    ]
    opinion.update({
        "task_id": TASK_ID, "candidate_hash": review_input["candidate"]["hash"],
        "prompt_version": review_input["prompt_version"], "rubric_version": review_input["rubric_version"],
        "review_input_file": str(input_path), "review_input_hash": json_hash(review_input),
        "confidence": opinion.get("confidence", "high"),
        "proof_class": "definition_only_completed" if passed else "semantic_fail",
        "completion_class": "definition_only_completed" if passed else "semantic_fail",
        "reviewer_independence": {
            "role": "independent_read_only_reviewer", "read_only": True,
            "did_edit_candidate": False, "used_current_review_request": True,
            "attestation": "SIMULATED REPLAY ENVELOPE: current request mechanically rebound to a fixed teaching opinion; no reviewer inspected this new runtime. Original reviewer provenance is retained separately.",
        },
        "teaching_replay": {"is_live_review": False, "is_catalog_authority": False,
                            "recorded_review_sha256": sha256(FIXTURES / "teaching-review.json"),
                            "original_provenance": recorded["provenance"],
                            "original_opinion": recorded["reviews"][variant]},
        "evidence_review": {
            "status": "covered", "summary": "Teaching protocol replay over isolated generated evidence; not a fresh review.",
            "items": [{"evidence_class": item, "status": "covered",
                       "evidence": "SIMULATED: generated fixture evidence bound by the current production request; not independently re-reviewed."}
                      for item in review_input["review_basis"]["required_evidence_classes"]],
            "blocking_issues": [],
        },
        "forbidden_weakenings": [{"status": "not_present", "summary": "Fixed teaching opinion: required conditions are explicit."}] if passed else [],
        "recommended_disposition": "promote" if passed else "revise",
    })
    opinion["summary"] = "TEACHING REPLAY, NOT LIVE REVIEW. " + opinion["summary"]
    return opinion


def run_reviewer(run_root: Path, request_path: Path, args: argparse.Namespace) -> Path:
    request = read_json(request_path)
    input_path, result_path = Path(request["review_input_file"]), Path(request["expected_result_file"])
    review_input = read_json(input_path)
    metadata_path = result_path.with_name(result_path.stem + "_runner.json")
    if args.reviewer_argv_json is None:
        variant = "initial" if review_input["candidate"]["lean"] == (FIXTURES / "initial.lean").read_text(encoding="utf-8") else "final"
        write_json(result_path, replay_review(review_input, input_path, variant))
        write_json(metadata_path, {"mode": "recorded_teaching_replay", "is_live_review": False,
                                   "model": None, "cost": None, "request_sha256": sha256(request_path),
                                   "result_sha256": sha256(result_path)})
        return result_path
    argv_template = json.loads(args.reviewer_argv_json)
    if not isinstance(argv_template, list) or not argv_template or not all(isinstance(s, str) and s for s in argv_template):
        raise ValueError("--reviewer-argv-json must be a nonempty JSON string array")
    substitutions = {"input": str(input_path), "prompt": request["review_prompt_file"],
                     "result": str(result_path), "request": str(request_path),
                     "run_metadata": str(metadata_path)}
    argv = [item.format(**substitutions) for item in argv_template]
    excluded = {result_path.resolve(), metadata_path.resolve()}
    before = snapshot(run_root, excluded)
    started, run_id = time.monotonic(), str(uuid.uuid4())
    proc = subprocess.run(argv, cwd=input_path.parent, shell=False, capture_output=True,
                          text=True, encoding="utf-8", errors="replace", timeout=args.reviewer_timeout)
    after = snapshot(run_root, excluded)
    changed = sorted(key for key in before.keys() | after.keys() if before.get(key) != after.get(key))
    supplied = read_json(metadata_path) if metadata_path.exists() else {}
    write_json(metadata_path, {"mode": "external_live_review", "run_id": run_id,
        "reviewer_identity": args.reviewer_id, "model": args.model,
        "elapsed_seconds": round(time.monotonic() - started, 3), "returncode": proc.returncode,
        "request_sha256": sha256(request_path), "result_sha256": sha256(result_path) if result_path.exists() else None,
        "persisted_input_changes": changed, "runner_reported": supplied,
        "stdout": proc.stdout, "stderr": proc.stderr})
    if changed:
        raise RuntimeError(f"Reviewer changed input/runtime files; refusing apply: {changed}")
    if proc.returncode or not result_path.is_file():
        raise RuntimeError(f"Reviewer failed; inspect {metadata_path}")
    return result_path


def prepare_math_review(pack: Path, settings: Settings, args: argparse.Namespace) -> dict[str, Any]:
    """Use a real recorded teaching route review, or request a new one."""
    skeleton = pack / "math_proof_skeleton_v1.md"
    shutil.copyfile(FIXTURES / "math-proof-skeleton.md", skeleton)
    source = settings.runtime_root / "inputs" / f"{SOURCE_PLAN}.tex"
    result_path = pack / "math_review_result_v1.json"
    source_digest, skeleton_digest = sha256(source), sha256(skeleton)
    if args.reviewer_argv_json is None:
        recorded_path = FIXTURES / "math-review.json"
        payload = read_json(recorded_path)
        payload["teaching_replay"] = {
            "is_live_review": False, "is_catalog_authority": False,
            "recorded_review_sha256": sha256(recorded_path),
            "statement": "Recorded three-round teaching route review copied into an isolated replay; no new review occurred.",
        }
        write_json(result_path, payload)
    else:
        input_path, prompt_path = pack / "math_review_input_v1.json", pack / "math_review_prompt_v1.md"
        template = {"schema_version": "workflow_demo.math_review.v1", "task_id": TASK_ID,
            "verdict": "unreviewed", "source_sha256": source_digest,
            "proof_skeleton_sha256": skeleton_digest,
            "provenance": {"reviewer_identity": "", "reviewed_at": "", "role": "independent_read_only_reviewer"},
            "rounds": [{"round": i, "focus": "", "verdict": "unreviewed", "findings": [], "reason": ""}
                       for i in (1, 2, 3)]}
        template_path = pack / "math_review_result_template_v1.json"
        write_json(template_path, template)
        write_json(input_path, {"review_kind": "math_route", "task_id": TASK_ID,
            "source_file": str(source), "source_sha256": source_digest,
            "proof_skeleton_file": str(skeleton), "proof_skeleton_sha256": skeleton_digest,
            "result_template_file": str(template_path), "is_catalog_authority": False})
        prompt_path.write_text(
            "Independently review the original source and repair skeleton in three explicit rounds.\n"
            "Use xhigh reasoning as required by the project contract; report actual identity and settings.\n"
            "Inspect source statement/domain, non-circular premises, and computation/edge cases.\n"
            "Do not edit inputs. Write the result template with a truthful go/stop verdict, three\n"
            "round-specific assessments, source/skeleton hashes, and actual reviewer provenance.\n"
            "Three rounds by one reviewer are not three independent reviewers or statistical samples.\n",
            encoding="utf-8")
        request_path = pack / "math_review_request_v1.json"
        write_json(request_path, {"review_kind": "math_route", "review_input_file": str(input_path),
            "review_prompt_file": str(prompt_path), "expected_result_file": str(result_path),
            "review_result_template_file": str(template_path)})
        result_path = run_reviewer(settings.runtime_root.parent, request_path, args)
        payload = read_json(result_path)
    if payload.get("source_sha256") != source_digest or payload.get("proof_skeleton_sha256") != skeleton_digest:
        raise RuntimeError("Math route review does not bind the exact teaching source and skeleton")
    rounds = payload.get("rounds", [])
    if (payload.get("task_id") != TASK_ID or payload.get("verdict") != "go"
            or not isinstance(rounds, list) or len(rounds) != 3
            or [item.get("round") for item in rounds] != [1, 2, 3]
            or any(item.get("verdict") != "go" or not item.get("reason") for item in rounds)):
        raise RuntimeError("Math route review did not provide three explicit go assessments; evidence retained")
    provenance = payload.get("provenance", {})
    if (provenance.get("role") not in {"independent_read_only_reviewer", "independent_read_only_math_reviewer"}
            or not provenance.get("reviewer_identity") or not provenance.get("reviewed_at")):
        raise RuntimeError("Math route review lacks independent reviewer provenance")
    return {"review_result": str(result_path), "review_sha256": sha256(result_path),
            "skeleton": str(skeleton), "skeleton_sha256": skeleton_digest}


async def execute(settings: Settings, ledger: SQLiteLedgerManager, args: argparse.Namespace) -> dict[str, Any]:
    run_root = settings.runtime_root.parent
    pack = settings.phase2_prompt_packs_dir / TASK_ID
    canonical = settings.canonical_lean_dir / f"{TASK_ID}.lean"
    events: list[dict[str, Any]] = []

    def record(stage: str, **fields: Any) -> None:
        events.append({"stage": stage, **fields})
        write_json(run_root / "events.json", events)
        print(f"{stage}: {fields.get('detail', fields.get('success', 'recorded'))}", flush=True)

    async def build(variant: str, expected: bool, stage: str) -> None:
        shutil.copyfile(FIXTURES / f"{variant}.lean", pack / "draft.lean")
        previous_receipt = ledger.ledger["tasks"][TASK_ID].get("latest_build_result_file")
        success, detail = await build_check_prompt_pack_candidate(TASK_ID, ledger, settings)
        receipt_path = ledger.ledger["tasks"][TASK_ID].get("latest_build_result_file")
        record(stage, success=success, detail=detail,
               receipt=receipt_path)
        if not receipt_path or receipt_path == previous_receipt:
            raise RuntimeError(f"Build was blocked before compilation at {stage}: {detail}")
        receipt = read_json(Path(receipt_path))
        if not expected and receipt.get("hard_checks", {}).get("success") is not True:
            raise RuntimeError("Expected a real Lean failure, not an input/schema rejection")
        if not expected and receipt.get("temp_build", {}).get("success") is not False:
            raise RuntimeError("Expected the compiler to reject the old caller")
        if success != expected:
            raise RuntimeError(f"Unexpected build result at {stage}; see events.json")
        if canonical.exists():
            raise RuntimeError("Build preparation unexpectedly created canonical output")

    async def review(stage: str) -> Path:
        ready, detail = await run_codex_review_now(TASK_ID, ledger, settings, review_subject="candidate")
        if not ready:
            raise RuntimeError(detail)
        request_path = Path(ledger.ledger["tasks"][TASK_ID]["current_review_request_file"])
        result_path = run_reviewer(run_root, request_path, args)
        record(stage, request=str(request_path), result=str(result_path), verdict=read_json(result_path).get("verdict"))
        return result_path

    await build("initial", True, "initial_build_passes")
    rejected = await review("initial_semantic_review")
    outcome = await apply_codex_review_result_once(TASK_ID, ledger, settings, str(rejected))
    record("initial_review_blocks_apply", success=outcome.success, detail=outcome.detail, disposition=outcome.disposition)
    if outcome.success or canonical.exists() or "invalid" in outcome.disposition:
        raise RuntimeError("Expected a valid failing semantic review with no promotion; reviewer may disagree with this teaching case.")
    gate_before = math_review_gate_state(TASK_ID, ledger.ledger["tasks"][TASK_ID], pack_dir=pack)
    record("source_mismatch_requires_math_route_review", required=gate_before.required, status=gate_before.status)
    math_evidence = prepare_math_review(pack, settings, args)
    gate_after = math_review_gate_state(TASK_ID, ledger.ledger["tasks"][TASK_ID], pack_dir=pack)
    record("recorded_math_route_go" if not args.reviewer_argv_json else "fresh_math_route_go",
           status=gate_after.status, **math_evidence)
    if gate_after.blocks_authoring():
        raise RuntimeError(gate_after.reason)
    await build("interface-only", False, "old_caller_fails_after_interface_repair")
    await build("final", True, "repaired_caller_builds")
    first_pass = await review("repaired_semantic_review")
    if read_json(first_pass).get("verdict") != "pass":
        raise RuntimeError("Reviewer did not pass the repaired fixture; retain evidence and investigate.")
    # Create a *new* build receipt; never mutate an immutable candidate snapshot.
    await build("initial", True, "changed_candidate_builds_without_conditions")
    outcome = await apply_codex_review_result_once(TASK_ID, ledger, settings, str(first_pass))
    record("old_pass_rejected_after_candidate_change", success=outcome.success, detail=outcome.detail,
           disposition=outcome.disposition)
    if outcome.success or canonical.exists() or outcome.disposition != "codex_review_invalid_no_promotion":
        raise RuntimeError("Freshness gate did not reject the old passing result")
    await build("final", True, "restored_repair_builds")
    fresh_pass = await review("fresh_semantic_review")
    outcome = await apply_codex_review_result_once(TASK_ID, ledger, settings, str(fresh_pass))
    record("fresh_pass_lands", success=outcome.success, detail=outcome.detail, disposition=outcome.disposition)
    if not outcome.success or not canonical.is_file():
        raise RuntimeError("Fresh review did not land; inspect retained evidence")
    if canonical.read_text(encoding="utf-8") != (FIXTURES / "final.lean").read_text(encoding="utf-8"):
        raise RuntimeError("Applied output differs from the reviewed fixture")
    applied_input = read_json(Path(read_json(fresh_pass)["review_input_file"]))
    if sha256(canonical) != sha256(Path(applied_input["candidate"]["file"])):
        raise RuntimeError("Applied bytes differ from the exact reviewed candidate snapshot")
    ledger.state_store.assert_integrity()
    result = {"schema_version": "workflow_demo.v1", "completed": True,
        "mode": "external_live_review" if args.reviewer_argv_json else "recorded_teaching_replay",
        "is_catalog_authority": False, "task_id": TASK_ID, "run_root": str(run_root),
        "canonical_output": str(canonical), "canonical_sha256": sha256(canonical),
        "canonical_text_sha256": hashlib.sha256(canonical.read_text(encoding="utf-8").encode("utf-8")).hexdigest(),
        "phase2_status_in_isolated_ledger": ledger.ledger["tasks"][TASK_ID].get("phase2_status"),
        "events": events}
    write_json(run_root / "summary.json", result)
    # Hash stable receipts and inputs, not SQLite lock files or disposable Lean cache.
    paths = list(pack.rglob("*")) + [canonical, run_root / "summary.json", run_root / "events.json",
        settings.runtime_root / "inputs" / f"{SOURCE_PLAN}.tex", settings.runtime_root / "lean-toolchain",
        settings.runtime_root / "lakefile.toml", settings.runtime_root / "lake-manifest.json"]
    write_json(run_root / "evidence-sha256.json", {p.relative_to(run_root).as_posix(): sha256(p)
               for p in sorted(set(paths)) if p.is_file()})
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New directory only; default is a preserved system temporary run")
    parser.add_argument("--repl-source", type=Path, default=REPO_ROOT / ".lake" / "packages" / "repl")
    parser.add_argument("--reviewer-argv-json", help="Opt into actual external review; command JSON with {input}, {prompt}, {result}, {request}, {run_metadata}")
    parser.add_argument("--reviewer-id", help="Actual external reviewer/runner identity (required in live mode)")
    parser.add_argument("--model", default=None, help="Actual model identifier, if known; absent means unreported")
    parser.add_argument("--reviewer-timeout", type=int, default=300)
    args = parser.parse_args(argv)
    if args.reviewer_argv_json and not args.reviewer_id:
        parser.error("Live review requires --reviewer-id; do not invent an identity.")
    run_root = (args.output or Path(tempfile.gettempdir()) / f"formalization-workflow-demo-{uuid.uuid4().hex[:12]}").resolve()
    print(f"Evidence: {run_root}", flush=True)
    print("Mode: " + ("EXTERNAL LIVE REVIEW" if args.reviewer_argv_json else "TEACHING REPLAY; no new semantic review"), flush=True)
    try:
        settings, ledger = prepare(run_root, args.repl_source.resolve())
        result = asyncio.run(execute(settings, ledger, args))
    except Exception as exc:
        if run_root.is_dir():
            write_json(run_root / "failure.json", {"completed": False, "error": str(exc),
                       "recorded_at": datetime.now(timezone.utc).isoformat()})
        print(f"Demo stopped: {exc}", file=sys.stderr)
        return 1
    print(f"Completed. Canonical SHA-256: {result['canonical_sha256']}")
    print(f"Inspect: {run_root / 'summary.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
