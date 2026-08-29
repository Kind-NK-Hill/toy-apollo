import asyncio
import hashlib
import json
import shutil
import sys
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.core.settings import Settings  # noqa: E402
from src.toy_apollo.phase2_pack_shared.io import write_text  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import build_check_prompt_pack_candidate, write_prompt_pack  # noqa: E402
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
)


class Phase2ReviewTestSupport:
    def _make_settings(self, root: Path, plans_dir: Path) -> Settings:
        return Settings(
            runtime_root=root,
            artifact_root=root,
            plans_dir=plans_dir,
            reports_dir=root / "reports",
            formalized_chapters_dir=root / "formalized_chapters",
            output_lean_files_dir=root / "output_lean_files",
            phase2_prompt_packs_dir=root / "phase2_prompt_packs",
            phase2_softdep_packs_dir=root / "phase2_softdep_packs",
            error_logs_dir=root / "error_logs",
            toyapollo_output_dir=root / "ToyApollo" / "Output",
            aristotle_outbox_dir=root / "aristotle_outbox",
            aristotle_archives_dir=root / "aristotle_archives",
            mathlib_index_file=root / "mathlib_index.faiss",
            mathlib_corpus_file=root / "mathlib_corpus.json",
            project_ledger_file=root / "project_ledger.json",
            lab_notebook_file=root / "lab_notebook.json",
            mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
        )

    def _fake_reviewer_env(self, root: Path, verdict: str = "pass") -> dict[str, str]:
        script = root / f"fake_reviewer_{verdict}.py"
        source_claims = [{"claim": "source claim", "status": "covered"}] if verdict == "pass" else []
        claim_mapping = [{"claim": "source claim", "lean": "target declaration"}] if verdict == "pass" else []
        interface_contract = {
            "status": "covered" if verdict == "pass" else "violated",
            "summary": f"fake reviewer interface {verdict}",
            "mismatches": [],
        }
        forbidden_weakenings = [{"status": "not_present", "summary": "fake reviewer weakening check"}] if verdict == "pass" else []
        payload = {
            "verdict": verdict,
            "confidence": "high" if verdict == "pass" else "medium",
            "summary": f"fake reviewer {verdict}",
            "proof_class": "textbook_proof_completed" if verdict == "pass" else "open_math_debt",
            "completion_class": "textbook_proof_completed" if verdict == "pass" else "open_math_debt",
            "reviewer_independence": {
                "role": "independent_read_only_reviewer",
                "read_only": True,
                "did_edit_candidate": False,
                "used_current_review_request": True,
                "attestation": "fake test reviewer is independent and read-only",
            },
            "source_claims": source_claims,
            "claim_mapping": claim_mapping,
            "route_inspection": {
                "status": "covered" if verdict == "pass" else "violated",
                "source_route": "fake reviewer checked the source route" if verdict == "pass" else "",
                "expected_answer_or_statement": "fake reviewer checked the expected statement" if verdict == "pass" else "",
                "local_mathlib_search": "fake reviewer checked local and Mathlib routes" if verdict == "pass" else "",
                "public_interface_check": "fake reviewer found no public-premise relocation" if verdict == "pass" else "",
                "support_or_reassembly_decision": "no family reassembly needed for this fixture" if verdict == "pass" else "",
                "stop_go_verdict": "go" if verdict == "pass" else "stop",
                "notes": f"fake reviewer route inspection {verdict}",
            },
            "spine_alignment": {
                "status": "covered" if verdict == "pass" else "violated",
                "summary": f"fake reviewer spine {verdict}",
                "source_steps_checked": [
                    {
                        "source_step": "source claim",
                        "lean_landing": "target declaration",
                        "landing_kind": "theorem",
                        "signature_match": "passed",
                        "body_reassumption_check": "passed",
                        "public_premise_check": "passed",
                        "notes": "direct fixture proof",
                    }
                ]
                if verdict == "pass"
                else [],
                "missing_source_steps": [] if verdict == "pass" else [{"source_step": "source claim"}],
                "shortcut_assessment": "faithful_abstraction" if verdict == "pass" else "unclear",
            },
            "interface_contract": interface_contract,
            "downstream_adequacy": {
                "status": "covered" if verdict == "pass" else "violated",
                "summary": f"fake reviewer downstream {verdict}",
                "consumers_checked": [],
                "blocking_issues": [],
            },
            "forbidden_weakenings": forbidden_weakenings,
            "findings": [] if verdict == "pass" else [{"severity": "error", "category": "faithfulness", "message": f"fake {verdict}"}],
            "recommended_disposition": "promote" if verdict == "pass" else "revise",
        }
        script.write_text(
            "import hashlib, json, sys\n"
            "input_path = sys.argv[sys.argv.index('--input') + 1]\n"
            "result = sys.argv[sys.argv.index('--result') + 1]\n"
            "review_input = json.loads(open(input_path, 'r', encoding='utf-8').read())\n"
            "consumers = []\n"
            "review_basis = review_input.get('review_basis', {})\n"
            "if isinstance(review_basis, dict):\n"
            "    raw_consumers = review_basis.get('direct_downstream_consumers', [])\n"
            "    if isinstance(raw_consumers, list):\n"
            "        for item in raw_consumers:\n"
            "            if isinstance(item, dict) and item.get('block_id'):\n"
            "                consumers.append({\n"
            "                    'block_id': item.get('block_id'),\n"
            "                    'relation': item.get('relation', ''),\n"
            "                    'status': 'covered',\n"
            "                    'evidence': 'fake reviewer coverage',\n"
            "                })\n"
            f"payload = {repr(payload)}\n"
            "payload.update({\n"
            "    'task_id': review_input.get('task', {}).get('block_id', ''),\n"
            "    'candidate_hash': review_input.get('candidate', {}).get('hash', ''),\n"
            "    'prompt_version': review_input.get('prompt_version'),\n"
            "    'rubric_version': review_input.get('rubric_version'),\n"
            "    'review_input_hash': hashlib.sha256(json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(\",\", \":\")).encode('utf-8')).hexdigest(),\n"
            "    'review_input_file': input_path,\n"
            "})\n"
            f"if {verdict == 'pass'!r}:\n"
            "    payload['downstream_adequacy']['consumers_checked'] = consumers\n"
            "open(result, 'w', encoding='utf-8').write(json.dumps(payload, ensure_ascii=False))\n",
            encoding="utf-8",
        )
        return {
            "TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON": json.dumps(
                [sys.executable, str(script), "--input", "{input}", "--result", "{result}"],
                ensure_ascii=False,
            ),
            "TOY_APOLLO_PHASE2_REVIEWER_BACKEND_ID": f"fake/{verdict}",
        }

    def _setup_trivial_phase2_task(
        self,
        root: Path,
        task_id: str,
        *,
        candidate_code: str | None = None,
        completed: bool = False,
    ):
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True, exist_ok=True)
        (plans_dir / "08_chap4_measurable_functions_plan.json").write_text(
            f"""
[
  {{
    "block_id": "{task_id}",
    "type": "Theorem",
    "title": "Codex Review Handoff",
    "content": "Show a trivial theorem.",
    "dependencies": []
  }}
]
            """.strip(),
            encoding="utf-8",
        )
        ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
        ledger.add_or_update_task(
            {
                "block_id": task_id,
                "type": "Theorem",
                "title": "Codex Review Handoff",
                "content": "Show a trivial theorem.",
                "source_plan": "08_chap4_measurable_functions",
                "dependencies": [],
            }
        )
        settings = self._make_settings(root, plans_dir)
        source_tex = settings.runtime_root / "inputs" / "08_chap4_measurable_functions.tex"
        source_tex.parent.mkdir(parents=True, exist_ok=True)
        source_tex.write_text("Show a trivial theorem.\n", encoding="utf-8")
        official_code = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
        output_path = settings.toyapollo_output_dir / f"{task_id}.lean"
        if completed:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(official_code, encoding="utf-8")
            ledger.register_success(task_id, official_code, ledger._hash_text(official_code))
        pack_dir = write_prompt_pack(task_id, ledger, settings)
        if completed:
            ledger.update_status(task_id, TaskStatus.COMPLETED)
        write_text(pack_dir / "draft.lean", candidate_code or official_code)
        return ledger, settings, pack_dir, output_path

    def _append_direct_downstream_consumer(self, plans_dir: Path, dependency_id: str, consumer_id: str) -> None:
        plan_path = plans_dir / "09_chap4_composition_plan.json"
        tasks = []
        if plan_path.exists():
            tasks = json.loads(plan_path.read_text(encoding="utf-8"))
        tasks.append(
            {
                "block_id": consumer_id,
                "type": "Theorem",
                "title": f"Consumer {consumer_id}",
                "content": "Consume an upstream theorem.",
                "dependencies": [dependency_id],
            }
        )
        plan_path.write_text(json.dumps(tasks, indent=2, ensure_ascii=False), encoding="utf-8")

    def _write_codex_review_result(
        self,
        pack_dir: Path,
        *,
        verdict: str,
        source_claims: list[dict] | None = None,
        claim_mapping: list[dict] | None = None,
        candidate_hash: str | None = None,
        obligation_review: dict | None = None,
        evidence_review: dict | None = None,
        proof_class: str | None = None,
        completion_class: str | None = None,
    ) -> Path:
        request_path = pack_dir / "semantic_review_request.json"
        if request_path.exists():
            review_request = json.loads(request_path.read_text(encoding="utf-8"))
            review_input_path = Path(str(review_request["review_input_file"]))
            result_path = Path(str(review_request["expected_result_file"]))
        else:
            review_input_path = pack_dir / "semantic_review_input_v1.json"
            result_path = pack_dir / "semantic_review_result_v1.json"
        review_input = json.loads(review_input_path.read_text(encoding="utf-8"))
        required_evidence = review_input.get("review_basis", {}).get("required_evidence_classes", [])
        if not isinstance(required_evidence, list) or not required_evidence:
            required_evidence = [
                "source_tex",
                "lean_subject",
                "audit",
                "classification",
                "dependency_status",
                "downstream",
                "ledger_status",
                "hashes",
            ]
        direct_consumers = review_input.get("review_basis", {}).get("direct_downstream_consumers", [])
        consumers_checked = []
        if verdict == "pass" and isinstance(direct_consumers, list):
            for consumer in direct_consumers:
                if isinstance(consumer, dict) and consumer.get("block_id"):
                    consumers_checked.append(
                        {
                            "block_id": consumer["block_id"],
                            "relation": consumer.get("relation", ""),
                            "status": "covered",
                            "evidence": "manual reviewer coverage",
                        }
                    )
        normalized_proof_class = proof_class if proof_class is not None else ("textbook_proof_completed" if verdict == "pass" else "open_math_debt")
        normalized_completion_class = completion_class if completion_class is not None else normalized_proof_class
        prompt_version = review_input.get("prompt_version", SEMANTIC_REVIEW_PROMPT_VERSION)
        legacy_obligation_schema = int(prompt_version) <= 10
        if legacy_obligation_schema:
            spine_alignment = {
                "status": "covered" if verdict == "pass" else "violated",
                "summary": f"manual spine {verdict}",
                "obligations_checked": (
                    [
                        {
                            "source_obligation": "source claim",
                            "lean_landing": review_input["task"]["block_id"],
                            "status": "covered",
                        }
                    ]
                    if verdict == "pass"
                    else []
                ),
                "missing_obligations": [],
                "shortcut_assessment": "faithful_abstraction" if verdict == "pass" else "unclear",
            }
        else:
            spine_alignment = {
                "status": "covered" if verdict == "pass" else "violated",
                "summary": f"manual spine {verdict}",
                "source_steps_checked": (
                    [
                        {
                            "source_step": "source claim",
                            "lean_landing": review_input["task"]["block_id"],
                            "landing_kind": "theorem",
                            "signature_match": "passed",
                            "body_reassumption_check": "passed",
                            "public_premise_check": "passed",
                            "notes": "the theorem directly discharges the source step",
                        }
                    ]
                    if verdict == "pass"
                    else []
                ),
                "missing_source_steps": [] if verdict == "pass" else [{"source_step": "source claim"}],
                "shortcut_assessment": "faithful_abstraction" if verdict == "pass" else "unclear",
            }
        payload = {
                    "task_id": review_input["task"]["block_id"],
                    "review_input_hash": hashlib.sha256(
                        json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
                    ).hexdigest(),
                    "candidate_hash": candidate_hash if candidate_hash is not None else review_input["candidate"]["hash"],
                    "prompt_version": prompt_version,
                    "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
                    "review_input_file": str(review_input_path),
                    "verdict": verdict,
                    "confidence": "high",
                    "summary": f"manual codex review {verdict}",
                    "proof_class": normalized_proof_class,
                    "completion_class": normalized_completion_class,
                    "reviewer_independence": {
                        "role": "independent_read_only_reviewer",
                        "read_only": True,
                        "did_edit_candidate": False,
                        "used_current_review_request": True,
                        "attestation": "manual test reviewer is independent and read-only",
                    },
                    "source_claims": source_claims if source_claims is not None else [{"claim": "source claim"}],
                    "claim_mapping": claim_mapping
                    if claim_mapping is not None
                    else [{"source_claim": "source claim", "lean_declaration": review_input["task"]["block_id"]}],
                    "route_inspection": {
                        "status": "covered" if verdict == "pass" else "violated",
                        "source_route": "manual reviewer checked the source route" if verdict == "pass" else "",
                        "expected_answer_or_statement": "manual reviewer checked the expected statement" if verdict == "pass" else "",
                        "local_mathlib_search": "manual reviewer checked local and Mathlib routes" if verdict == "pass" else "",
                        "public_interface_check": "manual reviewer found no public-premise relocation" if verdict == "pass" else "",
                        "support_or_reassembly_decision": "no family reassembly needed for this fixture" if verdict == "pass" else "",
                        "stop_go_verdict": "go" if verdict == "pass" else "stop",
                        "notes": f"manual route inspection {verdict}",
                    },
                    "spine_alignment": spine_alignment,
                    "evidence_review": evidence_review
                    if evidence_review is not None
                    else {
                        "status": "covered" if verdict == "pass" else "violated",
                        "summary": f"manual evidence review {verdict}",
                        "items": [
                            {
                                "evidence_class": str(item),
                                "status": "covered" if verdict == "pass" else "violated",
                                "evidence": f"manual reviewer checked {item}",
                            }
                            for item in required_evidence
                        ],
                        "blocking_issues": []
                        if verdict == "pass"
                        else [{"evidence_class": "source_tex", "issue": f"manual {verdict} evidence blocker"}],
                    },
                    "interface_contract": {
                        "status": "covered" if verdict == "pass" else "violated",
                        "summary": f"manual interface {verdict}",
                        "mismatches": [],
                    },
                    "downstream_adequacy": {
                        "status": "covered" if verdict == "pass" else "violated",
                        "summary": f"manual downstream {verdict}",
                        "consumers_checked": consumers_checked,
                        "blocking_issues": [],
                    },
                    "forbidden_weakenings": [{"status": "not_present", "summary": "manual weakening check"}] if verdict == "pass" else [],
                    "findings": [],
                    "recommended_disposition": "promote" if verdict == "pass" else "revise",
                }
        if legacy_obligation_schema:
            payload["obligation_review"] = (
                obligation_review
                if obligation_review is not None
                else {
                    "status": "covered" if verdict == "pass" else "violated",
                    "summary": f"manual obligation review {verdict}",
                    "items": [],
                    "open_blockers": []
                    if verdict == "pass"
                    else [{"obligation_id": "source_claim", "issue": f"manual {verdict} blocker"}],
                    "scaffold_assessment": [],
                }
            )
        result_path.write_text(
            json.dumps(
                payload,
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )
        return result_path

    def _run_successful_build_check(self, task_id: str, ledger: LedgerManager, settings):
        with patch(
            "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
            new=AsyncMock(return_value=(True, "repl ok")),
        ), patch(
            "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
            new=AsyncMock(return_value=(True, "temp build ok")),
        ), patch(
            "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
            return_value=(True, "final build ok"),
        ):
            return asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

    def _clean_root(self, root: Path) -> None:
        if root.exists():
            shutil.rmtree(root, ignore_errors=True)
