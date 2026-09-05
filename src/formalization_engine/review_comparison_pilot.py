"""Offline, paired review pilot. This module never invokes a model or runtime state."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Any


ARMS = ("ordinary", "reverse_translation")
USAGE_KEYS = ("input_tokens", "output_tokens", "elapsed_seconds", "cost_usd")
BUDGET_KEYS = USAGE_KEYS[:3]
PROVENANCES = ("synthetic_test_only", "independent_human")


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                    separators=(",", ":")).encode("utf-8")).hexdigest()


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_new(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, ensure_ascii=False, indent=2)
        handle.write("\n")


def _numbers(value: Any, keys: tuple[str, ...]) -> dict[str, float | None]:
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ValueError(f"expected numeric fields {keys}")
    for key in keys:
        number = value[key]
        if key == "cost_usd" and number is None:
            continue
        if (isinstance(number, bool) or not isinstance(number, (float, int))
                or not math.isfinite(number) or number < 0):
            raise ValueError(f"invalid {key}")
        if key.endswith("tokens") and not isinstance(number, int):
            raise ValueError(f"{key} must be an integer")
    return value


def _add_usage(total: dict[str, Any], addition: dict[str, Any]) -> None:
    for key in USAGE_KEYS:
        total[key] = None if total[key] is None or addition[key] is None else total[key] + addition[key]


def load_manifest(path: Path) -> dict[str, Any]:
    manifest = read_json(path)
    if not isinstance(manifest, dict) or manifest.get("schema_version") != 1:
        raise ValueError("unsupported manifest schema")
    if not isinstance(manifest.get("model"), str) or not manifest["model"].strip():
        raise ValueError("pin an exact model identifier before preparing requests")
    if not isinstance(manifest.get("model_config", {}), dict):
        raise ValueError("model_config must be an object")
    _numbers(manifest.get("budget"), BUDGET_KEYS)
    tasks = manifest.get("tasks")
    if not isinstance(tasks, list) or not 1 <= len(tasks) <= 8:
        raise ValueError("pilot requires 1 to 8 tasks")
    ids: set[str] = set()
    for task in tasks:
        if not isinstance(task, dict):
            raise ValueError("task must be an object")
        task_id = task.get("task_id", "")
        if (not isinstance(task_id, str) or not task_id or
                any(c not in "abcdefghijklmnopqrstuvwxyz0123456789_-" for c in task_id)
                or task_id in ids):
            raise ValueError("task identifiers must be unique, neutral path-safe labels")
        ids.add(task_id)
        for kind in ("source", "lean"):
            entry = task.get(kind)
            if (not isinstance(entry, dict) or not isinstance(entry.get("path"), str)
                    or not isinstance(entry.get("sha256"), str)):
                raise ValueError(f"{kind} requires a path and SHA-256")
            target = (path.parent / entry["path"]).resolve()
            if not target.is_relative_to(path.parent.resolve()):
                raise ValueError("task input escapes manifest directory")
            raw = target.read_bytes()
            if hashlib.sha256(raw).hexdigest() != entry["sha256"]:
                raise ValueError(f"input hash mismatch: {task_id}/{kind}")
            task[f"{kind}_text"] = raw.decode("utf-8")
    manifest["manifest_sha256"] = digest(read_json(path))
    return manifest


def _subject(task: dict[str, Any]) -> str:
    return digest({kind: task[kind]["sha256"] for kind in ("source", "lean")})


def _request(manifest: dict[str, Any], task: dict[str, Any], stage: str,
             translation: dict[str, Any] | None = None) -> dict[str, Any]:
    budget = manifest["budget"].copy()
    value: dict[str, Any] = {
        "schema_version": 1, "task_id": task["task_id"], "stage": stage,
        "model": manifest["model"], "budget": budget,
        "model_config": manifest.get("model_config", {}),
        "lean": task["lean_text"],
    }
    if stage == "translate":
        # Deliberately omit source text, source paths, subject/manifest hashes,
        # truth, and all ordinary-arm responses from the isolated translator.
        value["instruction"] = (
            "Translate the Lean declarations into natural language. State every "
            "assumption, quantifier, domain, and conclusion literally; explain "
            "which claims are inputs rather than proved. Do not infer a source text."
        )
    else:
        value.update(source=task["source_text"], subject_sha256=_subject(task),
                     manifest_sha256=manifest["manifest_sha256"])
        value["instruction"] = (
            "Review fidelity of the Lean assumptions, domains, quantifiers, "
            "conclusions and derivation to the supplied source. Lean compilation "
            "alone is insufficient. Return pass, fail, or abstain with rationale. "
            "No reference verdict is supplied. Do not access other sessions."
        )
        if translation is not None:
            value["reverse_translation"] = translation["text"]
            value["translation_sha256"] = digest(translation)
            for key in BUDGET_KEYS:
                budget[key] -= translation["usage"][key]
    return value


def prepare(manifest_path: Path, output: Path) -> dict[str, Any]:
    manifest = load_manifest(manifest_path)
    if output.exists():
        raise ValueError("prepare output must not already exist")
    output.mkdir(parents=True)
    for task in manifest["tasks"]:
        root = output / task["task_id"]
        write_new(root / "ordinary.request.json", _request(manifest, task, "ordinary"))
        write_new(root / "translate.request.json", _request(manifest, task, "translate"))
    index = {"schema_version": 1, "manifest_sha256": manifest["manifest_sha256"],
             "tasks": [task["task_id"] for task in manifest["tasks"]],
             "status": "prepared_no_model_calls"}
    write_new(output / "index.json", index)
    return index


def _check_record(record: Any, request: dict[str, Any], *, translation: bool = False) -> None:
    if not isinstance(record, dict):
        raise ValueError("record must be an object")
    if record.get("request_sha256") != digest(request):
        raise ValueError("request hash mismatch")
    if record.get("model") != request["model"]:
        raise ValueError("model mismatch")
    if record.get("model_config", {}) != request["model_config"]:
        raise ValueError("model configuration mismatch")
    usage = _numbers(record.get("usage"), USAGE_KEYS)
    if any(usage[key] > request["budget"][key] for key in BUDGET_KEYS):
        raise ValueError("budget exceeded")
    if not isinstance(record.get("session_id"), str) or not record["session_id"].strip():
        raise ValueError("separate session identity required")
    if translation:
        if not isinstance(record.get("text"), str) or not record["text"].strip():
            raise ValueError("translation text missing")
    else:
        if record.get("subject_sha256") != request["subject_sha256"]:
            raise ValueError("subject hash mismatch")
        if record.get("task_id") != request["task_id"] or record.get("arm") != request["stage"]:
            raise ValueError("task/arm mismatch")
        if record.get("verdict") not in ("pass", "fail", "abstain"):
            raise ValueError("invalid verdict")
        if not isinstance(record.get("rationale"), str) or not record["rationale"].strip():
            raise ValueError("review rationale required")


def seal_translation(manifest_path: Path, prepared: Path, task_id: str,
                     response_path: Path) -> dict[str, Any]:
    manifest = load_manifest(manifest_path)
    task = next((t for t in manifest["tasks"] if t["task_id"] == task_id), None)
    if task is None:
        raise ValueError("unknown task")
    if read_json(prepared / "index.json")["manifest_sha256"] != manifest["manifest_sha256"]:
        raise ValueError("prepared manifest mismatch")
    request = _request(manifest, task, "translate")
    if read_json(prepared / task_id / "translate.request.json") != request:
        raise ValueError("translation request altered")
    response = read_json(response_path)
    _check_record(response, request, translation=True)
    root = prepared / task_id
    if (root / "translation.sealed.json").exists() or (root / "reverse_translation.request.json").exists():
        raise ValueError("translation already sealed; start a new preregistered run to replace it")
    write_new(root / "translation.sealed.json", response)
    assisted = _request(manifest, task, "reverse_translation", response)
    write_new(root / "reverse_translation.request.json", assisted)
    return {"task_id": task_id, "translation_sha256": digest(response),
            "request_sha256": digest(assisted), "status": "sealed_no_model_calls"}


def _truth(record: Any, task: dict[str, Any]) -> None:
    if not isinstance(record, dict) or record.get("subject_sha256") != _subject(task):
        raise ValueError("adjudication subject hash mismatch")
    if record.get("provenance") not in PROVENANCES:
        raise ValueError("unsupported truth provenance")
    if record.get("verdict") not in ("pass", "fail", "pending"):
        raise ValueError("invalid adjudication verdict")
    if record["verdict"] != "pending":
        if not isinstance(record.get("rationale"), str) or not record["rationale"].strip():
            raise ValueError("adjudication rationale required")
        if record["provenance"] == "independent_human":
            if (not isinstance(record.get("adjudicator_id"), str) or
                    not record["adjudicator_id"].strip() or
                    record.get("independent_of_review_arms") is not True or
                    record.get("blinded_to_arm_results") is not True):
                raise ValueError("independent blinded human adjudication attestation missing")


def _empty_arm() -> dict[str, Any]:
    return {"n": 0, "false_accept": 0, "false_reject": 0, "abstain": 0,
            "correct_decisive": 0, "usage": dict.fromkeys(USAGE_KEYS, 0)}


def score(manifest_path: Path, prepared: Path, results_path: Path,
          adjudications_path: Path) -> dict[str, Any]:
    manifest = load_manifest(manifest_path)
    if read_json(prepared / "index.json")["manifest_sha256"] != manifest["manifest_sha256"]:
        raise ValueError("prepared manifest mismatch")
    records, truths = read_json(results_path), read_json(adjudications_path)
    if not isinstance(records, list) or not isinstance(truths, list):
        raise ValueError("results and adjudications must be JSON arrays")
    report: dict[str, Any] = {"schema_version": 1,
        "manifest_sha256": manifest["manifest_sha256"],
        "results_sha256": digest(records), "adjudications_sha256": digest(truths),
        "claim": "offline scoring only; synthetic fixtures are not empirical evidence",
        "issues": [], "unadjudicated_tasks": [], "unpaired_tasks": [],
        "valid_review_records": 0, "groups": {},
        "paired_process": {"tasks": [], "same_verdict": 0, "verdict_pairs": {}, "arms": {
            arm: {"abstain": 0, "usage": dict.fromkeys(USAGE_KEYS, 0)} for arm in ARMS}}}

    def issue(kind: str, task_id: Any, detail: str) -> None:
        report["issues"].append({"kind": kind, "task_id": task_id, "detail": detail})

    tasks = {task["task_id"]: task for task in manifest["tasks"]}
    keyed: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for index, record in enumerate(records):
        if (not isinstance(record, dict) or not isinstance(record.get("task_id"), str)
                or not isinstance(record.get("arm"), str)):
            issue("invalid_record", None, f"result index {index}: malformed record")
            continue
        key = (record["task_id"], record["arm"])
        if key[0] not in tasks or key[1] not in ARMS:
            issue("invalid_record", key[0], f"result index {index}: unknown task/arm")
            continue
        keyed.setdefault(key, []).append(record)
    truth_by_id: dict[str, list[dict[str, Any]]] = {}
    for index, truth in enumerate(truths):
        if not isinstance(truth, dict) or not isinstance(truth.get("task_id"), str) or truth["task_id"] not in tasks:
            issue("invalid_adjudication", None, f"adjudication index {index}: unknown task")
            continue
        truth_by_id.setdefault(truth["task_id"], []).append(truth)

    valid_by_task: dict[str, dict[str, Any]] = {}
    sessions: dict[str, set[tuple[str, str]]] = {}
    for task_id, task in tasks.items():
        valid: dict[str, dict[str, Any]] = {}
        translation: dict[str, Any] | None = None
        translation_error = "sealed translation missing"
        try:
            translation_request = _request(manifest, task, "translate")
            if read_json(prepared / task_id / "translate.request.json") != translation_request:
                raise ValueError("prepared translation request altered")
            translation = read_json(prepared / task_id / "translation.sealed.json")
            _check_record(translation, translation_request, translation=True)
            sessions.setdefault(translation["session_id"], set()).add((task_id, "translate"))
        except (ValueError, OSError, KeyError, TypeError) as exc:
            translation_error = str(exc)
            translation = None
        for arm in ARMS:
            candidates = keyed.get((task_id, arm), [])
            if len(candidates) != 1:
                issue("duplicate" if candidates else "missing", task_id, arm)
                continue
            try:
                if arm == "reverse_translation":
                    if translation is None:
                        raise ValueError(translation_error)
                request = _request(manifest, task, arm, translation if arm == "reverse_translation" else None)
                if read_json(prepared / task_id / f"{arm}.request.json") != request:
                    raise ValueError("prepared review request altered")
                record = candidates[0]
                _check_record(record, request)
                valid[arm] = dict(record, usage=record["usage"].copy())
                sessions.setdefault(record["session_id"], set()).add((task_id, arm))
                if arm == "reverse_translation":
                    _add_usage(valid[arm]["usage"], translation["usage"])
            except (ValueError, OSError, KeyError, TypeError) as exc:
                issue("invalid_record", task_id, f"{arm}: {exc}")
        valid_by_task[task_id] = valid

    for session_id, owners in sessions.items():
        if len(owners) > 1:
            for task_id in sorted({owner[0] for owner in owners}):
                issue("invalid_pair", task_id,
                      f"session {session_id!r} reused across stages/tasks: {sorted(owners)}")
                valid_by_task[task_id].clear()

    for task_id, task in tasks.items():
        valid = valid_by_task[task_id]
        if len(valid) != 2:
            report["unpaired_tasks"].append(task_id)
        else:
            report["valid_review_records"] += 2
            report["paired_process"]["tasks"].append(task_id)
            process_pair = report["paired_process"]
            process_pair["same_verdict"] += int(valid[ARMS[0]]["verdict"] == valid[ARMS[1]]["verdict"])
            pair_key = f"{valid[ARMS[0]]['verdict']}->{valid[ARMS[1]]['verdict']}"
            process_pair["verdict_pairs"][pair_key] = process_pair["verdict_pairs"].get(pair_key, 0) + 1
            for arm in ARMS:
                process = report["paired_process"]["arms"][arm]
                process["abstain"] += int(valid[arm]["verdict"] == "abstain")
                _add_usage(process["usage"], valid[arm]["usage"])
        candidates = truth_by_id.get(task_id, [])
        truth = candidates[0] if len(candidates) == 1 else None
        try:
            if truth is None:
                raise ValueError("missing adjudication" if not candidates else "duplicate adjudications")
            _truth(truth, task)
        except (ValueError, TypeError) as exc:
            issue("invalid_adjudication", task_id, str(exc))
            truth = None
        if truth is None or truth["verdict"] == "pending":
            report["unadjudicated_tasks"].append(task_id)
            continue
        if len(valid) != 2:
            continue
        if truth["provenance"] == "independent_human" and truth["adjudicator_id"] in sessions:
            issue("invalid_adjudication", task_id, "adjudicator identity overlaps review/translation")
            report["unadjudicated_tasks"].append(task_id)
            continue
        group = report["groups"].setdefault(truth["provenance"], {
            "paired_tasks": [], "truth_pass": 0, "truth_fail": 0,
            "arms": {arm: _empty_arm() for arm in ARMS}, "paired_outcomes": {}})
        group["paired_tasks"].append(task_id)
        group[f"truth_{truth['verdict']}"] += 1
        outcome = f"{valid[ARMS[0]]['verdict']}->{valid[ARMS[1]]['verdict']}"
        group["paired_outcomes"][outcome] = group["paired_outcomes"].get(outcome, 0) + 1
        for arm in ARMS:
            stats, record = group["arms"][arm], valid[arm]
            stats["n"] += 1
            verdict = record["verdict"]
            category = ("abstain" if verdict == "abstain" else
                        "correct_decisive" if verdict == truth["verdict"] else
                        "false_accept" if verdict == "pass" else "false_reject")
            stats[category] += 1
            _add_usage(stats["usage"], record["usage"])
    for group in report["groups"].values():
        group["reverse_minus_ordinary"] = {
            metric: group["arms"][ARMS[1]][metric] - group["arms"][ARMS[0]][metric]
            for metric in ("false_accept", "false_reject", "abstain")}
        ordinary_cost = group["arms"][ARMS[0]]["usage"]["cost_usd"]
        assisted_cost = group["arms"][ARMS[1]]["usage"]["cost_usd"]
        group["cost_usd_difference"] = (None if ordinary_cost is None or assisted_cost is None
                                        else assisted_cost - ordinary_cost)
    report["qa_status"] = "issues_present" if report["issues"] else "valid"
    report["empirical_status"] = ("independent_human_pairs_available" if
        "independent_human" in report["groups"] else "pending_independent_human_adjudication")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for command in ("prepare", "seal-translation", "score"):
        part = sub.add_parser(command)
        part.add_argument("--manifest", type=Path, required=True)
        if command == "prepare":
            part.add_argument("--output", type=Path, required=True)
        else:
            part.add_argument("--prepared", type=Path, required=True)
        if command == "seal-translation":
            part.add_argument("--task", required=True)
            part.add_argument("--response", type=Path, required=True)
        elif command == "score":
            part.add_argument("--results", type=Path, required=True)
            part.add_argument("--adjudications", type=Path, required=True)
            part.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            result = prepare(args.manifest, args.output)
        elif args.command == "seal-translation":
            result = seal_translation(args.manifest, args.prepared, args.task, args.response)
        else:
            result = score(args.manifest, args.prepared, args.results, args.adjudications)
            if args.output:
                write_new(args.output, result)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        parser.exit(2, f"pilot input rejected: {exc}\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 1 if result.get("qa_status") == "issues_present" else 0


if __name__ == "__main__":
    raise SystemExit(main())
