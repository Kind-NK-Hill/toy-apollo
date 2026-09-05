"""Exercise scoring with fabricated responses; no provider calls or empirical claims."""
from pathlib import Path
import json
import sys
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from formalization_engine.review_comparison_pilot import (
    digest, prepare, read_json, score, seal_translation, write_new,
)


def main():
    manifest_path = Path(__file__).with_name("manifest.json")
    manifest = read_json(manifest_path)
    with TemporaryDirectory(prefix="review-comparison-fixture-") as directory:
        root = Path(directory)
        prepared = root / "prepared"
        prepare(manifest_path, prepared)
        results, adjudications = [], []
        for task in manifest["tasks"]:
            task_id = task["task_id"]
            request = read_json(prepared / task_id / "translate.request.json")
            translation_path = root / f"{task_id}.translation.json"
            write_new(translation_path, {
                "request_sha256": digest(request), "model": manifest["model"],
                "session_id": f"synthetic-translate-{task_id}",
                "text": "Fabricated response for testing accounting and binding only.",
                "usage": {"input_tokens": 10, "output_tokens": 10,
                          "elapsed_seconds": 1, "cost_usd": 0},
            })
            seal_translation(manifest_path, prepared, task_id, translation_path)
            verdicts = ("fail", "pass") if task_id == "case01" else ("pass", "abstain")
            for arm, verdict in zip(("ordinary", "reverse_translation"), verdicts):
                request = read_json(prepared / task_id / f"{arm}.request.json")
                results.append({
                    "task_id": task_id, "arm": arm, "request_sha256": digest(request),
                    "subject_sha256": request["subject_sha256"], "model": manifest["model"],
                    "session_id": f"synthetic-{arm}-{task_id}", "verdict": verdict,
                    "rationale": "Fabricated scorer branch coverage; not a real review.",
                    "usage": {"input_tokens": 20, "output_tokens": 20,
                              "elapsed_seconds": 2, "cost_usd": 0},
                })
            adjudications.append({
                "task_id": task_id, "subject_sha256": request["subject_sha256"],
                "provenance": "synthetic_test_only",
                "verdict": "pass" if task_id == "case01" else "fail",
                "rationale": "Assigned test label for scorer branch coverage; not human adjudication.",
            })
        write_new(root / "results.json", results)
        write_new(root / "adjudications.json", adjudications)
        report = score(manifest_path, prepared, root / "results.json", root / "adjudications.json")
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0 if report["qa_status"] == "valid" else 1


if __name__ == "__main__":
    raise SystemExit(main())
