"""Transport/isolation regressions; the real Lean sequence runs via the demo CLI."""
import argparse
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from tools.run_workflow_demo import FIXTURES, SOURCE_PLAN, prepare, prepare_math_review, replay_review, run_reviewer, write_json


class WorkflowDemoTests(unittest.TestCase):
    def test_existing_output_is_refused_before_any_write(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sentinel = root / "protected.txt"
            sentinel.write_text("keep", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "existing output"):
                prepare(root, root / "missing_repl")
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "keep")
            self.assertEqual(list(root.iterdir()), [sentinel])

    def _request(self, root: Path):
        input_path, result_path = root / "input.json", root / "result.json"
        write_json(input_path, {"candidate": {"lean": "immutable input"}})
        request_path = root / "request.json"
        write_json(request_path, {"review_input_file": str(input_path),
                                 "expected_result_file": str(result_path),
                                 "review_prompt_file": str(root / "prompt.md")})
        (root / "prompt.md").write_text("Read only", encoding="utf-8")
        return request_path, input_path, result_path

    def test_replay_refuses_a_changed_intermediate_fixture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("source.tex", "initial.lean", "interface-only.lean", "final.lean", "teaching-review.json"):
                shutil.copyfile(FIXTURES / name, root / name)
            (root / "interface-only.lean").write_text("unrelated syntax error", encoding="utf-8")
            review_input = {"candidate": {"lean": (root / "initial.lean").read_text(encoding="utf-8")}}
            with patch("tools.run_workflow_demo.FIXTURES", root):
                with self.assertRaisesRegex(ValueError, "interface-only.lean"):
                    replay_review(review_input, root / "input.json", "initial")

    def _args(self, script: str):
        return argparse.Namespace(
            reviewer_argv_json=json.dumps([sys.executable, "-c", script, "{input}", "{result}", "{run_metadata}"]),
            reviewer_timeout=20, reviewer_id="unit-test-subprocess-transport", model=None)

    def test_math_route_replay_refuses_changed_skeleton_and_incomplete_rounds(self):
        for mutation in ("skeleton", "rounds"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                fixtures, runtime, pack = root / "fixtures", root / "runtime", root / "pack"
                fixtures.mkdir()
                pack.mkdir()
                (runtime / "inputs").mkdir(parents=True)
                for name in ("math-proof-skeleton.md", "math-review.json"):
                    shutil.copyfile(FIXTURES / name, fixtures / name)
                shutil.copyfile(FIXTURES / "source.tex", runtime / "inputs" / f"{SOURCE_PLAN}.tex")
                if mutation == "skeleton":
                    (fixtures / "math-proof-skeleton.md").write_text("A different unreviewed route.", encoding="utf-8")
                else:
                    payload = json.loads((fixtures / "math-review.json").read_text(encoding="utf-8"))
                    payload["rounds"] = payload["rounds"][:2]
                    write_json(fixtures / "math-review.json", payload)
                expected = "exact teaching source and skeleton" if mutation == "skeleton" else "three explicit go"
                with patch("tools.run_workflow_demo.FIXTURES", fixtures):
                    with self.assertRaisesRegex(RuntimeError, expected):
                        prepare_math_review(pack, SimpleNamespace(runtime_root=runtime),
                                            argparse.Namespace(reviewer_argv_json=None))

    def test_external_runner_input_change_is_detected_and_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request, input_path, result = self._request(root)
            script = "import pathlib,sys; pathlib.Path(sys.argv[1]).write_text('changed'); pathlib.Path(sys.argv[2]).write_text('[]')"
            with self.assertRaisesRegex(RuntimeError, "changed input/runtime"):
                run_reviewer(root, request, self._args(script))
            metadata = json.loads((root / "result_runner.json").read_text(encoding="utf-8"))
            self.assertIn("input.json", metadata["persisted_input_changes"])
            self.assertEqual(input_path.read_text(encoding="utf-8"), "changed")
            self.assertTrue(result.exists())

    def test_external_result_and_optional_cost_are_preserved_without_filling_verdict(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request, input_path, result = self._request(root)
            original = input_path.read_bytes()
            script = (
                "import pathlib,sys,json; "
                "pathlib.Path(sys.argv[2]).write_text('[]'); "
                "pathlib.Path(sys.argv[3]).write_text(json.dumps(dict(cost_usd=0.125, tokens=12)))"
            )
            self.assertEqual(run_reviewer(root, request, self._args(script)), result)
            self.assertEqual(input_path.read_bytes(), original)
            self.assertEqual(result.read_text(), "[]")
            metadata = json.loads((root / "result_runner.json").read_text(encoding="utf-8"))
            self.assertEqual(metadata["runner_reported"], {"cost_usd": 0.125, "tokens": 12})
            self.assertEqual(metadata["persisted_input_changes"], [])
            self.assertIsNone(metadata["model"])
            self.assertTrue(metadata["run_id"])


if __name__ == "__main__":
    unittest.main()
