import os
import sys
import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.compiler import LeanREPL  # noqa: E402


class LeanREPLTests(unittest.TestCase):
    def test_run_oneshot_uses_default_timeout_when_env_missing(self):
        with patch.dict(os.environ, {}, clear=True):
            repl = LeanREPL(str(REPO_ROOT))
        self.assertEqual(repl.timeout_seconds, 300)

    def test_run_oneshot_uses_configured_timeout(self):
        class FakeProcess:
            def __init__(self):
                self.pid = 12345
                self.returncode = 0
                self.timeout = None

            def communicate(self, timeout=None):
                self.timeout = timeout
                return ("{}", "")

        with patch.dict(os.environ, {"FORMALIZATION_ENGINE_REPL_TIMEOUT_SECONDS": "120"}, clear=False):
            fake_process = FakeProcess()
            repl = LeanREPL(str(REPO_ROOT))
            with patch("formalization_engine.compiler.subprocess.Popen", return_value=fake_process):
                repl._run_oneshot({"cmd": "#check True"})

        self.assertEqual(fake_process.timeout, 120)

    def test_run_oneshot_timeout_kills_process_tree_and_removes_input_file(self):
        class FakeProcess:
            def __init__(self):
                self.pid = 43210
                self.returncode = None
                self._calls = 0

            def communicate(self, timeout=None):
                self._calls += 1
                if self._calls == 1:
                    raise subprocess.TimeoutExpired(
                        cmd="lake exe repl < repl_input_deadbeef.json",
                        timeout=timeout,
                    )
                return ("", "")

        repl_input = REPO_ROOT / "repl_input_deadbeef.json"
        if repl_input.exists():
            repl_input.unlink()

        with patch.dict(os.environ, {}, clear=True), patch(
            "formalization_engine.compiler.uuid.uuid4",
            return_value="deadbeefcafebabe",
        ), patch(
            "formalization_engine.compiler.subprocess.Popen",
            return_value=FakeProcess(),
        ) as popen_mock, patch(
            "formalization_engine.compiler.subprocess.run"
        ) as run_mock:
            run_mock.return_value.returncode = 0
            run_mock.return_value.stdout = ""
            run_mock.return_value.stderr = ""
            repl = LeanREPL(str(REPO_ROOT))

            result = repl._run_oneshot({"cmd": "#check True"})

        self.assertIn("timed out after 300 seconds", result["error"])
        self.assertIn("cleanup: terminated process tree", result["error"])
        self.assertFalse(repl_input.exists())
        self.assertEqual(popen_mock.call_args.kwargs["timeout"] if "timeout" in popen_mock.call_args.kwargs else None, None)
        self.assertEqual(run_mock.call_args.args[0][:4], ["taskkill", "/T", "/F", "/PID"])
        self.assertEqual(run_mock.call_args.args[0][4], "43210")


if __name__ == "__main__":
    unittest.main()
