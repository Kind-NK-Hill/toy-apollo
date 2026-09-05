import os
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
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
                self.kill_calls = 0

            def kill(self):
                self.kill_calls += 1

            def communicate(self, timeout=None):
                self._calls += 1
                if self._calls == 1:
                    raise subprocess.TimeoutExpired(
                        cmd="lake exe repl < repl_input_deadbeef.json",
                        timeout=timeout,
                    )
                return ("", "")

        for platform in ("nt", "posix"):
            with self.subTest(platform=platform), tempfile.TemporaryDirectory() as tmp:
                fake_process = FakeProcess()
                with patch.dict(os.environ, {}, clear=True):
                    repl = LeanREPL(str(REPO_ROOT), temp_dir=tmp)
                repl_input = repl.temp_dir / "repl_input_deadbeef.json"
                # Replace only the compiler's platform view, not global os.name:
                # pathlib must retain the host's real filesystem implementation.
                with patch("formalization_engine.compiler.os", SimpleNamespace(name=platform)), patch(
                    "formalization_engine.compiler.uuid.uuid4",
                    return_value="deadbeefcafebabe",
                ), patch(
                    "formalization_engine.compiler.subprocess.Popen",
                    return_value=fake_process,
                ) as popen_mock, patch(
                    "formalization_engine.compiler.subprocess.run"
                ) as run_mock:
                    run_mock.return_value.returncode = 0
                    run_mock.return_value.stdout = ""
                    run_mock.return_value.stderr = ""
                    result = repl._run_oneshot({"cmd": "#check True"})

                self.assertIn("timed out after 300 seconds", result["error"])
                self.assertFalse(repl_input.exists())
                self.assertIsNone(popen_mock.call_args.kwargs.get("timeout"))
                if platform == "nt":
                    self.assertIn("cleanup: terminated process tree via taskkill", result["error"])
                    run_mock.assert_called_once()
                    self.assertEqual(run_mock.call_args.args[0], ["taskkill", "/T", "/F", "/PID", "43210"])
                    self.assertEqual(fake_process.kill_calls, 0)
                else:
                    self.assertIn("cleanup: terminated process via kill()", result["error"])
                    run_mock.assert_not_called()
                    self.assertEqual(fake_process.kill_calls, 1)


if __name__ == "__main__":
    unittest.main()
