"""Provider-free checks of the optional CLI runner's exclusion boundary."""
import json
from pathlib import Path
import unittest

from tools.run_codex_review_pilot import DISABLED_FEATURES, command_for, parse_events


class CodexReviewPilotRunnerTests(unittest.TestCase):
    def events(self, extra=()):
        return "\n".join(json.dumps(event) for event in [
            {"type": "thread.started", "thread_id": "real-provider-session"},
            *extra,
            {"type": "item.completed", "item": {"type": "agent_message", "text": '{"verdict":"pass"}'}},
            {"type": "turn.completed", "usage": {"input_tokens": 120, "output_tokens": 20}},
        ])

    def test_extracts_actual_session_usage_without_fabricating_cost(self):
        parsed = parse_events(self.events())
        self.assertEqual(parsed["session_id"], "real-provider-session")
        self.assertEqual(parsed["provider_usage"]["input_tokens"], 120)
        self.assertNotIn("cost_usd", parsed["provider_usage"])
        self.assertEqual(parsed["problems"], [])

    def test_any_non_message_item_excludes_tools_even_unknown_future_types(self):
        for tool in ("command_execution", "mcp_tool_call", "web_search", "future_tool"):
            with self.subTest(tool=tool):
                parsed = parse_events(self.events([{"type": "item.started", "item": {"type": tool}}]))
                self.assertEqual(len(parsed["tool_events"]), 1)

    def test_missing_or_duplicate_receipts_are_not_inferred(self):
        self.assertTrue(parse_events("")["problems"])
        parsed = parse_events(self.events([{"type": "turn.completed", "usage": {}}]))
        self.assertTrue(parsed["problems"])
        self.assertIsNone(parsed["provider_usage"])

    def test_known_pre_turn_cli_diagnostics_are_not_tool_invocations(self):
        parsed = parse_events(self.events([
            {"type": "item.completed", "item": {"type": "error", "message":
                "Code Mode is unavailable because code-mode host is disabled. Code mode will fail closed."}},
            {"type": "turn.started"},
        ]))
        self.assertEqual(parsed["tool_events"], [])
        self.assertEqual(len(parsed["startup_diagnostics"]), 1)
        late = parse_events(self.events([
            {"type": "turn.started"},
            {"type": "item.completed", "item": {"type": "error", "message":
                "Code Mode is unavailable because code-mode host is disabled."}},
        ]))
        self.assertEqual(len(late["tool_events"]), 1)

    def test_invocation_preserves_model_and_isolates_config(self):
        command = command_for("codex", {"model": "configured-model", "model_config": {"reasoning_effort": "ultra"}},
                              Path("empty"), Path("schema.json"), Path("final.json"))
        self.assertEqual(command[command.index("--model") + 1], "configured-model")
        self.assertIn("--ignore-user-config", command)
        self.assertIn("--ephemeral", command)
        self.assertIn('web_search="disabled"', command)
        self.assertIn("project_doc_max_bytes=0", command)
        self.assertEqual(command.count("--disable"), len(DISABLED_FEATURES))
        self.assertIn("skip_host_skill_discovery", command)
        self.assertEqual(command[-1], "-")


if __name__ == "__main__":
    unittest.main()
