import contextlib
import io
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from unittest.mock import patch

from check_lean_vacuity import PROJECT, affected, report, scan_modules


MODULE = Path("Example.lean")
RESULT = {"scanned": 2, "findings": [{"name": "one", "line": 2}], "incomplete": ["two: heartbeat limit"]}


def record(data, kind="VacuityAudit.result", line=10, severity="information"):
    return {"data": data, "kind": kind, "severity": severity, "fileName": str(MODULE),
            "pos": {"line": line, "column": 0}}


def read(*records, status=0):
    stdout = "\n".join(["ordinary output on stdout", "null", *(json.dumps(r) for r in records)])
    return report(subprocess.CompletedProcess(["lean"], status, stdout, ""), MODULE, 10)


class VacuityTests(unittest.TestCase):
    def test_change_to_shared_predicate_reaches_transitive_proofs(self):
        proof = "VerifiedGarbage.Proof."
        graph = {"Spec": [], "Common": ["Spec"], proof + "A": ["Common"],
                 proof + "B": [proof + "A"], proof + "C": []}
        self.assertEqual(list(affected(graph, {"Spec"})), [proof + "A", proof + "B"])

    def test_uses_only_appended_commands_result(self):
        self.assertEqual(read(record("vacuity finding innocent", kind="[anonymous]"),
                              record("another command", line=3),
                              record("other module") | {"fileName": "Other.lean"}, record(json.dumps(RESULT))), RESULT)

    def test_requires_one_complete_result(self):
        valid = record(json.dumps(RESULT))
        for rows in [[], [valid, valid], [record('{"scanned":0}')]]:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                read(*rows)

    def test_elaboration_failure_invalidates_result(self):
        with self.assertRaisesRegex(ValueError, "failed proof"):
            read(record("failed proof", severity="error"), record(json.dumps(RESULT)), status=1)

    def test_summary_distinguishes_private_helpers_and_a_timeout(self):
        paths = [PROJECT / f"{m}.lean" for m in "ABC"]
        found = {"scanned": 1, "findings": [{"name": "impossible", "line": 8}], "incomplete": []}
        timeout = subprocess.TimeoutExpired("lean", 60)
        with tempfile.TemporaryDirectory() as directory:
            summary = Path(directory) / "summary"
            with (patch.dict(os.environ, GITHUB_STEP_SUMMARY=str(summary)),
                  patch("check_lean_vacuity.scan", side_effect=[found, found, timeout]),
                  contextlib.redirect_stdout(io.StringIO())):
                scan_modules(paths, Path(directory), {})
            text = summary.read_text()
        self.assertIn("lean/A.lean:8 impossible", text)
        self.assertIn("lean/B.lean:8 impossible", text)
        self.assertIn("1 of 3 selected modules incomplete", text)
