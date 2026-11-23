"""Report arithmetic contradictions in changed Lean proofs and their transitive importers.

From lean/, after the normal proof build: lake env python3 ../ci/check_lean_vacuity.py HEAD^1
"""

import argparse
import html
import json
import os
from collections import defaultdict, deque
from pathlib import Path
import re
import subprocess
import tempfile
import time

import lean_shards

PROJECT = lean_shards.LEAN
AUDIT = Path(__file__).resolve().parent / "vacuity"


def affected(graph, changed):
    """Visit edited modules first, then importers in order of distance."""
    importers = defaultdict(list)
    for name, deps in graph.items():
        for dep in deps:
            importers[dep].append(name)
    queue = deque(sorted(changed))
    seen = set(changed)
    while queue:
        name = queue.popleft()
        if name.startswith("VerifiedGarbage.Proof."):
            yield name
        for importer in importers[name]:
            if importer not in seen:
                queue.append(importer)
                seen.add(importer)


def run(args, **kwargs):
    return subprocess.run(args, text=True, cwd=PROJECT, capture_output=True, **kwargs)


def report(proc, path, line):
    # A module can also print ordinary text to stdout with IO.println.
    records = []
    for row in proc.stdout.splitlines():
        try:
            record = json.loads(row)
        except ValueError:
            continue
        if isinstance(record, dict):
            records.append(record)
    errors = [str(r.get("data", "")) for r in records if r.get("severity") == "error"]
    if proc.returncode or errors:
        raise ValueError("\n".join(errors) or proc.stderr[-2000:] or f"Lean exited with {proc.returncode}")
    results = [r.get("data") for r in records if r.get("kind") == "VacuityAudit.result"
               and r.get("fileName") == str(path) and r.get("pos") == {"line": line, "column": 0}]
    if len(results) != 1:
        raise ValueError(f"expected one audit result, got {len(results)}")
    if not isinstance(results[0], str):
        raise ValueError("invalid audit diagnostic")
    result = json.loads(results[0])
    if not isinstance(result, dict) or type(result.get("scanned")) is not int:
        raise ValueError("invalid theorem count")
    findings, incomplete = result.get("findings"), result.get("incomplete")
    if not isinstance(findings, list) or not all(
        isinstance(f, dict) and isinstance(f.get("name"), str) and type(f.get("line")) is int and f["line"] > 0
        for f in findings
    ):
        raise ValueError("invalid finding")
    if not isinstance(incomplete, list) or not all(isinstance(m, str) for m in incomplete):
        raise ValueError("invalid incomplete result")
    if result["scanned"] < len(findings) + len(incomplete):
        raise ValueError("invalid theorem count")
    return result


def audit(path, env, deadline, args=()):
    source, count = re.subn(r"^module[ \t]*$", "module meta import VacuityAudit",
                            path.read_text(), count=1, flags=re.MULTILINE)
    if count != 1:
        raise ValueError("missing module header")
    line = source.count("\n") + 2
    proc = run(["lean", "-j2", "--json", *args, "--stdin", str(path)],
               env=env, input=source + "\n#auditVacuity\n", timeout=max(0, deadline - time.monotonic()))
    return report(proc, path, line)


def scan(path, temp, env, deadline):
    # Use the same plugins and import artifacts as the normal build. A cache
    # restore may omit the setup file; Lake can regenerate it from the source.
    relative = path.relative_to(PROJECT)
    setup = PROJECT / ".lake/build/ir" / relative.with_suffix(".setup.json")
    if not setup.is_file():
        config = run(["lake", "setup-file", str(relative)], timeout=max(0, deadline - time.monotonic()))
        if config.returncode:
            raise ValueError(config.stderr[-2000:] or "lake setup-file failed")
        setup = temp / "setup.json"
        setup.write_text(config.stdout)
    return audit(path, env, deadline, ("--setup", str(setup)))


def scan_modules(paths, temp, env):
    print(f"Selected {len(paths)} proof modules.", flush=True)
    scanned = 0
    incomplete = 0
    findings = []
    deadline = time.monotonic() + 300
    for i, path in enumerate(paths):
        now = time.monotonic()
        if now >= deadline:
            print(f"vacuity incomplete: scan budget exhausted; {len(paths) - i} modules unscanned")
            incomplete += len(paths) - i
            break
        try:
            result = scan(path, temp, env, min(deadline, now + 60))
            scanned += result["scanned"]
            for f in result["findings"]:
                findings.append(f"{path.relative_to(PROJECT.parent)}:{f['line']} {f['name']}")
            incomplete += bool(result["incomplete"])
            for reason in result["incomplete"]:
                print(f"{path}: incomplete: {reason}", flush=True)
        except (ValueError, subprocess.TimeoutExpired) as error:
            print(f"{path}: vacuity incomplete: {error}", flush=True)
            incomplete += 1
    summary = (f"Reviewed {scanned} theorem(s). Found {len(findings)} with contradictory hypotheses. "
               f"{incomplete} of {len(paths)} selected modules incomplete.")
    print(summary)
    for name in findings:
        print(name)
    if filename := os.getenv("GITHUB_STEP_SUMMARY"):
        with open(filename, "a") as output:
            print("### Proof hypothesis audit", summary, sep="\n\n", file=output)
            for name in findings:
                print(f"- <code>{html.escape(name)}</code>", file=output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="base commit for the diff against HEAD")
    options = parser.parse_args()
    diff = run(["git", "diff", "--relative", "--name-only", "--no-renames", "-z", options.base, "HEAD", "--", "."])
    diff.check_returncode()
    changed_paths = set(diff.stdout.split("\0"))
    with tempfile.TemporaryDirectory() as directory:
        temp = Path(directory)
        env = {**os.environ, "LEAN_PATH": os.pathsep.join([directory, os.environ.get("LEAN_PATH", "")])}
        build = run(["lean", "-R", str(AUDIT), "-o", str(temp / "VacuityAudit.olean"), str(AUDIT / "VacuityAudit.lean")])
        if build.returncode:
            raise SystemExit(build.stdout + build.stderr)
        fixture_path = AUDIT / "Fixture.lean"
        fixture = audit(fixture_path, env, time.monotonic() + 30)
        expected_line = next(i for i, line in enumerate(fixture_path.read_text().splitlines(), 1)
                             if line.startswith("private theorem impossible "))
        expected = {"name": "VacuityFixture.impossible", "line": expected_line}
        if fixture != {"scanned": 2, "findings": [expected], "incomplete": []}:
            raise SystemExit(f"unexpected fixture results: {fixture}")
        mods = lean_shards.modules()
        changed = {m for m, p in mods.items() if str(p.relative_to(PROJECT)) in changed_paths}
        if not changed:
            print("No changed Lean library modules.")
            return 0
        names = list(affected(lean_shards.imports(mods), changed))
        scan_modules([mods[name] for name in names], temp, env)
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
