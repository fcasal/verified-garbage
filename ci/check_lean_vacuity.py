"""List affected proof modules, nearest edits first. Read NUL-delimited paths relative to lean/."""

import os
import sys
from collections import defaultdict, deque

import lean_shards


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


if __name__ == "__main__":
    paths = set(os.fsdecode(sys.stdin.buffer.read()).split("\0"))
    mods = lean_shards.modules()
    changed = {name for name, path in mods.items() if str(path.relative_to(lean_shards.LEAN)) in paths}
    if changed:
        for name in affected(lean_shards.imports(mods), changed):
            sys.stdout.buffer.write(os.fsencode(name) + b"\0")
