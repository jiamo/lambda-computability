#!/usr/bin/env python3
"""Summarize Lean linter warnings from a `lake build` log.

Usage: python3 scripts/lint_report.py BUILD_LOG [FILE_FILTER]

Prints one line per linter warning (`file:line:col class`) followed by per-file
and per-class totals.  Only warnings that name a linter option are reported.
"""

from __future__ import annotations

import re
import sys
from collections import Counter

WARN = re.compile(r"^warning: (Start/[^:]+):(\d+):(\d+): (.*)$")
NOTE = re.compile(r"set_option (linter\.[\w.]+) false")


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    path = sys.argv[1]
    filt = sys.argv[2] if len(sys.argv) > 2 else ""
    lines = open(path, encoding="utf-8").read().splitlines()
    entries = []
    pending = None
    for line in lines:
        m = WARN.match(line)
        if m:
            pending = m
            continue
        n = NOTE.search(line)
        if n and pending is not None:
            entries.append((pending.group(1), int(pending.group(2)),
                            int(pending.group(3)), n.group(1)))
            pending = None
    seen = set()
    per_file: Counter[str] = Counter()
    per_class: Counter[str] = Counter()
    for f, line, col, cls in entries:
        key = (f, line, col, cls)
        if key in seen:
            continue
        seen.add(key)
        per_file[f] += 1
        per_class[cls] += 1
        if filt and filt not in f:
            continue
        print(f"{f}:{line}:{col} {cls}")
    print("--- per file")
    for f, n in per_file.most_common():
        print(f"{n:5d} {f}")
    print("--- per class")
    for c, n in per_class.most_common():
        print(f"{n:5d} {c}")
    print(f"--- total {sum(per_class.values())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
