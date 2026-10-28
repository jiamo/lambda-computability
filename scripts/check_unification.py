#!/usr/bin/env python3
"""The unification gate for the `Start` library (milestone M31).

The library is *unified* when its import graph is connected: every module is linked to every
other one through imports, the aggregators excepted.  The aggregators are the root `Start.lean`,
`Start/Capstones.lean` (the list of end results) and the consumer `Start/Demo.lean`.  They import
everything, so they would connect any two modules; they are left out.

A link between two parts of the library is meant to be a *bridge theorem*.  Such a theorem
relates the basic notions of both parts, and it is registered in `Start/Capstones.lean` and on
the task board (rows `M31-*`).  This script checks only the connectivity that bridges create; it
does not check what a bridge proves.

Usage:  python3 scripts/check_unification.py [--strict] [--list]

Without `--strict`, report the components and exit 0.  With `--strict`, exit 1 when there is
more than one component.  With `--list`, print the modules of every component except the
largest.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.join(ROOT, "Start")
AGGREGATORS = {"Capstones", "Demo"}

IMPORT_RE = re.compile(r"^import\s+Start\.([A-Za-z0-9_.]+)", re.M)


def modules() -> dict[str, list[str]]:
    mods: dict[str, list[str]] = {}
    for f in sorted(os.listdir(LIB)):
        if not f.endswith(".lean"):
            continue
        name = f[:-5]
        with open(os.path.join(LIB, f), encoding="utf-8") as fh:
            mods[name] = IMPORT_RE.findall(fh.read())
    return mods


def components(mods: dict[str, list[str]]) -> list[list[str]]:
    adj: dict[str, set[str]] = {n: set() for n in mods if n not in AGGREGATORS}
    for n, imps in mods.items():
        if n in AGGREGATORS:
            continue
        for i in imps:
            if i in adj:
                adj[n].add(i)
                adj[i].add(n)
    seen: set[str] = set()
    comps: list[list[str]] = []
    for n in sorted(adj):
        if n in seen:
            continue
        stack, comp = [n], []
        seen.add(n)
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        comps.append(sorted(comp))
    comps.sort(key=len, reverse=True)
    return comps


def stem(name: str) -> str:
    m = re.match(r"[A-Z]+[a-z0-9]*", name)
    return m.group(0) if m else name


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    comps = components(modules())
    total = sum(len(c) for c in comps)
    print(f"{len(comps)} component(s) over {total} modules; largest {len(comps[0])}")
    for c in comps[1:]:
        stems = Counter(stem(n) for n in c).most_common(4)
        print(f"  island of {len(c)}: " + ", ".join(f"{s}×{k}" for s, k in stems))
        if args.list:
            print("    " + " ".join(c))
    if args.strict and len(comps) > 1:
        print("FAIL: the import graph is not connected (see M31 on the task board)")
        return 1
    if len(comps) == 1:
        print("OK: the import graph is connected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
