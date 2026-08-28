#!/usr/bin/env python3
"""Two mechanical gates for the `Start` library.

Gate 1 (import closure).  Every module `Start/X.lean` must be reachable from the root
`Start.lean` by imports, unless it is a *consumer* module that imports `Start` itself
(`Start/Demo.lean` is one: it may not be in the closure, or the imports would be circular).

Gate 2 (registration).  Every module must either be *used* — some declaration it introduces is
mentioned in another module — or be *registered* in `Start/Capstones.lean`, the compiled list of
end results.  A module that is neither used nor registered is a dead end.

Usage:  python3 scripts/check_closure.py [--list-terminal]

Exit code 0 iff both gates pass.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.join(ROOT, "Start")
ROOT_MODULE = os.path.join(ROOT, "Start.lean")
CAPSTONES = os.path.join(LIB, "Capstones.lean")

IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'?!.]*)",
    re.M,
)


def module_of(path: str) -> str:
    rel = os.path.relpath(path, ROOT)
    return rel[:-5].replace(os.sep, ".")


def path_of(module: str) -> str:
    return os.path.join(ROOT, module.replace(".", os.sep) + ".lean")


def imports_of(path: str) -> list[str]:
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as f:
        return IMPORT_RE.findall(f.read())


def closure(start: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(start)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(imports_of(path_of(m)))
    return seen


def declarations(path: str) -> set[str]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    names = set()
    for name in DECL_RE.findall(text):
        short = name.split(".")[-1]
        if len(short) > 2:
            names.add(short)
    return names


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list-terminal", action="store_true",
                        help="list the modules no other module refers to")
    args = parser.parse_args()

    files = sorted(
        os.path.join(LIB, f) for f in os.listdir(LIB) if f.endswith(".lean")
    )
    modules = {module_of(p): p for p in files}

    failures: list[str] = []

    # ---- Gate 1: import closure -------------------------------------------------
    reachable = closure(imports_of(ROOT_MODULE))
    for module, path in sorted(modules.items()):
        if module in reachable:
            continue
        if "Start" in imports_of(path):
            continue  # a consumer of the whole library, e.g. `Start/Demo.lean`
        failures.append(f"[closure] {module} is not imported by Start.lean")

    # ---- Gate 2: registration ---------------------------------------------------
    texts = {}
    for module, path in modules.items():
        with open(path, encoding="utf-8") as f:
            texts[module] = f.read()
    capstones = texts.get("Start.Capstones", "")

    terminal = []
    for module, path in sorted(modules.items()):
        names = declarations(path)
        if not names:
            continue
        used = any(
            any(re.search(r"\b" + re.escape(n) + r"\b", other_text) for n in names)
            for other, other_text in texts.items()
            if other != module
        )
        if used:
            continue
        terminal.append(module)
        if module == "Start.Capstones":
            continue
        if not re.search(r"\b" + re.escape(module.split(".")[-1]) + r"\b", capstones) and not any(
            re.search(r"\b" + re.escape(n) + r"\b", capstones) for n in names
        ):
            failures.append(
                f"[registration] {module} is neither used elsewhere nor #check-ed in "
                f"Start/Capstones.lean"
            )

    if args.list_terminal:
        print("terminal modules (no external references):")
        for module in terminal:
            print("  " + module)

    if failures:
        print("\n".join(failures))
        print(f"\n{len(failures)} problem(s).")
        return 1
    print(f"OK: {len(modules)} modules, all in the import closure and all registered.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
