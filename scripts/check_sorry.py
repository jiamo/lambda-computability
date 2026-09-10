#!/usr/bin/env python3
"""Refuse `sorry` and `admit` in the shipped library, ignoring comments and strings.

A plain `grep` for the words is not usable as a gate here: the documentation of this
repository *talks* about `sorry` (for instance "all fully proved, no sorry"), and several
module headers use the English word "admit".  This script removes comments and string
literals first, so it only sees the tokens that Lean would elaborate.

Usage:  python3 scripts/check_sorry.py [repository root]
Exit status 0 when the library is clean, 1 when a `sorry`/`admit` survives, with the
offending file and line on stderr.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

TOKENS = ("sorry", "sorryAx", "admit")

TOKEN_RE = re.compile(r"\b(" + "|".join(TOKENS) + r")\b")


def strip_comments(text: str) -> str:
    """Blank out Lean comments and string literals, keeping the line structure.

    Block comments nest in Lean, so the scan keeps a depth counter; line comments run to
    the end of the line; string literals are removed because a `sorry` inside one is not a
    proof either.  Everything removed is replaced by spaces so that line and column
    numbers of what remains are unchanged.
    """
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == '"':
            out.append(" ")
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                    continue
                if text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def main() -> None:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    targets = [root / "Start.lean"]
    targets.extend(sorted((root / "Start").rglob("*.lean")))

    failures: list[str] = []
    for path in targets:
        if not path.is_file():
            print(f"check_sorry: missing {path}", file=sys.stderr)
            raise SystemExit(1)
        stripped = strip_comments(path.read_text())
        for lineno, line in enumerate(stripped.splitlines(), start=1):
            match = TOKEN_RE.search(line)
            if match:
                failures.append(
                    f"{path.relative_to(root)}:{lineno}: `{match.group(1)}` in the library"
                )

    if failures:
        for failure in failures:
            print(f"check_sorry: {failure}", file=sys.stderr)
        raise SystemExit(1)

    print(f"OK: no sorry/admit in {len(targets)} modules")


if __name__ == "__main__":
    main()
