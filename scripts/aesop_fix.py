#!/usr/bin/env python3
"""Helper used while removing non-terminal `aesop` calls.

For a given Lean file, locate every `aesop`/`bound_nt` invocation that the
compiler reports as non-terminal (i.e. that emits
`aesop: failed to prove the goal ...`) and try to replace it by a tactic that
performs the same normalisation but is not a non-terminal automation call.

A candidate replacement is accepted only if, after the edit, the file still
elaborates without errors and the only change in the message set is that the
warning for this site has disappeared.

Usage:  python3 scripts/aesop_fix.py Start/Computability.lean [candidates...]
"""

from __future__ import annotations

import re
import subprocess
import sys

CANDIDATES = [
    "simp_all",
    "dsimp only",
    "simp only [] at *",
    "constructor",
    "intros",
    "grind",
    "tauto",
]

MSG = re.compile(
    r"^(?P<file>\S+\.lean):(?P<line>\d+):(?P<col>\d+): "
    r"(?P<sev>warning|error)(?:\([^)]*\))?: (?P<msg>.*)$"
)


def run(path: str) -> list[tuple[int, int, str, str]]:
    out = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    msgs = []
    base = path.split("/")[-1]
    for line in (out.stdout + out.stderr).splitlines():
        m = MSG.match(line)
        if m and m.group("file").endswith(base):
            msgs.append((int(m.group("line")), int(m.group("col")), m.group("sev"), m.group("msg")))
    return msgs


def aesop_sites(msgs) -> list[tuple[int, int]]:
    seen: list[tuple[int, int]] = []
    for line, col, _sev, msg in msgs:
        if msg.startswith("aesop: failed") and (line, col) not in seen:
            seen.append((line, col))
    return seen


def replace_at(text: str, line: int, col: int, new: str) -> str | None:
    lines = text.split("\n")
    src = lines[line - 1]
    for tok in ("aesop", "bound_nt"):
        if src[col:col + len(tok)] == tok:
            lines[line - 1] = src[:col] + new + src[col + len(tok):]
            return "\n".join(lines)
    return None


def main() -> int:
    path = sys.argv[1]
    cands = sys.argv[2:] or CANDIDATES
    baseline = run(path)
    if any(sev == "error" for _l, _c, sev, _m in baseline):
        print("file already has errors; aborting", flush=True)
        return 1
    sites = sorted(aesop_sites(baseline), key=lambda lc: (-lc[0], -lc[1]))
    print(f"{len(sites)} non-terminal sites in {path}", flush=True)
    fixed = 0
    for line, col in sites:
        current = open(path).read()
        expected = [m for m in baseline if not (m[0] == line and m[1] == col)]
        done = False
        for cand in cands:
            trial = replace_at(current, line, col, cand)
            if trial is None:
                print(f"  {line}:{col}: token not found", flush=True)
                break
            open(path, "w").write(trial)
            new_msgs = run(path)
            if new_msgs == expected:
                print(f"  {line}:{col}: fixed with `{cand}`", flush=True)
                fixed += 1
                baseline = expected
                done = True
                break
            open(path, "w").write(current)
        if not done:
            print(f"  {line}:{col}: NO CANDIDATE WORKED", flush=True)
    print(f"fixed {fixed} of {len(sites)} sites", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
