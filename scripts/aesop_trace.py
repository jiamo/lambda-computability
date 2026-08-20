#!/usr/bin/env python3
"""Print the goal states around every non-terminal `aesop` call of a Lean file.

For each site reported by the compiler as `aesop: failed to prove the goal`,
a scratch copy of the file is created in which that single call is wrapped as
`(trace_state; aesop; trace_state)`, and the file is elaborated.  The trace
output shows exactly which goals the automation consumed and which ones it
left behind, which is what one needs in order to replace it by an explicit
proof.

Usage:  python3 scripts/aesop_trace.py Start/Computability.lean [line ...]
"""

from __future__ import annotations

import subprocess
import sys

from aesop_fix import aesop_sites, replace_at, run  # type: ignore


def main() -> int:
    path = sys.argv[1]
    only = {int(a) for a in sys.argv[2:]}
    msgs = run(path)
    sites = aesop_sites(msgs)
    if only:
        sites = [s for s in sites if s[0] in only]
    text = open(path).read()
    for line, col in sites:
        trial = replace_at(text, line, col, "(trace_state; aesop; trace_state)")
        if trial is None:
            print(f"=== {line}:{col}: token not found", flush=True)
            continue
        scratch = "/tmp/aesop_trace_scratch.lean"
        open(scratch, "w").write(trial)
        out = subprocess.run(["lake", "env", "lean", scratch], capture_output=True, text=True)
        print(f"=== SITE {line}:{col} " + "=" * 40, flush=True)
        print(out.stdout, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
