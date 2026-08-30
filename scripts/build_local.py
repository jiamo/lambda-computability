#!/usr/bin/env python3
"""Dependency-ordered builder for the `Start` library.

This bypasses `lake` and calls `lean` directly with an explicit `LEAN_PATH`.
It is a convenience for environments where the pre-built dependency tree and
`lake`'s trace database disagree; `lake build` remains the normal entry point.

Usage:  python3 scripts/build_local.py [Module.Name ...]
With no arguments, every module of the `Start` library is built.
"""
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PKGS = os.path.join(ROOT, ".lake/packages")
LEAN_PATH = ":".join(
    [f"{PKGS}/{pkg}/.lake/build/lib/lean"
     for pkg in ("Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph",
                 "LeanSearchClient", "plausible", "mathlib", "cslib")]
    + [os.path.join(ROOT, ".lake/build/lib/lean")]
)
# `lean` from `PATH`; `elan` selects the toolchain named in `lean-toolchain`.
LEAN = os.environ.get("LEAN_BIN", "lean")
BUILD = os.path.join(ROOT, ".lake/build/lib/lean")

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][\w.]*)", re.M)


def modules():
    out = {}
    for dirpath, _, files in os.walk(os.path.join(ROOT, "Start")):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                rel = os.path.relpath(p, ROOT)[:-5]
                out[rel.replace("/", ".")] = p
    return out


def deps(path, known):
    src = open(path).read()
    return [m for m in IMPORT_RE.findall(src) if m in known]


def olean(mod):
    return os.path.join(BUILD, mod.replace(".", "/") + ".olean")


def up_to_date(mod, path, dep_list):
    o = olean(mod)
    if not os.path.exists(o):
        return False
    t = os.path.getmtime(o)
    if os.path.getmtime(path) > t:
        return False
    for d in dep_list:
        od = olean(d)
        if not os.path.exists(od) or os.path.getmtime(od) > t:
            return False
    return True


def compile_one(mod, path):
    o = olean(mod)
    os.makedirs(os.path.dirname(o), exist_ok=True)
    env = dict(os.environ, LEAN_PATH=LEAN_PATH)
    tmp = o + ".tmp"
    r = subprocess.run([LEAN, path, "-o", tmp, "-i", o[:-6] + ".ilean"],
                       capture_output=True, text=True, cwd=ROOT, env=env)
    if r.returncode == 0:
        os.replace(tmp, o)
    else:
        if os.path.exists(tmp):
            os.remove(tmp)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def main():
    mods = modules()
    graph = {m: deps(p, mods) for m, p in mods.items()}
    targets = sys.argv[1:] or list(mods)
    # transitive closure of targets
    want, stack = set(), list(targets)
    while stack:
        m = stack.pop()
        if m in want or m not in mods:
            continue
        want.add(m)
        stack.extend(graph[m])
    done, failed = set(), {}
    pending = set(want)
    pool = ThreadPoolExecutor(max_workers=int(os.environ.get("JOBS", "6")))
    while pending:
        ready = [m for m in pending
                 if all(d in done for d in graph[m]) or
                 all(d not in pending and d not in failed for d in graph[m])]
        ready = [m for m in pending if all(d in done for d in graph[m])]
        if not ready:
            for m in pending:
                failed.setdefault(m, "skipped (dependency failed)")
            break
        skipped = [m for m in ready if up_to_date(m, mods[m], graph[m])]
        for m in skipped:
            done.add(m)
            pending.discard(m)
        ready = [m for m in ready if m not in skipped]
        if not ready:
            continue
        results = list(pool.map(lambda m: (m,) + compile_one(m, mods[m]), ready))
        for m, rc, log in results:
            pending.discard(m)
            if rc == 0:
                done.add(m)
                print(f"OK   {m}", flush=True)
                if log.strip():
                    print(log.strip()[:2000], flush=True)
            else:
                failed[m] = log
                print(f"FAIL {m}\n{log[:3000]}", flush=True)
    print(f"\nbuilt {len(done)}  failed {len(failed)}")
    for m in sorted(failed):
        print("  FAILED:", m)
    return 1 if failed else 0


if __name__ == "__main__":
    t0 = time.time()
    rc = main()
    print(f"elapsed {time.time() - t0:.0f}s")
    sys.exit(rc)
