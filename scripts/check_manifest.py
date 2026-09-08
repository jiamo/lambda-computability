#!/usr/bin/env python3
"""Check that the checked-in dependency manifest agrees with the build configuration.

The manifest (`lake-manifest.json`) is part of what the repository ships: a clone that
carries a manifest disagreeing with `lakefile.toml` cannot be built at all, even if the
tree it was produced from could be.  This script is a fast, offline gate that catches
exactly that failure, without downloading anything:

* every dependency required by `lakefile.toml` appears in the manifest;
* for each of them the manifest's `inputRev` is the revision `lakefile.toml` asks for;
* no manifest entry is missing a resolved `rev`;
* the manifest names the package that `lakefile.toml` declares;
* `lean-toolchain` is a well-formed pin.

Usage:  python3 scripts/check_manifest.py [repository root]
Exit status 0 on success, 1 on the first failure, with a diagnosis on stderr.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


def parse_lakefile(text: str) -> tuple[str, list[tuple[str, str | None]]]:
    """Return the package name and the list of `(name, rev)` of the `[[require]]` blocks.

    The lakefile of this project uses a small, regular subset of TOML, so a line-based
    reader is enough and keeps the gate dependency-free.
    """
    package_name = ""
    requires: list[tuple[str, str | None]] = []
    in_require = False
    current: dict[str, str] = {}

    def flush() -> None:
        if current.get("name"):
            requires.append((current["name"], current.get("rev")))
        current.clear()

    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[["):
            if in_require:
                flush()
            in_require = line == "[[require]]"
            continue
        if line.startswith("["):
            if in_require:
                flush()
            in_require = False
            continue
        match = re.match(r'^(\w+)\s*=\s*"([^"]*)"', line)
        if not match:
            continue
        key, value = match.group(1), match.group(2)
        if in_require:
            current[key] = value
        elif key == "name" and not package_name:
            package_name = value
    if in_require:
        flush()
    return package_name, requires


def fail(message: str) -> None:
    print(f"check_manifest: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    lakefile = root / "lakefile.toml"
    manifest_path = root / "lake-manifest.json"
    toolchain_path = root / "lean-toolchain"

    for path in (lakefile, manifest_path, toolchain_path):
        if not path.is_file():
            fail(f"missing {path.relative_to(root)}")

    toolchain = toolchain_path.read_text().strip()
    if not re.fullmatch(r"leanprover/lean4:\S+", toolchain):
        fail(f"lean-toolchain is not a Lean pin: {toolchain!r}")

    package_name, requires = parse_lakefile(lakefile.read_text())
    if not requires:
        fail("no [[require]] block found in lakefile.toml")

    try:
        manifest = json.loads(manifest_path.read_text())
    except json.JSONDecodeError as error:  # pragma: no cover - malformed file
        fail(f"lake-manifest.json is not valid JSON: {error}")

    packages = {entry["name"]: entry for entry in manifest.get("packages", [])}

    if package_name and manifest.get("name") not in (package_name, package_name.lower()):
        fail(
            f"lake-manifest.json is for package {manifest.get('name')!r}, "
            f"but lakefile.toml declares {package_name!r}"
        )

    for name, rev in requires:
        entry = packages.get(name)
        if entry is None:
            fail(
                f"dependency {name!r} is required by lakefile.toml but absent from "
                f"lake-manifest.json (lake would refuse to build: "
                f"\"dependency '{name}' not in manifest\")"
            )
        if rev is not None and entry.get("inputRev") != rev:
            fail(
                f"dependency {name!r} is pinned at {rev!r} in lakefile.toml but the "
                f"manifest records inputRev {entry.get('inputRev')!r}"
            )

    for name, entry in packages.items():
        if not entry.get("rev"):
            fail(f"manifest entry {name!r} has no resolved revision")

    print(
        f"OK: lake-manifest.json agrees with lakefile.toml "
        f"({len(packages)} packages, {len(requires)} direct dependencies, {toolchain})"
    )


if __name__ == "__main__":
    main()
