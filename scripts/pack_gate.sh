#!/usr/bin/env bash
# Run the release gates on what `git archive` actually ships, not on the working tree.
#
# The failure this catches is the one a warm working tree hides: a `lake-manifest.json`
# that disagrees with `lakefile.toml` (a missing dependency, a stale `inputRev`, the wrong
# package name) breaks a fresh clone while the tree it was produced from still builds,
# because `lake` never has to re-resolve anything locally.  The `build-from-archive` job of
# `.github/workflows/lean_action_ci.yml` runs the same gates, but it only reports after a
# push: this script is the packaging step's own gate, to be run *before* delivering.
#
# Usage:  scripts/pack_gate.sh [revision]     (default: HEAD)
# Exit status 0 when the packed tree passes every gate.

set -euo pipefail

revision="${1:-HEAD}"
root="$(git rev-parse --show-toplevel)"
tmp="$(mktemp -d)"
trap 'rm -rf "${tmp}"' EXIT

cd "${root}"

echo "pack_gate: packing ${revision}"
git archive --format=tar "${revision}" > "${tmp}/delivered.tar"
mkdir -p "${tmp}/delivered"
tar -x -f "${tmp}/delivered.tar" -C "${tmp}/delivered"

cd "${tmp}/delivered"

echo "pack_gate: manifest"
python3 scripts/check_manifest.py

echo "pack_gate: sorry/admit"
python3 scripts/check_sorry.py

echo "pack_gate: task board"
python3 scripts/goal_state.py validate

echo "pack_gate: closure"
python3 scripts/check_closure.py

echo "pack_gate: OK — the packed tree passes every offline gate."
echo "pack_gate: note that building the packed tree is done by the CI job"
echo "pack_gate: 'build-from-archive' in .github/workflows/lean_action_ci.yml."
