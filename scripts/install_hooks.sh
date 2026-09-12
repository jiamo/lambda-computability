#!/usr/bin/env bash
# Point this clone's hooks at `.githooks/`, so that `.githooks/pre-commit` runs the
# packaging gate (`scripts/pack_gate.sh`) on every commit.
#
# Hooks are not carried by a clone, so this has to be run once per working copy.

set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "${root}"
chmod +x .githooks/* scripts/*.sh
git config core.hooksPath .githooks
echo "install_hooks: core.hooksPath = $(git config core.hooksPath)"
