#!/usr/bin/env bash
# Usage: scripts/check_file.sh EvalSound
# Builds the single module Start.<name> and reports only the style/flexible/
# multiGoal linter warnings (and errors) that originate in Start/<name>.lean.
set -uo pipefail
mod="$1"
lake build "Start.$mod" 2>&1 \
  | grep -E "^(warning|error): Start/$mod\.lean|^error" \
  | grep -v "aesop:" \
  | grep -v "manifest"
