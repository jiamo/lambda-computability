# Releasing, and repository metadata

This file records how releases of this repository are meant to work, and the one-off
clean-up steps that have to be done through the GitHub web interface or the `gh` CLI
(they cannot be done from inside the repository).

## Why the `v4.33.0` release exists, and why it is wrong

The repository used to contain `.github/workflows/create-release.yml`, taken from the
Lean community CI template:

```yaml
on:
  push:
    paths:
      - 'lean-toolchain'
```

It runs `leanprover-community/lean-release-tag`, which creates a GitHub release named
after the **Lean toolchain** version every time `lean-toolchain` changes.  That is
appropriate for an *application* that users download per toolchain, not for a library:
it produced a release tagged `v4.33.0` with the body "Automated release for Lean version
v4.33.0", which is a Lean version, not a version of this library.

**The workflow has been deleted.**  `update.yml` (automatic dependency-bump PRs) and
`lean_action_ci.yml` (CI build) are kept — those are useful.

## One-off clean-up (needs GitHub access)

```bash
# 1. delete the toolchain-named release and its tag
gh release delete v4.33.0 --cleanup-tag --yes

# 2. create the first real library release
gh release create v0.1.0 \
  --title "v0.1.0" \
  --notes-file docs/release-notes/v0.1.0.md

# 3. repository metadata (currently empty)
gh repo edit \
  --description "Computability theory and algorithmic information theory, formalized in Lean 4 (sorry-free)" \
  --add-topic lean4 \
  --add-topic mathlib \
  --add-topic lambda-calculus \
  --add-topic computability \
  --add-topic kolmogorov-complexity \
  --add-topic algorithmic-information-theory \
  --add-topic church-turing-thesis
```

The same three things can be done from the web interface: *Releases → v4.33.0 → Delete*,
then *Tags → v4.33.0 → Delete*; *Releases → Draft a new release* with tag `v0.1.0`; and
the *About* gear on the repository front page for description and topics.

## Packaging: run the gates on the archive, before delivering

The tree that is delivered is the one `git archive` produces, and it is *not* the working
tree: the working tree carries `.lake/`, so `lake` never has to re-resolve dependencies
there and a `lake-manifest.json` that disagrees with `lakefile.toml` stays invisible in it
while breaking every fresh clone.  That is exactly the failure that shipped four times.

The packaging step therefore has its own gate, to be run **after** `git archive` and
**before** the archive is handed over:

```bash
scripts/pack_gate.sh          # or: scripts/pack_gate.sh <revision>
```

It packs the given revision (default `HEAD`), unpacks it into a scratch directory, and
runs, *inside the unpacked copy*:

* `scripts/check_manifest.py` — the shipped manifest agrees with the shipped
  `lakefile.toml`: every `[[require]]` is present, its `inputRev` is the pinned revision,
  every entry has a resolved `rev`, and the manifest names the package that the lakefile
  declares;
* `scripts/check_sorry.py` — no `sorry`/`admit` in `Start.lean` or `Start/`, comments and
  string literals excluded (a plain `grep` fails on the documentation, which discusses
  `sorry` in prose);
* `scripts/goal_state.py validate` and `scripts/check_closure.py` — the task board is
  well formed and every module is in the import closure.

### The gate now has a caller

Shipping the gate is not the same as running it, and the gate was shipped, documented and
not called: the fifth delivery again carried a manifest naming the wrong package, pinning
the wrong Mathlib revision and omitting `cslib`.  So the call is now automatic:

```bash
scripts/install_hooks.sh       # once per clone: git config core.hooksPath .githooks
```

`.githooks/pre-commit` runs `scripts/pack_gate.sh "$(git write-tree)"`, i.e. the gate on
the *staged* tree.  Nothing can enter history without passing it, and what `git archive`
ships is exactly what is in history.  A packaging step that tars the repository therefore
needs no extra discipline; a delivery that bypasses git should still run
`scripts/pack_gate.sh` immediately before the `tar`.

The `build-from-archive` job of `.github/workflows/lean_action_ci.yml` runs the same gates
and then *builds* the archive, so it also catches what an offline gate cannot.  But CI
only reports after a push: a delivery that does not go through CI must run
`scripts/pack_gate.sh` itself.

## Versioning policy from now on

* The library version lives in `lakefile.toml` (`version = "0.1.0"`) and is **independent**
  of the Lean toolchain version.
* Releases are cut by hand: bump `version` in `lakefile.toml`, add a file under
  `docs/release-notes/`, tag `vX.Y.Z`, and create the release from that tag.
* Bumping `lean-toolchain` (and the pinned Mathlib/`cslib` revisions in `lakefile.toml`)
  no longer creates a release.

## Package name

`lakefile.toml` declares `name = "lambda_computability"`, matching the repository name
`lambda-computability` (Lake package names must be Lean identifiers, so the hyphen is
written as an underscore).  The Lean library target is still called `Start`, so all
`import Start.…` lines are unaffected.
