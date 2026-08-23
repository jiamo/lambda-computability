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
