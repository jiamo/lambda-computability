# M7-VERIFICATION-DEBT

**Status:** DONE_STRONG

The milestone M7 modules had been written but never validated end to end against the
Lean `v4.33.0` toolchain, and the checked-in dependency manifest disagreed with
`lakefile.toml`. Both problems are fixed.

## Dependency manifest

`lake-manifest.json` recorded every dependency as a **path** package pointing into
`.lake/packages/…`, which is not part of the repository. On a clean checkout Lake then
re-resolves (and, without a cache, recompiles) all dependencies on every invocation.

`lake update` regenerated the manifest with **git** dependencies, with Mathlib pinned to
`db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`). The three version sources now
agree:

* `lean-toolchain`: `leanprover/lean4:v4.33.0`;
* `lakefile.toml`: `rev = "v4.33.0"`;
* `lake-manifest.json`: the corresponding Mathlib revision, plus the transitive
  dependencies (`batteries`, `aesop`, `Qq`, `proofwidgets`, `importGraph`,
  `LeanSearchClient`, `plausible`, `Cli`) at the revisions Mathlib pins.

## Build

* `lake build` — `Build completed successfully (8760 jobs)`, no errors, no linter
  warnings, no stray `Try this` output.
* `lake build Start Start.Demo Start.DecodeTest` — `Build completed successfully
  (8763 jobs)`; the showcase and the scratch decoding test compile as well.

## Two real defects found by the build

1. **`Start/OmegaOracle.lean` did not compile.** In `Lambda.partrec_oracleRun` the
   `Primrec.nat_lt` instance obtained by `obtain ⟨_inst, hlt⟩` is not syntactically the
   instance Lean elaborates for the goal, so `simp` reduced the goal to
   `decide P = decide P` with two different `Decidable P` instances and left it open. It
   is closed by `decide_eq_decide.mpr Iff.rfl`, which is insensitive to the instance.
2. **`Start/OmegaOracle.lean` was not imported by `Start.lean`,** so the failure was
   invisible to `lake build`. The import was added; every module under `Start/` is now
   either imported by `Start.lean` or built explicitly by the gate above.

## Other gates

* `rg 'sorry|admit' Start.lean Start/` finds only prose occurrences (`admits`,
  "no sorry" in the demo commentary) — no `sorry`, no `admit` in any proof.
* `python3 scripts/goal_state.py validate` passes.
