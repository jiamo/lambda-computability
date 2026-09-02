# M10-MANIFEST-RESTORE-V433

**Status:** DONE_STRONG

The checked-in `lake-manifest.json` had again drifted from `lakefile.toml`: it carried no entry for
`cslib` at all, and its Mathlib entry recorded an older input revision than the one the lakefile
requires, so `lake build` stopped immediately with

```
error: dependency 'cslib' not in manifest
```

and nothing in the library could be compiled.

## The repair

`lake update`, run under the pinned toolchain `leanprover/lean4:v4.33.0`, regenerated the manifest
against `lakefile.toml`.  It now records exactly the required dependencies:

* `mathlib` — `db584cd6d46c92f209a44c0f1c829460d327499d`, the `v4.33.0` tag, with its build cache
  fetched by the post-update hook;
* `cslib` — `3951377e5a3f5772737f11cd62bc5bb6a72f95d1`, the revision that moves `cslib` to Lean
  `v4.33.0`;
* the transitive dependencies `batteries`, `aesop`, `Qq`, `proofwidgets`, `Cli`, `importGraph`,
  `LeanSearchClient` and `plausible` at the revisions that tag requires.

No source file under `Start/` had to change: the library compiles unmodified against the pin it
documents.

## Gates

* `lake build` — `Build completed successfully (9061 jobs)`, zero errors and zero warnings.
* `python3 scripts/check_closure.py` — all modules in the import closure and all registered.
* `python3 scripts/goal_state.py validate` — board validates.
* No `sorry` or `admit` anywhere under `Start/`.
