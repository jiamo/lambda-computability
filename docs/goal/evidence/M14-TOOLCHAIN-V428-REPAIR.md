# M14-TOOLCHAIN-V428-REPAIR

**Status:** DONE_STRONG

The tree builds again on the toolchain/Mathlib pair that is actually available, with the
dependency manifest agreeing with `lakefile.toml`, no errors and no warnings.

## What had drifted

Three things were inconsistent in the delivered tree:

* `lake-manifest.json` named the package `start` while `lakefile.toml` declares
  `lambda_computability`, recorded `inputRev = v4.28.0` for Mathlib against a `v4.33.0`
  requirement, and omitted the `cslib` entry altogether — with that manifest `lake` refuses to
  start at all (`dependency 'cslib' not in manifest`).
* `lean-toolchain` and `lakefile.toml` asked for Lean `v4.33.0` and Mathlib `v4.33.0`, but the
  Mathlib checkout available here is the `v4.28.0` tag (`8f9d9cff6b`), built with Lean
  `v4.28.0`; under `v4.33.0` no module that imports Mathlib can be elaborated.
* Several sources had been written against the `v4.33` APIs.

## The pin

* `lean-toolchain`: `leanprover/lean4:v4.28.0`;
* Mathlib: `rev = "v4.28.0"`, resolved to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`;
* `cslib`: `rev = "b13a67207c489f4b3f816cf96fcd3d38855db80f"` — the last revision of `cslib`
  whose own `lean-toolchain` is `v4.28.0` and whose manifest pins the same Mathlib commit;
* `lake-manifest.json`: package name corrected, Mathlib `inputRev` corrected, `cslib` entry
  added, so `python3 scripts/check_manifest.py` passes.

## Sources brought back to the pinned APIs

* `Start/TM2Forward.lean`, `Start/TM2Capstone.lean` — `StateTransition.Reaches`, `.eval`,
  `.mem_eval` are `Turing.Reaches`, `Turing.eval`, `Turing.mem_eval`.
* `Start/TM2Partrec.lean`, `Start/TM2PolyTime.lean` — `Turing.TM2Computable` and
  `Turing.TM2ComputableInPolyTime` take `Computability.FinEncoding`s, so the statements read the
  input as `ea.encode a`, and the non-vacuity example supplies `ea.ΓFin` as the finiteness of the
  stack alphabets.
* `Start/Representation.lean` — the pinned `cslib` presents full β-reduction as a single
  inductive `Term.FullBeta` with constructors `beta`, `appL`, `appR`, `abs`, its confluence is
  `Term.confluence_beta`, and `Term.subst_intro` carries a local-closure hypothesis for the
  substituted term.
* `Start/CwaType.lean`, `Start/CwaStrictRigid.lean`, `Start/CwaFamiliesNoStrictify.lean` —
  morphisms of `Type u` are plain functions, so `TypeCat.ofHom` and `TypeCat.homEquiv` disappear
  and equality of morphisms is `funext`; `isDemocratic_families` must be `noncomputable`.
* `Start/CwaCat.lean` and the other users of `set_option linter.checkUnivs` — that option does
  not exist here; the comment explaining why the universes of the models are independent is kept.
* `Start/PCATotal.lean`, `Start/CwaTwoCell.lean`, `Start/CwaLaxCategory.lean`,
  `Start/CwaLaxBicat.lean` — the `@[instance_reducible]` attribute does not exist here.
* `Start/OracleSim.lean` — `RecursiveIn` is the inductive predicate itself, so the named wrappers
  are its constructors and `RecursiveIn.iff_nat` disappears; `Part.mem_bind_iff` is applied by
  `simp` rather than explicitly.
* `Start/KrivineSpace.lean`, `Start/KrivineSpaceGc.lean` — `List.Nodup.length_le_of_subset` is
  `(List.subperm_of_subset _ _).length_le`.
* `Start/Kolmogorov.lean`, `Start/MartinLof.lean`, `Start/PostSimple.lean`,
  `Start/BusyBeaver.lean`, `Start/OmegaURandom.lean`, `Start/EffectiveOperation.lean` —
  `Set.mem_ofPred(_eq)` is `Set.mem_setOf(_eq)`.
* `Start/OmegaUncomputable.lean` — the parity case split must record the case hypothesis.
* `Start/MultiTypes.lean` — `ac_rfl` on pointwise multiset contexts is `add_add_add_comm`.
* `Start/AsmExRegProd.lean` — the limit fields need `beta_reduce` before the quotient induction,
  so that the endpoints of the fan are abstracted.
* `Start/AssemblyKleeneBool.lean`, `Start/CwaLcccOfFull.lean`,
  `Start/LambdaPiInterpTransport.lean`, `Start/CwaStrictSection.lean`,
  `Start/CwaStrictPseudofunctor.lean`, `Start/Qbf.lean` — rewriting chains need one fewer (or, in
  one place, one more) closing `rfl` under the simp normal forms of this Mathlib.
* `Start/GapTheorem.lean` — elaborating the primitive-recursion step function of
  `computable_goodB` costs several minutes here, so the heartbeat budget is lifted for that
  declaration, with a comment saying why.

## Delivery chain

`scripts/install_hooks.sh` was run in this clone, so `core.hooksPath = .githooks` is in effect and
every commit of this batch ran `scripts/pack_gate.sh` on the staged tree.

## Gates

```
lake build                        # Build completed successfully, 0 errors, 0 warnings
python3 scripts/check_manifest.py # OK, agrees with lakefile.toml
python3 scripts/check_sorry.py    # OK: no sorry/admit
python3 scripts/check_closure.py  # OK: all modules in the import closure and registered
python3 scripts/goal_state.py validate
python3 scripts/pack_gate.sh      # via the pre-commit hook, on every commit
```

## Note for this repository

This repository did **not** take the downgrade recorded above.  It stays on
`leanprover/lean4:v4.33.0` with Mathlib `v4.33.0` (`db584cd6`) and `cslib`
`3951377e`, the pair that `scripts/check_manifest.py` accepts here.  The repair described
above applies to the delivering tree, where only a Mathlib `v4.28.0` checkout is available;
the ~50 modules it rewrote backwards to the `v4.28` APIs are therefore not merged, and the
modules delivered alongside it were taken only after checking they use no `v4.28`-only API.
