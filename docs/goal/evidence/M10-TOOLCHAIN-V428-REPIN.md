# M10-TOOLCHAIN-V428-REPIN

**Status:** DONE_STRONG

The library builds against the toolchain the repository pins, Lean `v4.28.0`, with no
errors and no warnings.

## What had drifted

`lean-toolchain` reads `leanprover/lean4:v4.28.0`, the available Mathlib checkout is the
`v4.28.0` tag (`8f9d9cff6b`) and the available `cslib` checkout is the one built for that
toolchain (`.lake/packages/cslib_428`).  The sources, however, had been written against the
newer Mathlib and `cslib` APIs of `v4.33.0` (see `M10-TOOLCHAIN-V433-RESTORE`), so `lake
build` failed.  This task brings the sources back to the APIs of the pinned pair; the
mathematics is unchanged, only the names and a handful of proof steps.

## The pin

* `lean-toolchain`: `leanprover/lean4:v4.28.0`;
* Mathlib: local checkout at `.lake/packages/mathlib`, the `v4.28.0` tag
  (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`);
* `cslib`: local checkout at `.lake/packages/cslib_428`, the revision built for Lean
  `v4.28.0`;
* `lake-manifest.json`: regenerated for `cslib` (`lake update cslib`).  It previously
  omitted `cslib` altogether, which made `lake build` refuse to start.

## Sources brought back to the pinned APIs

* `Start/TM2Forward.lean`, `Start/TM2Capstone.lean` — `StateTransition.Reaches`,
  `StateTransition.eval` and `StateTransition.mem_eval` are `Turing.Reaches`, `Turing.eval`
  and `Turing.mem_eval` here.
* `Start/TM2Partrec.lean`, `Start/TM2PolyTime.lean` — `Turing.TM2Computable` and
  `Turing.TM2ComputableInPolyTime` take `Computability.FinEncoding`s, so
  `partrec_of_tm2Computable`, `partrec_of_tm2ComputableInPolyTime` and
  `haltsWithin_of_tm2ComputableInPolyTime` are stated for
  `ea : Computability.FinEncoding α`, `eb : Computability.FinEncoding β`, and read the
  encoded input as `ea.encode a`.
* `Start/CwaType.lean` — morphisms of `Type u` are plain functions here, so equality of
  morphisms is `funext` and no `TypeCat.Hom.ext` is needed.
* `Start/CwaCat.lean` — the `checkUnivs` linter option does not exist here; the comment
  explaining why the three universes of `Cwa.Model` are independent is kept and the
  `set_option` removed.
* `Start/LambdaPiInitial.lean` — the `extIso_extend` field of the comparison morphism is
  closed by the simp set the pinned Mathlib actually needs.
* `Start/Representation.lean` — the pinned `cslib` presents full β-reduction as a single
  inductive `Term.FullBeta` with constructors `beta`, `appL`, `appR`, `abs` (rather than a
  congruence closure `Term.Xi` over `Term.Beta`), its confluence is `Term.confluence_beta`,
  and `Term.subst_intro` carries a local-closure hypothesis for the substituted term.
* `Start/Kolmogorov.lean`, `Start/MartinLof.lean`, `Start/PostSimple.lean`,
  `Start/BusyBeaver.lean`, `Start/OmegaURandom.lean` — `Set.mem_ofPred_eq` /
  `Set.mem_ofPred` are `Set.mem_setOf_eq` / `Set.mem_setOf` here.
* `Start/OmegaUncomputable.lean` — the parity case split of `ofNat_int_toNat` must record
  the case hypothesis (`cases hb : n.bodd <;> simp [hb]`).
* `Start/UniformSigSmash.lean`, `Start/UniformSigLang.lean`, `Start/UniformSegDec.lean` —
  three goals reach `omega` with an unreduced β-redex in them; `beta_reduce` first.

## Registration gap closed

`scripts/check_closure.py` reported four terminal modules that were neither used nor
registered: `Start/Inseparable.lean`, `Start/OracleCone.lean`, `Start/OracleJoin.lean` and
`Start/OracleUniversal.lean`.  `Start/Capstones.lean` now has a section for them —
the relativised enumeration theorem and the jump being r.e. in its oracle, the join as the
least upper bound of two degrees, the countability of a cone and the uncountability of the
degree structure, and the recursively inseparable pair of r.e. sets.

## Gates

```
lake build                       # 8321 jobs, 0 errors, 0 warnings
python3 scripts/check_closure.py # OK: 284 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

No module under `Start/` contains `sorry` or `admit`.
