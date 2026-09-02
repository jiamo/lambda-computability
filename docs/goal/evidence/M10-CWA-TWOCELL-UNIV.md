# M10-CWA-TWOCELL-UNIV

**Status:** DONE_STRONG

Module `Start/CwaTwoCellUniv.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings; `#print axioms` on
`Cwa.TwoCell.tmMap_eq`, `Cwa.TwoCell.preservesSmallPi`, `Cwa.TwoCell.preservesPiClosed`,
`LambdaPiBiInitial.isTerminal_empty_of_iso` and `LambdaPiBiInitial.iso_mor_necessary` reports only
`propext`, `Classical.choice`, `Quot.sound`.

`Start/CwaMorUniv.lean` says what it means for a morphism of categories with attributes to
preserve a universe, the dependent products over the small types and the codes for those
products — the structure an interpretation of `λΠ` has to respect.  `Start/CwaTwoCell.lean` adds
2-cells between morphisms.  Nothing so far related the two: a priori, a 1-cell isomorphic to an
interpretation of `λΠ` need not itself be one.  This module closes that gap.

## A 2-cell transports the action on terms

`Cwa.TwoCell.tmMap_eq` is the engine: for `θ : TwoCell F G` and a term `a` of `A` in context `Γ`,

    tmCast (θ.tySub_app A) (S.tmSub (θ.nat.app Γ) (G.tmMap a)) = F.tmMap a,

so `F.tmMap a` is `G.tmMap a` substituted along the component of `θ`.  Both sides are sections of
the same display map; a section into a context extension is determined by its composite with the
extension square, and the naturality of `θ.nat` computes that composite.

## Consequences

* `Cwa.TwoCell.codeMap_eq`, `Cwa.TwoCell.codeMap_preservesUniverse` — the action on codes is
  transported likewise;
* `Cwa.substCompare_congr_ty`, `Cwa.substCompare_eqToHom_left`,
  `Cwa.Universe.extHom_eq_substCompare` — the calculus of the canonical map out of an extended
  context needed to compare the two comparisons;
* **`Cwa.TwoCell.preservesUniverse`** — universe preservation is invariant under 2-cells;
* `Cwa.TwoCell.extElIso_hom_twoCell`, `Cwa.TwoCell.extElIso_inv_twoCell` — a 2-cell transports the
  comparison of the contexts extended by a decoded type;
* **`Cwa.TwoCell.preservesSmallPi`** — preservation of the dependent products over the small types
  is invariant under 2-cells;
* **`Cwa.TwoCell.preservesPiClosed`** — so is preservation of the codes for those products, for a
  universe whose codes are stable under substitution (the Beck–Chevalley condition of
  `Cwa.Universe.CodePi.code_sub`, which `Cwa.Universe.PiClosed` does not itself demand).

Each of the three preservation properties therefore depends only on the isomorphism class of a
1-cell in the hom-category of `Start/CwaBicat.lean`.

## The necessary conditions for a 1-cell out of the syntax of `λΠ`

* `LambdaPiBiInitial.preservesUniverse_of_twoCell` — a 1-cell out of the syntactic model receiving
  a 2-cell from the canonical interpretation preserves the universe;
* `LambdaPiBiInitial.isoObjEmpty`, `LambdaPiBiInitial.isTerminal_empty_of_iso` — a 1-cell
  isomorphic to the canonical interpretation sends the empty context to a terminal object;
* **`LambdaPiBiInitial.iso_mor_necessary`** — both at once.

The second condition is exactly the hypothesis under which
`LambdaPiBiInitial.nonempty_iso_mor_iff` of `Start/CwaBiInitial.lean` reduces the comparison with
the canonical interpretation to the existence of 2-cells, so the criterion is now pinned down from
both sides: the comparison can only exist for structure-preserving pointed 1-cells, and for those
it does exist.

## Boundary

This is a package of *necessary* conditions.  The sufficiency half — that every model of `λΠ`
receives a 1-cell from the syntactic model that is unique up to isomorphism, i.e. bi-initiality —
remains open, and is recorded on `M10-CWA-BICATEGORY`.

## Gates

* `lake build` — `Build completed successfully (9045 jobs)`, zero errors and zero warnings.
* `python3 scripts/goal_state.py validate`.
* `python3 scripts/check_closure.py` — 325 modules, all in the import closure and all registered.
* No `sorry` and no `admit` anywhere under `Start/`.
