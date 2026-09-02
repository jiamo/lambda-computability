# M10-MODEST-CCC

**Status:** DONE_STRONG

Module `Start/ModestCcc.lean`, imported by `Start.lean` and registered in `Start/Capstones.lean`.
It builds without `sorry` and without linter warnings.

## What this task adds

`Start/Modest.lean` already showed that modesty is stable under the terminal object, the binary
products and the exponentials of `Asm(A)`, but only as a statement about objects.  This module
makes the full subcategory `Realizability.ModestCat A` of the modest assemblies into a cartesian
closed category with that structure.

- `Realizability.Assembly.Modest.of_iso` — **modesty is invariant under isomorphism**: a realizer
  of two elements of `X` is carried by a tracker of `e.hom` to a *single* realizer of their images,
  which modesty of `Y` identifies, and `e.inv` cancels.
- `Realizability.Modest.unitModest`, `Realizability.Modest.isTerminalUnitModest` — the terminal
  assembly is terminal among the modest ones (the inclusion is full, so the unique map of `Asm(A)`
  is the unique map here).
- `Realizability.Modest.prodModest`, `Realizability.Modest.prodFanModestIsLimit` — the product
  assembly of two modest assemblies is their product in the subcategory, and
  `Realizability.Modest.instCartesianMonoidalCategory` packages the two as a cartesian monoidal
  structure with `X ⊗ Y` the product assembly on the nose.
- `Realizability.Modest.expModest`, `Realizability.Modest.curryEquivModest`,
  `Realizability.Modest.instClosedModest` — the exponential assembly of two modest assemblies is
  modest, currying is a bijection `(X × Y ⟶ Z) ≃ (Y ⟶ X ⇒ Z)`, and it is natural, giving the
  adjunction `X × - ⊣ X ⇒ -`; hence
  **`Realizability.Modest.instMonoidalClosed : MonoidalClosed (ModestCat A)`**.
- `Realizability.PER.hasFiniteProducts`, `Realizability.PER.instCartesianMonoidalCategory`,
  **`Realizability.PER.instMonoidalClosed`** — transported along the equivalence
  `Realizability.perEquivModest` of the previous task, the category of PERs has finite products and
  is cartesian closed as well; `Realizability.PER.toModestArrowIso` records that the comparison
  functor carries the arrow PER to the exponential of the modest assemblies.

## Gates

- `lake build Start.ModestCcc` — success, no warnings.
- `lake build` — the whole library still builds.
- `python3 scripts/check_closure.py` — 322 modules, all in the import closure and all registered.
- `python3 scripts/goal_state.py validate` — board validates.
