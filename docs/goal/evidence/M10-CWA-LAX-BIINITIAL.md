# M10-CWA-LAX-BIINITIAL

**Status:** DONE_WEAK

Module `Start/CwaLaxBiInitial.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warning; `#print axioms` on
the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

## Why this task exists

Bi-initiality *in the lax sense* could not previously be stated at all: mathlib's
`Bicategory.BiInitial` needs a bicategory, and the models with lax 2-cells were not one.  With
`M10-CWA-LAX-BICAT` they are, so the question can be asked for the first time.

## What is proved

* **`Cwa.LaxCModel.biInitial_iff`** — bi-initiality in the lax 2-category is a condition on the
  functors on contexts alone: `X` is bi-initial exactly when there is a 1-cell into every object
  and, between the functors underlying any two 1-cells out of `X`, there is exactly one natural
  transformation.  This is the classification of lax 2-cells (`M10-CWA-LAX-RIGID`) applied to the
  three clauses of `Bicategory.BiInitial`.
* `LambdaPi.Model.toCModel`, `LambdaPi.Model.toLaxCModel`,
  `LambdaPiLaxBiInitial.laxSyntacticCModel`, `LambdaPiLaxBiInitial.laxNoTypesCModel` — the models
  of `λΠ`, the syntactic model and the model with no types as objects of the lax 2-category.
* **`LambdaPiLaxBiInitial.not_biInitial_laxSyntacticCModel`** — the syntactic model of `λΠ` is
  **not** bi-initial in the lax 2-category of all coherent models.  Weakening the 2-cells does not
  help: the obstruction is one-dimensional, there being no 1-cell at all into the model with no
  types, exactly as in the strict case (`LambdaPiBiInitial.not_biInitial_syntacticCModel`).
* `LambdaPiLaxBiInitial.nonempty_hom_lax` — into every small model of `λΠ` with injective products
  there is a 1-cell out of the syntax, namely the interpretation.
* `LambdaPiLaxBiInitial.nonempty_laxTwoCell_modelHom` — between any two morphisms of models out of
  the syntax there is a lax 2-cell: the image of the unique strict one.
* `LambdaPiLaxBiInitial.subsingleton_laxTwoCell_iff_natTrans` — the outstanding uniqueness clause,
  reduced: there is at most one lax 2-cell between two 1-cells out of the syntax exactly when the
  two interpretation functors admit at most one natural transformation.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxBiInitial
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

The uniqueness clause for the models of `λΠ` with injective products is **not** claimed, in either
direction.  The rigidity argument that settles it for strict 2-cells
(`LambdaPiBiInitial.app_eq_of_app_empty`) forces the component at an extended context from the
component at the base, using the compatibility of a *strict* 2-cell with the types; a bare natural
transformation has no such compatibility, and naturality alone leaves the term component at an
extension free.  So the argument does not transfer, and no counterexample is exhibited either.
Consequently a positive lax bi-initiality statement for the syntactic model is not available; what
is available is the reduction above, together with the negative result for all coherent models.
