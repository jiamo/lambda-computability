# M10-CWA-LAX-BIINITIAL

**Status:** DONE_STRONG

Modules `Start/CwaLaxBiInitial.lean`, `Start/PointedCwa.lean`, `Start/PointedModel.lean` and
`Start/CwaLaxNotUnique.lean`, imported by `Start.lean` and registered in
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

* **`PointedModel.not_subsingleton_laxTwoCell_modelHom`** — the uniqueness clause **fails**, so
  the syntactic model of `λΠ` is not bi-initial in the lax 2-category even when the models are
  restricted to those of `λΠ` with injective products.  The witness is a new, non-syntactic model:

  * `PointedModel.ptCwa` — a category with attributes on the category of pointed sets: a type over
    a pointed set `Γ` is a function `Γ → Bool × ℕ`, decoded as `ℕ` (the universe of codes) or as a
    one-point set (a small type), the boolean deciding which and the natural number serving as a
    tag;
  * `PointedModel.ptModel` — the corresponding **model of `λΠ`**: the universe of small types is
    `ℕ`, and the code of a product of two small types is the Cantor pairing of their codes.  It is
    pointed because `Nat.pair 0 0 = 0`;
  * `PointedModel.ptModel_piInj` — its product former is **injective**, so the interpretation
    `PointedModel.ptModelHom` of the syntax exists;
  * `PointedModel.collapseNat` — the constant map to the base point is a natural endomorphism of
    any functor into the pointed sets, hence of the interpretation functor;
  * `PointedModel.starCtx_not_subsingleton` — the interpretation of the context `x : ∗` has more
    than one point (its fibre is the universe `ℕ`), so that natural endomorphism is not the
    identity: `PointedModel.not_subsingleton_natTrans`, and therefore
    `PointedModel.not_subsingleton_laxTwoCell`.

  The strict rigidity theorem is untouched: the collapsing 2-cell is not a strict one, because
  substituting along a constant map does not carry a type to itself.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxBiInitial Start.PointedModel Start.CwaLaxNotUnique
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

None.  Both halves are now settled: the existence clauses hold for the models of `λΠ` with
injective products, and the uniqueness clause fails there, so the syntactic model is not bi-initial
in the lax 2-category in any of the readings considered.
