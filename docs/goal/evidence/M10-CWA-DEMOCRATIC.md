# M10-CWA-DEMOCRATIC

**Status:** DONE_WEAK

`Start/LcccBiequivalence.lean` (M10-CWA-BICATEGORY) compares the 2-category of locally cartesian
closed categories with the 2-category `Cwa.LcccModelCat` of the models they present.  That class
of models is described by how its objects are built — as strictifications — rather than by a
property of a model.  This task is the intrinsic description.

## What is proved — `Start/CwaDemocratic.lean`

The module builds without `sorry`, is imported by `Start.lean`, and `#print axioms` on its results
reports only `propext`, `Classical.choice`, `Quot.sound`.

* `Cwa.IsFull T` — a model is **full** when every morphism of contexts `f : X ⟶ Z` is a display
  map up to isomorphism over its codomain: a type `ty f` over `Z`, an isomorphism
  `X ≅ ext Z (ty f)` and the equation saying it lies over `Z`.
* `Cwa.IsDemocratic T` — a model is **democratic** when it has a terminal context and every
  context is, up to isomorphism, an extension of it, so that a context is a closed type.
* `Cwa.IsFull.isPullback`, `Cwa.IsFull.hasPullback` — in a full model, an arbitrary cospan is the
  extension square of the type presenting one of its legs, transported along the isomorphism that
  presents it, hence a pullback square.
* **`Cwa.hasPullbacks_of_isFull`** — the category of contexts of a full model has pullbacks.
* `Cwa.isFull_ofPullbacks`, `Cwa.isDemocratic_ofPullbacks` — the strictification of a category
  with pullbacks is full, and democratic as soon as the category has a terminal object.  So the
  objects of `Cwa.LcccModelCat` do have both properties, and the intrinsic description is at least
  not too narrow.

## Boundary

Two steps are missing before `Cwa.LcccModelCat` could be replaced by the 2-category of full
democratic models of the dependent product.

1. **From a Π-structure on a full model to local cartesian closure of its contexts.**
   `Start/CwaLcccOfPi.lean` does this for the *strictified* model
   (`LcccPullbacks.ofNaturalPiStruct`), where a type is a local universe.  For a general full
   model the dependent product has to be transported along the presentation `Cwa.IsFull.ty`,
   which is stable under substitution only up to isomorphism, so the adjunction between the
   slices has to be built directly from `lam`/`app` rather than by transporting the existing
   proof.
2. **The comparison of a full democratic model with the strictification of its contexts**, as an
   equivalence in the lax 2-category of models.
