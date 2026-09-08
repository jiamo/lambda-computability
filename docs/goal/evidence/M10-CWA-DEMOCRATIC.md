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

## What is proved — `Start/CwaHomOver.lean` and `Start/CwaLcccOfFull.lean`

Both modules build without `sorry`, are imported by `Start.lean`, and `#print axioms` on their
results reports only `propext`, `Classical.choice`, `Quot.sound`.

* `Cwa.HomOver`, `Cwa.homOverEquivTm` — in an arbitrary category with attributes, the maps into a
  display map lying over a substitution `σ` are exactly the terms of the substituted type, and
  `Cwa.homOverEquivTm_symm_precomp` / `Cwa.tmCast_tmSub_extend` say that precomposing the map of a
  term is substituting the term.
* `Cwa.LcccOfFull.piObj`, `Cwa.LcccOfFull.transpose` — for a full model with a Π-structure, the
  dependent product of an object of a slice, and the bijection between the maps out of the
  pullback and the maps into it.  It is the composite of: presenting the slice object by a type
  over the extended context (fullness), reading a map over a substitution as a term
  (`Cwa.homOverEquivTm`), `lam`/`app`, and stability of `Pi` under substitution.
* `Cwa.LcccOfFull.transpose_naturality` — the transposition is natural in the slice object over
  the base; the essential ingredient is the law `(λ b)[σ] = λ (b[σ⁺])` of a natural Π-structure,
  transported along the comparison of the two extended contexts
  (`Cwa.LcccOfFull.extCompare_extend`, `Cwa.LcccOfFull.pbIso_naturality`).
* **`LcccPullbacks.ofIsFull`** — the category of contexts of a full model whose substitution on
  extended contexts is coherent (`Cwa.ExtCoherent`) and which carries a natural Π-structure is
  locally cartesian closed.  This is exit criterion 2, for an arbitrary full model and not only
  for a strictified one.

## What is proved — `Start/CwaStrictifyFull.lean`

* `Cwa.luTyMap`, `Cwa.luTyMap_sub` — a local universe over `Γ` is sent to the presentation of its
  generic family substituted along its classifying map, and this commutes with substitution *on
  the nose*, because substitution of a local universe acts on the classifying map alone.
* **`Cwa.fullStrictify`** — hence a morphism of models `Cwa.ofPullbacks C ⟶ T` out of the
  strictification of the category of contexts of a full model `T`, which is the identity on
  contexts.
* `Cwa.fullStrictify_tmMap_bijective` — it is a bijection on terms;
  `Cwa.fullStrictify_essSurj` — and every type of `T` is in its image up to an isomorphism of
  extended contexts over the base.
* `Cwa.nonempty_naturalPiStruct_ofPullbacks_of_isFull` — for a full *democratic* model with a
  natural Π-structure the contexts have pullbacks and a terminal object, hence binary products,
  and are locally cartesian closed, so the strictification of the contexts is itself a model with
  a natural Π-structure.

## Boundary

What remains of exit criterion 3 is the *equivalence* of a full democratic model with the
strictification of its contexts, in the lax 2-category of models.  A morphism the other way,
`T ⟶ Cwa.ofPullbacks C`, would have to send a type over `Γ` to a local universe whose base and
generic family do not depend on `Γ` — that is, it would amount to a universe for the model, which
a model need not have.  It is not constructed here, and neither its existence nor its
non-existence is claimed; what is proved is the comparison `Cwa.fullStrictify` in the other
direction, together with its bijectivity on terms and essential surjectivity on types.
