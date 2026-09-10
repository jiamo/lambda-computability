# M10-CWA-DEMOCRATIC

**Status:** DONE_STRONG

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

## Exit criterion 3, settled — `Start/CwaStrictifyEquiv.lean` and `Start/CwaFamiliesNoStrictify.lean`

Exit criterion 3 asked for an *equivalence*, in the lax 2-category of models, between a full
democratic model and the strictification of its contexts.  As stated it is **false**, and the two
modules say exactly how much of it survives.

*What an equivalence would take.*  In the lax 2-category a 2-cell is nothing but a natural
transformation of the functors on contexts (`Cwa.LaxTwoCell.ofNat`, `Cwa.LaxTwoCell.ext_of_nat`),
so an isomorphism of 1-cells is an isomorphism of those functors: `Cwa.laxIsoOfNatIso`.
Consequently the *only* thing an equivalence needs, beyond `Cwa.fullStrictify`, is a morphism of
models back, and one that is the identity on contexts already suffices:
`Cwa.fullStrictify_comp_iso_id` and `Cwa.comp_fullStrictify_iso_id` show that both composites are
then isomorphic to the identity 1-cells.  A morphism `T ⟶ Cwa.ofPullbacks C` sends a type over `Γ`
to a local universe whose base and generic family do not depend on `Γ`, so it is a universe naming
every type of the model.

*And a full democratic model need not have one.*  `CwaType.families`, the standard model of
families of types (contexts are types, a type over `Γ` is a family `Γ → Type u`), is full
(`CwaType.isFull_families`), democratic (`CwaType.isDemocratic_families`), coherent
(`CwaType.extCoherent_families`) and has a Π-structure (`CwaType.piStruct`) — so
`Cwa.fullStrictify` applies to it — and yet:

* `CwaType.total_tySub` — substitution acts on the classifying map alone, so the generic family a
  morphism of models assigns to a type is unchanged by substitution;
* `CwaType.total_const_eq` — a family over a two-element context connects any two closed types,
  so *all* closed types get one and the same generic family;
* `CwaType.exists_injective_total` — the extended context of a closed type embeds into that
  generic family (the image of the terminal context is a singleton, so the pullback embeds in the
  total space);
* **`CwaType.false_of_mor_isEquivalence`** — hence there is no morphism of models
  `CwaType.families ⟶ Cwa.ofPullbacks (Type u)` whose functor on contexts is an equivalence: every
  type of `Type u`, `Set Q` included, would embed into a single type `Q`, which Cantor's theorem
  forbids;
* **`CwaType.not_equivalent_ofPullbacks`** — so the standard model is **not** equivalent, in the
  lax 2-category, to the strictification of its own category of contexts.

So the intrinsic description of the models presented by locally cartesian closed categories cannot
be "full and democratic" up to equivalence of models: fullness and democracy give the contexts
their pullbacks and their local cartesian closure (exit criteria 1 and 2, above) and the comparison
`Cwa.fullStrictify`, bijective on terms and essentially surjective on types, but a genuine
equivalence needs a universe, and the standard model has none.  Both modules build without
`sorry`, are imported by `Start.lean`, registered in `Start/Capstones.lean`, and `#print axioms` on
their results reports only `propext`, `Classical.choice`, `Quot.sound`.
