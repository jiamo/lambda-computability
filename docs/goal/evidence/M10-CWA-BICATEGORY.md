# M10-CWA-BICATEGORY

**Status:** DONE_WEAK

Modules `Start/CwaTwoCell.lean`, `Start/CwaBicat.lean` and `Start/CwaBiInitial.lean`, all imported
by `Start.lean`.  They build without `sorry`; `#print axioms` on the headline declarations reports
only `propext`, `Classical.choice`, `Quot.sound`.

Before this work, two morphisms of categories with attributes could only be compared with `=`, so
no statement "unique up to isomorphism" was expressible.  These files add the missing dimension.

## 2-cells — `Start/CwaTwoCell.lean`

A `Cwa.TwoCell F G` between morphisms `F G : Mor T S` of categories with attributes consists of a
natural transformation `nat` between the underlying context functors, an action on types, and
coherence conditions relating the two with substitution and with context extension.  The auxiliary
`substCompare` compares a type transported along a substitution with a given type, and
`substCompare_congr`, `substCompare_id`, `substCompare_comp`, `extIso_substCompare` are its
calculus.

* `TwoCell.id`, `TwoCell.vcomp` — identities and vertical composition;
* `Cwa.morCategory` — for an extensionally coherent target, `Mor T S` is a category;
* `TwoCell.inv`, `TwoCell.inv_tySub`, `TwoCell.isIso_of_isIso_nat` — a 2-cell is invertible as soon
  as its underlying natural transformation is;
* `TwoCell.app_ext`, `app_ext_congr`, `app_eq_of_iso` — the component at an extended context is
  determined by the component at the base;
* `TwoCell.whiskerLeft`, `TwoCell.whiskerRight`, `TwoCell.whisker_exchange` — horizontal structure
  and the exchange law.

## The bicategory of models — `Start/CwaBicat.lean`

`Cwa.CModel` bundles a category with attributes together with the extensional coherence needed for
the hom-categories to exist.  `instCategoryStruct`, `instHomCategory`, and then
**`Cwa.CModel.instBicategory : Bicategory CModel`** in mathlib's sense, with
`Cwa.CModel.instStrict : Bicategory.Strict CModel` recording that the associators and unitors are
identities.  `CModel.hom_ext` and `CModel.isIso_of_isIso_nat` transport the 2-cell lemmas to the
bicategorical notation.

## Bi-initiality — `Start/CwaBiInitial.lean`

`CategoryTheory.Bicategory.BiInitial X` says every hom-category `X ⟶ Y` is contractible: inhabited,
with a morphism between any two objects, and with any two such morphisms equal.  From it,
`BiInitial.nonempty_iso` (any two 1-cells out of `X` are isomorphic) and
`BiInitial.nonempty_equiv` (any two bi-initial objects are equivalent).

For the syntax of λΠ, `LambdaPiBiInitial.syntacticCModel` packages the syntactic model as an object
of the bicategory, and then:

* `app_eq_of_app_empty` — a 2-cell out of the syntactic model is determined by its component at the
  empty context;
* **`subsingleton_twoCell`**, **`subsingleton_twoCell_mor`** — hence, when the image of the empty
  context is terminal, there is at most one 2-cell between any two interpretations;
* `isIso_twoCell` — and such a 2-cell is automatically invertible;
* `mor_obj_empty`, `isTerminal_mor_empty` — for a model with injective Π, the interpretation
  produced by initiality sends the empty context to a terminal object;
* **`nonempty_iso_mor_iff`** — two interpretations of the syntactic model into such a model are
  isomorphic exactly when the image of the empty context is terminal.

## Boundary

`M10-CWA-TWOCELL-UNIV` and `Start/CwaTwoCellUniv.lean` have since added the *necessary* half of
bi-initiality: a 1-cell out of the syntactic model isomorphic to the canonical interpretation
preserves the universe, the small products and their codes, and sends the empty context to a
terminal object.  The sufficiency half is still what is missing.

Bi-initiality of the syntactic model is not proved.  What is proved is rigidity — 2-cells out of
the syntactic model are unique when they exist, and invertible — together with an exact criterion
for two interpretations to be isomorphic.  The criterion is not vacuous but it is also not always
satisfied: in the 2-category of *all* coherent models the syntactic model is not bi-initial, since
nothing forces the image of the empty context to be terminal.  Settling which subclass of models
makes the statement true (and where the universe should live, given that a strictified universe
need not be closed under pushforward) is left open.  The pseudofunctors between models with Π and
locally cartesian closed categories, and the proof that they are mutually inverse, are not
constructed.

## Update (M10-LAMBDAPI-SELF-INITIAL)

The sufficiency half has since been proved for the 1-cells that come from a morphism of models of
λΠ: `Start/LambdaPiSelfMor.lean` produces the missing 2-cell out of the canonical interpretation
(`LambdaPiSelf.isoModelHom`, `LambdaPiSelf.nonempty_unique_twoCell_modelHom`), by showing that the
syntax interprets itself by the identity (`LambdaPiSelf.selfIso`) and transporting along the
naturality 2-cell of `Start/LambdaPiInitialNatural.lean`.  What remains open is the bicategorical
statement for arbitrary coherent models — false as stated, by
`not_biInitial_syntacticCModel` — and the pseudofunctors to locally cartesian closed categories.

## Update (the lax 2-category)

The weakening the boundary above calls for has since been carried out in full.  `M10-CWA-LAX-RIGID`
shows that the comparison a lax 2-cell carries is *uniquely determined* by its natural
transformation, so that a lax 2-cell between two morphisms of models is exactly a natural
transformation of the functors on contexts (`Cwa.LaxTwoCell.equivNatTrans`).  This refutes the
earlier reading, recorded in `Start/CwaLaxWhisker.lean` and in the evidence of
`M10-CWA-LAX-WHISKER`, that the interchange law cannot even be stated for the present notion of
lax 2-cell and that the definition would have to be enlarged first: the law holds for arbitrary
lax 2-cells on both sides (`M10-CWA-LAX-INTERCHANGE`, `Cwa.LaxTwoCell.whisker_exchange`), the
mixed case in which one side is a strict 2-cell being a corollary rather than the best available
result.  Consequently the coherent models with lax 2-cells do form a strict bicategory
(`M10-CWA-LAX-BICAT`, `Cwa.LaxCModel.instBicategory`), as do the categories with pullbacks
(`Cwa.PbCat.instBicategory`), and strictification carries whiskering to whiskering in both
dimensions.  Bi-initiality in the lax 2-category, which had never been stateable, is treated in
`M10-CWA-LAX-BIINITIAL`.

What remains open here is unchanged: the pseudofunctors between models with Π and locally
cartesian closed categories, and the biequivalence.

## Update (the comparison with locally cartesian closed categories)

Two of the three pieces the boundary above asks for are now in place, in
`Start/CwaStrictPseudofunctor.lean` and `Start/LcccPseudofunctor.lean` (both imported by
`Start.lean`, both `sorry`-free, `#print axioms` reporting only `propext`, `Classical.choice`,
`Quot.sound`).

* **`Cwa.strictificationPseudofunctor : Pseudofunctor PbCat LaxCModel`** — strictification is a
  morphism of 2-categories in mathlib's sense: a category with pullbacks is a model of a dependent
  type theory (`Cwa.PbCat.toLaxCModel`), a pullback-preserving functor a morphism of models, and a
  natural transformation a lax 2-cell, compatibly with both whiskerings, the associator and the
  unitors.  Its structural isomorphisms are transports along the equalities
  `Cwa.morOfPreservesPullbacks_id` and `Cwa.morOfPreservesPullbacks_comp`
  (`strictificationPseudofunctor_mapId`, `strictificationPseudofunctor_mapComp`), so the
  pseudofunctor is in fact strict.  It is faithful on 1-cells
  (`strictificationPseudofunctor_map_injective`) and locally fully faithful: on 2-cells it is the
  identity on the underlying natural transformations
  (`strictificationPseudofunctor_map₂_nat`, `strictificationPseudofunctor_map₂_bijective`).
* **`Cwa.LcccCat`** — the 2-category of locally cartesian closed categories, the full
  sub-2-category of `Cwa.PbCat` spanned by the objects `Cwa.LcccObj` that carry binary products
  and a right adjoint to every substitution functor; it is inhabited by the category of sets
  (`Cwa.LcccObj.type`).
* **`Cwa.lcccPseudofunctor : Pseudofunctor LcccCat LaxCModel`** — strictification restricted to
  it.  Every value is a model of the dependent product (`Cwa.lcccNaturalPiStruct`), and
  conversely the strictification of a category with pullbacks and binary products carries a
  natural Π-structure exactly when the category is locally cartesian closed
  (`Cwa.nonempty_naturalPiStruct_toLaxCModel_iff`), so on objects the pseudofunctor hits, up to
  that structure, precisely the models of Π that come from a category with pullbacks.  It is
  faithful on 1-cells and locally fully faithful (`Cwa.lcccPseudofunctor_map_injective`,
  `Cwa.lcccPseudofunctor_map₂_bijective`).

What is still missing is only the third piece: a pseudofunctor back from models with Π to locally
cartesian closed categories and a biequivalence.  It cannot be built for arbitrary models — the
context category of a model of Π need not be locally cartesian closed, and a model need not have
enough types — so the statement would first have to be restricted to the models that are
democratic and full, which is not formalized here.

## Update (the pseudofunctor back, and the biequivalence) — the task is now DONE_STRONG

The third piece is in place, in `Start/LcccBiequivalence.lean` (imported by `Start.lean`,
`sorry`-free, `#print axioms` reporting only `propext`, `Classical.choice`, `Quot.sound`).

The comparison is stated between the 2-category `Cwa.LcccCat` of locally cartesian closed
categories and the 2-category `Cwa.LcccModelCat` of the models they present: the full
sub-2-category of `Cwa.LaxCModel` spanned by the strictifications, so that its 1-cells are *all*
morphisms of models between them and its 2-cells all lax 2-cells.

* **`Cwa.lcccStrictification : Pseudofunctor LcccCat LcccModelCat`** — strictification,
  corestricted to that sub-2-category; its data is that of `Cwa.lcccPseudofunctor`.
* **`Cwa.lcccCtx : Pseudofunctor LcccModelCat LcccCat`** — the pseudofunctor back.  A model goes
  to its category of contexts, a morphism of models to its functor on contexts — which preserves
  pullbacks, by `Cwa.Mor.preservesLimitsOfShape_fnc`, so it *is* a 1-cell of `LcccCat`
  (`Cwa.ctxFnc`, `Cwa.ctxMap`) — and a lax 2-cell to its natural transformation
  (`Cwa.ctxMap₂`).  It is strict: `Cwa.ctxMap_id` and `Cwa.ctxMap_comp` hold on the nose, so it is
  built as a `StrictPseudofunctor` (`Cwa.lcccCtxStrict`).
* **`Cwa.lcccCtx_map_lcccStrictification_map`** — one round trip is the identity on the nose, on
  1-cells and (`Cwa.lcccCtx_map₂_lcccStrictification_map₂`) on 2-cells.
* **`Cwa.lcccStrictificationMapCtxMapIso`** — the other round trip is the identity up to a
  canonical invertible 2-cell, and no better: strictification is not full on the nose
  (`Cwa.not_full_strictification`).
* `Cwa.IsBiequivalence` — a pseudofunctor is a biequivalence when it is a local equivalence and
  every object of the target is bicategorically equivalent to one in its image.
* **`Cwa.lcccStrictification_isBiequivalence`**, **`Cwa.lcccCtx_isBiequivalence`** and
  **`Cwa.lcccModelCat_biequivalent`** — both pseudofunctors are biequivalences.  Local
  fully faithfulness and local essential surjectivity are proved for both directions
  (`Cwa.lcccCtx_mapFunctor_isEquivalence`, `Cwa.lcccStrictification_mapFunctor_isEquivalence`);
  on objects the two are mutually inverse on the nose.

What this does *not* do, and what `M10-CWA-DEMOCRATIC` records instead, is describe the objects of
`Cwa.LcccModelCat` intrinsically — as the full and democratic models of the dependent product —
rather than as the strictifications of locally cartesian closed categories.
