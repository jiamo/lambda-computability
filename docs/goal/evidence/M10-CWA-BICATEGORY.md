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
