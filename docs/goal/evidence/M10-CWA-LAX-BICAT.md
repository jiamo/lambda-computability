# M10-CWA-LAX-BICAT

**Status:** DONE_STRONG

Modules `Start/CwaLaxBicat.lean`, `Start/PbCatBicat.lean` and `Start/CwaStrictLaxWhisker.lean`, all
imported by `Start.lean` and registered in `Start/Capstones.lean`.  They build without `sorry` and
without linter warning; `#print axioms` on the headline declarations reports only `propext`,
`Classical.choice`, `Quot.sound`.

## The bicategory of models with lax 2-cells

`M10-CWA-LAX-CATEGORY` gave the hom-categories and `M10-CWA-LAX-WHISKER` the whiskerings;
`M10-CWA-LAX-INTERCHANGE` supplied the law that connects them.  What was missing for a mathlib
`Bicategory` is therefore only the packaging, and it is done here.

* `Cwa.LaxCModel` — a coherent model, as an object of the lax 2-category; a one-field wrapper of
  `Cwa.CModel` so that the lax structure does not clash with the strict one of
  `M10-CWA-BICATEGORY` (`Cwa.LaxCModel.of`);
* `Cwa.LaxCModel.laxCategoryStruct`, `Cwa.LaxCModel.laxHomCategory` — the 1-cells and the
  hom-categories, kept as `def`s so that both instance paths stay under control;
* the primed section (`whiskerLeft_id'`, `whiskerLeft_comp'`, `id_whiskerLeft'`,
  `comp_whiskerLeft'`, `id_whiskerRight'`, `comp_whiskerRight'`, `whiskerRight_id'`,
  `whiskerRight_comp'`, `whisker_assoc'`, `pentagon'`, `triangle'`) — the bicategory axioms, each
  proved by `Cwa.LaxTwoCell.ext_of_nat` from the corresponding identity of natural transformations;
* **`Cwa.LaxCModel.instBicategory`** — the bicategory, and **`Cwa.LaxCModel.instStrict`**: it is
  strict, the associator and unitors being identities;
* `Cwa.LaxCModel.hom_ext`, `Cwa.LaxCModel.homEquivNatTrans`, `Cwa.LaxCModel.isIso_of_isIso_nat` —
  a 2-cell of the bicategory is determined by its natural transformation, the hom-sets of 2-cells
  are the natural transformations, and a 2-cell is invertible as soon as its natural transformation
  is.

## The 2-category of categories with pullbacks

The source of strictification also has to be a bicategory for the comparison to be stated:

* `Cwa.PbCat.homCategory`, `Cwa.PbCat.twoCell_ext` — the hom-categories are the functor categories
  cut down to the pullback-preserving functors;
* **`Cwa.PbCat.instBicategory`**, `Cwa.PbCat.instStrict` — a strict bicategory, with
  `bicategoryWhiskerLeft_eq` and its companions identifying its whiskerings with the ordinary
  whiskerings of natural transformations.

## Strictification and whiskering

* `Cwa.laxEqToHom`, `Cwa.laxEqToHom_nat`, `Cwa.morOfPreservesPullbacks_fnc`,
  `Cwa.laxTwoCellOfNatTrans_eq_ofNat` — the transports needed to compare the two sides;
* **`Cwa.laxTwoCellOfNatTrans_whiskerLeft`, `Cwa.laxTwoCellOfNatTrans_whiskerRight`** —
  strictification carries whiskering of natural transformations to whiskering of lax 2-cells, on
  either side, up to the transports along its strict preservation of composition of 1-cells.
  Together with the compatibility with identities and vertical composition already known from
  `M10-CWA-LAX-TWOCELL`, this is 2-functoriality of strictification in both dimensions.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxBicat Start.PbCatBicat Start.CwaStrictLaxWhisker
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

None for the statements above.  What is *not* done here — and is the remaining open boundary of
`M9-LAMBDAPI-LCCC` and `M10-CWA-BICATEGORY` — is packaging strictification as a mathlib
`Pseudofunctor` between these two bicategories, and the biequivalence with locally cartesian
closed categories.  An attempt at the `Pseudofunctor` was made and abandoned: the compatibility
lemmas above are exactly its data, but the coherence axioms are equations between 2-cells whose
1-cells appear only under projection chains, so the rewriting needed to reduce them to the
identities of natural transformations does not fire.  The concrete whiskering theorems are the
deliverable instead.
