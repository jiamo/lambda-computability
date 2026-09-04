# M10-CWA-LAX-WHISKER

**Status:** DONE_STRONG

Module `Start/CwaLaxWhisker.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warning; `#print axioms` on
the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

`M10-CWA-LAX-CATEGORY` proved that the lax 2-cells give the morphisms of models hom-categories.
This task adds the horizontal direction: whiskering by a morphism of models.

## The image of a map over the base

Whiskering on the right has to push the comparison of a lax 2-cell through a morphism of models
`H`, so it needs a calculus for the image of a map of extended contexts over the base.

* `Cwa.morOver` — the image `(H.extIso A).inv ≫ H.fnc.map u ≫ (H.extIso B).hom` of such a map,
  and `Cwa.morOver_disp`: it again lies over the base;
* `Cwa.morOver_id`, `Cwa.morOver_comp`, `Cwa.morOver_eqToHom` — the image is functorial and
  carries transports to transports;
* **`Cwa.morMap_subOver`, `Cwa.morOver_subOver`** — a morphism of models carries the substituted
  map of extended contexts to the substituted map of the image, up to the transports identifying
  the image of a substituted type.  This is the compatibility that makes right whiskering
  functorial.

## Whiskering

* **`Cwa.LaxTwoCell.whiskerLeft`** — whiskering by `F` on the left; the comparison at `A` is the
  comparison of the 2-cell at `F.tyMap A`;
* **`Cwa.LaxTwoCell.whiskerRight`** — whiskering by `H` on the right; the comparison is the image
  of the comparison, corrected by the transport along `H.tyMap_sub`;
* `Cwa.LaxTwoCell.whiskerLeft_nat`, `Cwa.LaxTwoCell.whiskerRight_nat`,
  `Cwa.LaxTwoCell.whiskerRight_cmp` — their underlying data;
* **`Cwa.LaxTwoCell.whiskerLeft_id`, `Cwa.LaxTwoCell.whiskerLeft_vcomp`,
  `Cwa.LaxTwoCell.whiskerRight_id`, `Cwa.LaxTwoCell.whiskerRight_vcomp`** — both whiskerings
  preserve the identity lax 2-cell and vertical composition, so each is a functor between the
  hom-categories of `M10-CWA-LAX-CATEGORY`.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxWhisker
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

The interchange law is **not** claimed, and is not expected to hold on the nose: for lax 2-cells
it would ask the comparison of one 2-cell to be natural in the component of the other, which is
not part of the data of a lax 2-cell.  Consequently no bicategory of models with lax 2-cells is
assembled here; what is proved is that whiskering on either side is defined and functorial in the
2-cell.
