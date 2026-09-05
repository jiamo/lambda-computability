# M10-CWA-LAX-RIGID

**Status:** DONE_STRONG

Module `Start/CwaLaxRigid.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warning; `#print axioms` on
the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

## What was believed, and what is true

`M10-CWA-LAX-TWOCELL` introduced the lax 2-cells: a natural transformation `n` of the functors on
contexts together with, for every type `A` over `Γ`, a *comparison* map over the base
`cmp Γ A : S.ext (F Γ) (F A) ⟶ S.ext (F Γ) ((G A)[n Γ])`.  It was recorded there, and repeated in
`Start/CwaLaxWhisker.lean`, that this datum is a genuine extra choice and that nothing forces it to
be natural in another 2-cell — from which it was concluded that the interchange law could not even
be stated, and that no bicategory could be built without first enlarging the definition.

That conclusion was wrong.  The comparison is not extra data at all: **it is uniquely determined by
the natural transformation.**

## The argument

The target of a comparison is an extended context of the target model, and in a coherent model the
extension square is a pullback (`Cwa.ExtCoherent`, `S.isPullback`).  A map into it is therefore
determined by its two projections, and both projections of `cmp Γ A` are prescribed by the two
laws a lax 2-cell must satisfy:

* `Cwa.LaxTwoCell.cmp_disp` (the comparison lies over the base) prescribes the composite with the
  display map;
* `Cwa.LaxTwoCell.extend_app` prescribes the composite with the other leg.

* `Cwa.LaxTwoCell.cmp_extend` — the two composites, packaged;
* **`Cwa.LaxTwoCell.cmp_eq`** — the comparison is the map into the pullback determined by them;
* **`Cwa.LaxTwoCell.ext_of_nat`** — hence two lax 2-cells with the same natural transformation are
  equal.

Conversely every natural transformation carries a comparison:

* `Cwa.nat_disp_square` — the square that the pullback property is applied to;
* **`Cwa.LaxTwoCell.ofNat`** — the lax 2-cell attached to a natural transformation, with
  `ofNat_nat` and `ofNat_self`.

## The classification

* **`Cwa.LaxTwoCell.equivNatTrans`** — `LaxTwoCell F G ≃ (F.fnc ⟶ G.fnc)`: a lax 2-cell between
  two morphisms of models *is* a natural transformation of the underlying functors on contexts;
* `Cwa.LaxTwoCell.nonempty_iff_nonempty_natTrans`,
  `Cwa.LaxTwoCell.subsingleton_iff_subsingleton_natTrans` — existence and uniqueness of lax 2-cells
  are existence and uniqueness of natural transformations.

## Consequences

The definition of a lax 2-cell did **not** have to be extended.  The interchange law is provable in
full generality (`M10-CWA-LAX-INTERCHANGE`), the bicategory of models with lax 2-cells exists
(`M10-CWA-LAX-BICAT`), and bi-initiality in it becomes a question about functors on contexts alone
(`M10-CWA-LAX-BIINITIAL`).

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxRigid
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

None.  The classification is an equivalence, stated for arbitrary morphisms of models into a
coherent model.
