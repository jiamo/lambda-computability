# M10-CWA-LAX-CATEGORY

**Status:** DONE_STRONG

Module `Start/CwaLaxCategory.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warning; `#print axioms` on
the headline declarations reports only `propext`, `Classical.choice`, `Quot.sound`.

`M10-CWA-LAX-TWOCELL` introduced the lax 2-cells — a natural transformation of the functors on
contexts together with a comparison of the extended contexts *over the base*, in place of the
equality of types a strict 2-cell demands — with an identity and a vertical composite, and proved
that strictification is 2-functorial for them.  It did not check that the vertical structure
obeys the laws of a category.  This task does.

## The calculus of the substituted map

Vertical composition of lax 2-cells substitutes the second comparison along the first component,
so the laws are equations about `Cwa.subOver`.

* `Cwa.subOver_id`, `Cwa.subOver_comp` — the substituted map of an identity is the identity and
  the substituted map of a composite is the composite of the substituted maps;
* `Cwa.subOver_eqToHom`, `Cwa.subOver_congr` — a transport is carried to a transport, and the
  substituted map depends only on the map;
* `Cwa.subOver_id_sub`, `Cwa.subOver_eq_of_eq_id` — substituting along the identity acts by the
  transports along `tySub_id`;
* `Cwa.subOver_subOver`, `Cwa.subOver_eq_of_eq_comp` — substituting along a composite is
  substituting twice, up to the transports along `tySub_comp`.  This is the lax replacement of
  `Cwa.substCompare_comp`, and like it, it needs the coherence law `Cwa.ExtCoherent`.

## The category of lax 2-cells

* `Cwa.LaxTwoCell.ext_of_cmp` — a lax 2-cell is determined by its natural transformation and its
  comparison, the latter compared after the transport along the equality of the two natural
  transformations;
* `Cwa.LaxTwoCell.vcomp_cmp`, `Cwa.LaxTwoCell.id_cmp` — the comparisons of the vertical composite
  and of the identity;
* **`Cwa.LaxTwoCell.id_vcomp`, `Cwa.LaxTwoCell.vcomp_id`, `Cwa.LaxTwoCell.vcomp_assoc`** —
  vertical composition is unital and associative;
* **`Cwa.laxMorCategory`** — hence the morphisms `T ⟶ S` of categories with attributes and the lax
  2-cells between them form a category.

## The strict 2-cells sit inside the lax ones

* `Cwa.TwoCell.toLax_cmp`, `Cwa.TwoCell.toLax_id`, `Cwa.TwoCell.toLax_vcomp` — the passage from a
  strict 2-cell to a lax one preserves identities and vertical composition;
* **`Cwa.laxInclusion`** — hence it is a functor from the hom-category of strict 2-cells
  (`Cwa.morCategory`) to the hom-category of lax ones;
* **`Cwa.TwoCell.toLax_injective`** — and it is injective, so a strict 2-cell is determined by the
  lax 2-cell it becomes.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxCategory
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

Only the vertical structure is built.  Horizontal composition of lax 2-cells (whiskering by a
morphism of models) and the interchange law are not defined, so no bicategory of models with lax
2-cells is assembled; the lax 2-cells are not asked to be invertible; and, as for the strict ones,
the comparison with locally cartesian closed categories remains only up to isomorphism of
presentations (`M10-CWA-STRICT-FULL`).
