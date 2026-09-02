# M10-CWA-STRICT-RIGID

**Status:** DONE_STRONG

`Start/CwaStrictRigid.lean` — strictification is rigid in the 2-dimensional direction, so it is
not a 2-functor into the bicategory of models of `Start/CwaBicat.lean`.

## The obstruction

A morphism of categories with attributes acts on types *strictly*, and a type of a strictified
model is a local universe: a whole span `total ⟶ base` of the ambient category, not just a fibre.
A 2-cell must therefore carry the local universe assigned by one morphism to the local universe
assigned by the other, and substitution along the component of the 2-cell touches the classifying
map only.  Applying this to the type presented by an identity map forces the two functors to agree
on objects.

## What is proved

* `Cwa.LuTy.cls_congr` — an equality of local universes identifies the classifying maps, up to the
  transport along the induced equality of bases.
* `Cwa.twoCell_strict_obj_eq` — a 2-cell between two strictified morphisms forces the two functors
  to agree on objects.
* `Cwa.twoCell_strict_nat_app` — its component is inverse to the transport along that equality,
  hence carries no information; `Cwa.twoCell_strict_self_nat` — a 2-cell from a strictified
  morphism to itself is the identity natural transformation.
* `Cwa.subsingleton_twoCell_strict` — there is **at most one** 2-cell between two strictified
  morphisms: the hom-categories of strictified morphisms are discrete.
* `Cwa.coyonedaConst`, `Cwa.emptyPow_obj_ne`, `Cwa.isEmpty_twoCell_id_coyoneda` — the
  2-dimensional structure is genuinely lost.  `emptyPow = coyoneda.obj (op Empty)` is
  representable, hence preserves pullbacks, and there is a natural transformation
  `𝟭 Type ⟶ emptyPow`; but the two functors disagree on objects at `Empty`, so there is **no**
  2-cell whatsoever between the morphisms of models they induce.

Consequently a pseudofunctor from categories with pullbacks to the bicategory of models must
weaken either the morphisms or the 2-cells; with the strict morphisms and the 2-cells of
`Start/CwaTwoCell.lean` no such 2-functor exists.  This is a negative resolution of one half of
the open boundary recorded for `M10-CWA-BICATEGORY`.

## Gates

```
lake build Start.CwaStrictRigid     # no error, no warning
python3 scripts/check_closure.py    # OK: 333 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

The module contains no `sorry` and no `axiom`, and is registered in `Start/Capstones.lean`.
