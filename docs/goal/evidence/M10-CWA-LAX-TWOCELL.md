# M10-CWA-LAX-TWOCELL

**Status:** DONE_STRONG

Modules `Start/CwaLaxTwoCell.lean` and `Start/CwaStrictLax.lean`, both imported by `Start.lean` and
registered in `Start/Capstones.lean`.  They build without `sorry` and without linter warning;
`#print axioms` on the headline declarations reports only `propext`, `Classical.choice`,
`Quot.sound`.

`M10-CWA-STRICT-RIGID` settled negatively the 2-dimensional half of the comparison between
categories with pullbacks and models of a dependent type theory: with the strict 2-cells of
`Start/CwaTwoCell.lean` the strictification cannot be made 2-functorial at all, since
`Cwa.isEmpty_twoCell_id_coyoneda` exhibits a natural transformation of pullback-preserving
endofunctors of `Type` inducing no 2-cell whatsoever.  Its conclusion was that any pseudofunctor
must weaken either the morphisms or the 2-cells.  This task carries out the second weakening and
shows it suffices.

## Lax 2-cells

A **lax 2-cell** keeps the natural transformation of the functors on contexts but replaces the
equality `S.tySub (nat.app Γ) (G.tyMap A) = F.tyMap A` by a *map over the base* between the
extended contexts, subject to the same coherence law.

* `Cwa.subOver` — a map of extended contexts over a context is substituted along a morphism, by
  the universal property of the extension square, with its two defining equations
  (`Cwa.subOver_extend`, `Cwa.subOver_disp`);
* `Cwa.LaxTwoCell` — the structure, and `Cwa.LaxTwoCell.ext_of_nat_eq` its extensionality;
* `Cwa.TwoCell.toLax` — **every strict 2-cell is lax**, its comparison being the transport along
  the equality of types;
* `Cwa.LaxTwoCell.id`, `Cwa.LaxTwoCell.vcomp` — identities and vertical composition; the composite
  comparison is the first comparison followed by the second one substituted along the first
  component, which is where `Cwa.subOver` is needed.

## Strictification is 2-functorial for them

* `Cwa.luCmp` — the comparison attached to a natural transformation `τ : F ⟶ G` of
  pullback-preserving functors: the identity on the base and `τ` on the total space of the local
  universe; it exists exactly because `τ` is natural at the projection and at the classifying map;
* `Cwa.luCmp_gen`, `Cwa.luCmp_disp` — its two defining equations;
* **`Cwa.laxTwoCellOfNatTrans`** — a natural transformation of pullback-preserving functors induces
  a lax 2-cell between the morphisms of models they induce;
* `Cwa.luCmp_id`, `Cwa.luCmp_comp` — the comparison of an identity is the transport, and the
  comparison of a composite is the composite of the comparisons;
* **`Cwa.laxTwoCellOfNatTrans_id`, `Cwa.laxTwoCellOfNatTrans_comp`** — hence the passage is
  functorial on 2-cells: strictification is 2-functorial once the 2-cells are taken lax;
* **`Cwa.nonempty_laxTwoCell_id_coyoneda`** — in particular the natural transformation of
  `M10-CWA-STRICT-RIGID`, which admits no strict 2-cell, does induce a lax one.

## Gates

```
python3 scripts/goal_state.py validate
python3 scripts/check_closure.py
lake build Start.CwaLaxTwoCell Start.CwaStrictLax
lake build
```

all pass; the full `lake build` reports no error and no linter warning.

## Boundary

What is proved is 2-functoriality of strictification for the lax 2-cells, not a biequivalence with
locally cartesian closed categories: the lax 2-cells are not asked to be invertible, no
horizontal composition or bicategory structure is built for them, and the comparison on types is
still only full up to isomorphism of presentations (`M10-CWA-STRICT-FULL`).
