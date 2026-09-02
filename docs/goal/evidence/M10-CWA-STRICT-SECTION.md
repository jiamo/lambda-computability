# M10-CWA-STRICT-SECTION

**Status:** DONE_STRONG

`Start/CwaStrictSection.lean` — the category of contexts of a model, and the fact that
strictification is a strict section of it.

## What is proved

* `Cwa.Model.ctx : Cwa.Model ⥤ Cat` — the category of contexts of a model, functorially; the
  underlying functor of a morphism of models is its action on contexts.
* `Cwa.PbCat.toCat : Cwa.PbCat ⥤ Cat` — the underlying category of a category with pullbacks.
* `Cwa.strictification_comp_ctx : strictification ⋙ Model.ctx = PbCat.toCat` — **on the nose**,
  not merely up to isomorphism: presenting a category with pullbacks as a model of a dependent
  type theory does not disturb the contexts, and `Cwa.strictification_map_fnc` records the same
  for morphisms.
* `Cwa.strictification_faithful` — a pullback-preserving functor is determined by the morphism of
  models it induces.
* `Cwa.strictification_reflects_iso` — **strictification reflects isomorphisms**.  If the induced
  morphism of models is invertible, the underlying functor of its inverse
  (`Cwa.invFnc`) is a strict two-sided inverse of the given functor
  (`Cwa.fnc_comp_invFnc`, `Cwa.invFnc_comp_fnc`), hence one half of an equivalence
  (`Cwa.strictEquiv`), hence preserves pullbacks; so the given functor was already an isomorphism
  in `Cwa.PbCat` (`Cwa.isIso_of_isIso_strictification_map`).

Together with `M10-CWA-STRICT-FUNCTOR` this makes the 1-dimensional comparison between categories
with pullbacks and models of a dependent type theory as tight as it can be: strictification is a
faithful, isomorphism-reflecting section.

## Gates

```
lake build Start.CwaStrictSection   # no error, no warning
python3 scripts/check_closure.py    # OK: 333 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

The module contains no `sorry` and no `axiom`, and is registered in `Start/Capstones.lean`.
