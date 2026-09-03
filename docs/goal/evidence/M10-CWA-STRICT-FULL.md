# M10-CWA-STRICT-FULL

**Status:** DONE_STRONG

`Start/CwaStrictFull.lean` — how far `Cwa.strictification : PbCat ⥤ Cwa.Model` is from being an
equivalence onto its image, in the 1-categorical direction.

`Start/CwaStrictSection.lean` had proved strictification faithful and conservative (it reflects
isomorphisms).  The remaining question is fullness: is every morphism of models between two
strictified categories induced by a pullback-preserving functor?  This module answers it in two
halves, and the answer is not the naive one.

## The functor part is always induced

* `Cwa.subExtIso`, `Cwa.subExtIso_hom_extend`, `Cwa.subExtIso_hom_disp` — the comparison
  isomorphism of a substituted extended context, with the identification of the substituted type
  folded in.
* `Cwa.isPullback_map_extend` — the image of an extension square of a local universe under a
  morphism of strictified models is a pullback: the comparison isomorphisms identify it with the
  extension square of the image type, which is a pullback in the target.
* `Cwa.Mor.map_isPullback` — **the functor on contexts of an arbitrary morphism of strictified
  models preserves pullbacks**, with no hypothesis at all.  Every pullback square is isomorphic to
  an extension square, because a morphism `p : Y ⟶ Γ` is presented by the local universe
  `LuTy.ofHom p` (`LuTy.isoExtOfHom`), and extension squares are carried to pullbacks.
* `Cwa.Mor.preservesLimitCospan`, `Cwa.Mor.preservesLimitsOfShape_fnc` — the same statement as a
  `PreservesLimitsOfShape WalkingCospan`.
* `Cwa.exists_pbCatHom_fnc` — hence **strictification is full on the underlying functors**: every
  morphism `strictification.obj X ⟶ strictification.obj Y` has its functor on contexts in the
  image of `PbCat.Hom`.

## The action on types need not be the induced one

What a morphism of models is free to choose is the *presentation* of a type: a type of a
strictified model is a whole local universe, and only the slice object it presents is determined.

* `Cwa.tyMapCompareIso`, `Cwa.tyMapCompareIso_hom_disp` — the type assigned by a morphism of
  strictified models is canonically isomorphic, **over the base context**, to the transported one.
* `Cwa.Chaotic`, `Cwa.Chaotic.instCategory`, `Cwa.Chaotic.instHasLimitsOfShape` — the indiscrete
  category on two objects: every hom-set is a singleton, so every diagram has a limit and in
  particular it has pullbacks.
* `Cwa.chaoticSwapMor` — a morphism of the strictified model of that category to itself, over the
  **identity** functor, which presents every type by the *other* object of the category.  All the
  laws hold because every hom-set is a singleton.
* `Cwa.not_full_strictification` — **strictification is not full.**  A preimage of
  `chaoticSwapMor` would have the identity as its underlying functor, hence would assign the
  transported presentation, whose total space is the same object, not the swapped one.

## What this settles

The honest 1-categorical statement about strictification is the conjunction: it is faithful, it
reflects isomorphisms, it is full on the underlying functors, and it is full up to a canonical
isomorphism of presentations — but not full on the nose.  So any equivalence between models of a
dependent type theory and categories with pullbacks (and, further out, locally cartesian closed
categories) has to be stated up to isomorphism of types.  This matches, in the 1-dimensional
direction, the negative result of `Start/CwaStrictRigid.lean` in the 2-dimensional one: with the
strict morphisms and the 2-cells of `Start/CwaTwoCell.lean`, no strictification 2-functor exists
either.

## Gates

```
lake build Start.CwaStrictFull      # no error, no warning
python3 scripts/check_closure.py    # OK: 344 modules, all in the import closure and all registered
python3 scripts/goal_state.py validate
```

The module contains no `sorry` and no `axiom`; `#print axioms` on `Cwa.Mor.map_isPullback`,
`Cwa.exists_pbCatHom_fnc`, `Cwa.tyMapCompareIso_hom_disp` and `Cwa.not_full_strictification`
reports only `propext`, `Classical.choice` and `Quot.sound`.  It is registered in
`Start/Capstones.lean`.
