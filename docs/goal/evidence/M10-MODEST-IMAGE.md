# M10-MODEST-IMAGE

**Status:** DONE_STRONG

`Start/ModestImage.lean` — the image of a modest assembly is modest, so the modest assemblies have
images and are a regular category.

## What is proved

* `Realizability.Assembly.Modest.image` — **the image of a modest assembly is modest**: a realizer
  of a point of the image realizes one of its preimages, and modesty of the domain determines that
  preimage.
* `Realizability.Assembly.Modest.pb` — the explicit pullback of two morphisms of modest assemblies
  is modest, being a sub-assembly of a product of modest assemblies.
* `Realizability.Modest.injective_of_mono` — a monomorphism of modest assemblies is injective, by
  testing it against the global elements.
* `Realizability.Modest.imageModest`, `.imageFactorModest`, `.imageInclModest`,
  `.imageFactorModest_comp`, `.hasLiftingProperty_imageFactorModest`,
  `.strongEpi_imageFactorModest` — the image factorization inside the full subcategory; the
  diagonal filler of `Start/AssemblyImage.lean` is again a morphism of modest assemblies.
* `Realizability.Modest.instHasStrongEpiMonoFactorisations`, `.instHasImages` — **the modest
  assemblies have images**.
* `Realizability.Modest.strongEpi_iff_liftsRealizers` — the strong epimorphisms of the subcategory
  are again exactly the morphisms that lift realizers.
* `Realizability.Modest.pbModest`, `.pbFstModest`, `.pbSndModest`, `.pbModestIsLimit`,
  `.isPullback_pbModest`, `.strongEpi_pbSndModest`, `.strongEpi_of_isPullback` — pullbacks are
  computed as in `Asm(A)` and **strong epimorphisms are stable under pullback**, so with the
  finite limits of `M10-MODEST-COLIMITS` the modest assemblies are a regular category.

## Scope

No hypothesis on the algebra.  Regularity is recorded as the conjunction of its three ingredients
(finite limits, strong epi-mono factorizations, pullback stability of strong epis).

## Gates

```
lake build Start.ModestImage        # no error, no warning
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
