# M10-ASSEMBLY-IMAGE

**Status:** DONE_STRONG

`Start/AssemblyImage.lean` — monomorphisms, epimorphisms and image factorizations in the category
of assemblies.

## What is proved

* `Realizability.Assembly.mono_iff_injective` — a morphism of assemblies is a monomorphism exactly
  when it is injective; the non-trivial direction tests it against the global elements
  (`Assembly.pointMap`).
* `Realizability.Assembly.epi_iff_surjective` — a morphism is an epimorphism exactly when it is
  surjective; the non-trivial direction compares the characteristic map of the set-theoretic image
  with the constantly true map into the assembly of propositions, which is legitimate because that
  assembly has no computational content.
* `Realizability.Assembly.imageAsm`, `.imageFactor`, `.imageIncl`,
  `.imageFactor_comp_imageIncl` — the **image factorization**: the carrier is the set-theoretic
  image, and `a` realizes a point when it realizes one of its preimages, so the first factor is
  the identity on realizers and the second is tracked by any tracker of the original morphism.
  This is *not* the sub-assembly of the codomain on the image set.
* `Realizability.Assembly.imageDiagonal`, `.imageDiagonal_comp`,
  `.imageFactor_comp_imageDiagonal`, `.hasLiftingProperty_imageFactor` — the diagonal filler of a
  square from the first factor to a monomorphism: a point of the image is sent to the value of the
  top map at any of its preimages, well defined because the right-hand map is injective, and
  tracked by the tracker of the top map.
* `Realizability.Assembly.strongEpi_imageFactor` — **the first factor is a strong epimorphism**.
* `Realizability.Assembly.instHasStrongEpiMonoFactorisations`, `.instHasImages` — **the assemblies
  have strong epi-mono factorizations, hence images** in mathlib's sense.

## Scope

No hypothesis on the algebra.  Nothing is claimed here about pullback stability of strong
epimorphisms, i.e. about `Asm(A)` being a regular category, nor about which epimorphisms are
strong.

## Gates

```
lake build Start.AssemblyImage      # no error, no warning
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
