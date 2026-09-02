# M10-ASSEMBLY-REGULAR

**Status:** DONE_STRONG

`Start/AssemblyRegular.lean` — the strong epimorphisms of `Asm(A)` are the morphisms that lift
realizers, and they are stable under pullback: `Asm(A)` is a regular category.

## What is proved

* `Realizability.Assembly.LiftsRealizers` — a morphism **lifts realizers** when a single element
  of the algebra turns a realizer of a point of the codomain into a realizer of one of its
  preimages; such a morphism is surjective (`LiftsRealizers.surjective`).
* `Realizability.Assembly.imageInclInv`, `.isIso_imageIncl_of_liftsRealizers`,
  `.strongEpi_of_liftsRealizers` — a lifting combinator tracks a section of the second factor of
  the image factorization, so that factor is invertible and the morphism is the first factor up to
  isomorphism, hence a strong epimorphism.
* `Realizability.Assembly.liftsRealizers_of_strongEpi` — conversely, a strong epimorphism lifts
  against the monomorphism `imageIncl f`, and the tracker of the diagonal is a lifting combinator.
* `Realizability.Assembly.strongEpi_iff_liftsRealizers` — **the strong epimorphisms are exactly
  the morphisms that lift realizers**.
* `Realizability.Assembly.pbAsm`, `.pbFst`, `.pbSnd`, `.pbIsLimit`, `.isPullback_pbAsm` — the
  explicit pullback: the sub-assembly of the product on which the two morphisms agree.
* `Realizability.Assembly.exists_pairWith`, `.liftsRealizers_pbSnd`, `.strongEpi_pbSnd` — the
  lifting combinator is transported to the pullback: from a realizer `c` of a point `z` of the
  base, the tracker of `g` gives a realizer of `g z`, the lifting combinator of `f` turns it into
  a realizer of a preimage `x`, and `λc. pair (r (t c)) c` pairs the two to realize `(x, z)`.
* `Realizability.Assembly.strongEpi_of_isPullback` — **strong epimorphisms of assemblies are
  stable under pullback** (for an arbitrary pullback square, by comparison with the explicit one).
  With the finite limits of `Start/AssemblyLimits.lean` and the image factorizations of
  `Start/AssemblyImage.lean`, this is regularity of `Asm(A)`.

## Scope

No hypothesis on the algebra.  Regularity is recorded as the conjunction of its three ingredients
(finite limits, strong epi-mono factorizations, pullback stability of strong epis), not as an
instance of a single mathlib typeclass.

## Gates

```
lake build Start.AssemblyRegular    # no error, no warning
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```

`#print axioms` on the headline results reports only `propext`, `Classical.choice` and
`Quot.sound`.  The module contains no `sorry` and no `axiom`, and is registered in
`Start/Capstones.lean`.
