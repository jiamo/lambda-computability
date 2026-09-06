# M11-APPLICATIVE-MORPHISM

**Status:** DONE_STRONG

With both Kleene algebras available, `Start/PCAMorphism.lean` adds the morphisms of Longley's
programme and the comparison between the two poles.  The module is imported from `Start.lean`,
registered in `Start/Capstones.lean`, free of `sorry` and of linter warnings, and its results
depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Applicative morphisms (first exit criterion)

* `Realizability.AppMorphism` — a total relation `map` assigning to each element of `A` a
  nonempty set of representatives in `B`, and one element `realizer` of `B` such that
  `realizer · b · b'` represents `a · a'` whenever `b` represents `a`, `b'` represents `a'` and
  `a · a'` is defined.

## The identity morphism (second exit criterion)

* `Realizability.AppMorphism.id` — realized by `λ x y. x y`, obtained from the combinatory
  completeness of `Start/PCA.lean` (`PCA.lam2`, `lam2_app_app`, `lam2_app_dom`);
* `Realizability.AppMorphism.comp` — the composite of two applicative morphisms, realized by
  `λ x y. t (t e x) y` for `t` the realizer of the second morphism and `e` a representative of
  the realizer of the first.

## From `K₁` to `K₂` (third exit criterion)

* `Realizability.KleeneTwo.natEl` — the constant function with value `n`, the representative
  of `n`;
* `Realizability.KleeneTwo.evalVal`, `evalEl`, `evalStage`, `evalAssoc` — the operation that
  reads its two arguments at `0` and runs the first, as a partial recursive code, on the second,
  and the canonical associates that realize it, with `cont_evalEl` and `cont_evalStage` the
  continuity these associates need;
* `Realizability.KleeneTwo.evalAssoc_app` — the realizer computes Turing application on the
  constant functions;
* `Realizability.KleeneTwo.kOneToTwo` — the applicative morphism `K₁ → K₂`.

## Scope

The 2-categorical structure — the preorder on applicative morphisms and the identity and
associativity laws up to it — is not part of this task; the identity morphism, composition, and
the comparison `K₁ → K₂` are.
