# M11-KLEENE-NO-RETRACTION

**Status:** DONE_STRONG

`Start/PCAMorphism.lean` builds the applicative morphism `Realizability.KleeneTwo.kOneToTwo` from
Kleene's first algebra to Kleene's second.  `Start/KleeneNoRetraction.lean` shows the inclusion
cannot be reversed — and first corrects the naive statement.

## The unqualified statement is false (first exit criterion)

`Realizability.AppMorphism.trivialMor` is an applicative morphism between *any* two partial
combinatory algebras: every element of the target represents every element of the source, and
the realizer is the constant `λ x y. k`, which is always defined.  So
`Realizability.KleeneTwo.nonempty_appMorphism_kleeneTwo_kleeneOne` — morphisms `K₂ → K₁` exist,
and a theorem has to assume that the target reads something back.

## The projections (second exit criterion)

`Realizability.KleeneTwo.projEl n` is the operation `β ↦ (the constant function β n)`; it is
continuous (`cont_projEl`), so its canonical associate `projAssoc n` is an element of `K₂` with
`appK (projAssoc n) β = Part.some (natEl (β n))` (`appK_projAssoc`).

## The hypothesis, and the theorem (exit criteria three to five)

* `Realizability.KleeneTwo.SeparatesBits` — one partial recursive code recovers `b` from every
  representative of the constant function `b`, for `b ≤ 1`;
  `Realizability.KleeneTwo.ReadsNumerals` — the same for every numeral, which is stronger;
* `Realizability.KleeneTwo.exists_map_natEl` — from a representative `m` of `β` and one of
  `projAssoc n`, the realizer computes a representative of the constant function `β n`, and it is
  unique because the application of `K₁` is a partial *function*;
* `Realizability.KleeneTwo.no_separatesBits_morphism` — hence, for a morphism that separates
  bits, the representative of a `0/1`-valued `β` determines every value of `β`.  The map sending
  a set of naturals to a representative of its characteristic function is therefore injective,
  which `Function.cantor_injective` forbids;
* `Realizability.KleeneTwo.no_readsNumerals_morphism`,
  `Realizability.KleeneTwo.kOneToTwo_not_invertible` — the conclusion in the form the inclusion
  suggests.

The module is imported by `Start.lean`, registered in `Start/Capstones.lean`, builds without
`sorry` and without linter warning; the headline results depend only on `propext`,
`Classical.choice`, `Quot.sound`.
