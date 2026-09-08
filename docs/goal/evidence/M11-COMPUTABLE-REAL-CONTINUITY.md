# M11-COMPUTABLE-REAL-CONTINUITY

**Status:** DONE_STRONG

`Start/ComputableReal.lean` runs the standard construction of computable analysis on top of
Kleene's second algebra `K₂` and proves that computability of a real function forces continuity,
with an explicit modulus.  The module is imported by `Start.lean`, registered in
`Start/Capstones.lean`, builds without `sorry` and without linter warning, and
`Realizability.KleeneTwo.IsComputableFun.continuous` depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Names (first exit criterion)

* `Realizability.KleeneTwo.ratOf` — the rational coded by a natural number, through the standard
  denumeration of `ℚ`, with `ratOf_surjective` and `exists_ratOf_near`;
* `Realizability.KleeneTwo.IsName` — error at most `2 ^ (-i)` at stage `i`;
* `Realizability.KleeneTwo.IsFastName`, `exists_fastName` — every real has a name whose error is
  half of what a name must achieve.

## The gluing lemma (second exit criterion)

`Realizability.KleeneTwo.glue_isName`: if `β` is a fast name of `x`, `γ` a name of `y` and
`|y - x| ≤ 2 ^ (-N-1)`, then the sequence following `β` for `N` steps and `γ` afterwards is a name
of `y`.  The spare half of a fast name is exactly the slack this needs.

## Computable real functions (third exit criterion)

`Realizability.KleeneTwo.Realizes` — an element of `K₂` turns every name of `x` into a name of
`f x` — and `Realizability.KleeneTwo.IsComputableFun`.

## Modulus and continuity (fourth exit criterion)

`Realizability.KleeneTwo.Realizes.exists_modulus`: the finite initial segment of the name of `x`
that the computation of the `k`-th output rational reads (Kleene continuity,
`Realizability.KleeneTwo.appK_continuous`) is a modulus, because by the gluing lemma every point
near enough to `x` has a name beginning with that same segment, so the two output names agree at
`k`.  `Realizability.KleeneTwo.IsComputableFun.continuous` follows.

## Both directions of non-vacuity (fifth exit criterion)

`Realizability.KleeneTwo.not_isComputableFun_step` — the step function is not computable, although
each of its values is a computable real; `Realizability.KleeneTwo.isComputableFun_id` and
`isComputableFun_const` — the identity and the constants are, realized by canonical associates.

## Boundary

This is the type-two statement, for functions computed from *names*.  The
Kreisel–Lacombe–Shoenfield theorem — the same statement for Markov computability, where the
function is defined on the computable reals and computed from indices of algorithms — is not
proved and is not claimed; there continuity does not follow from Kleene continuity.  The
partial-function analogue for operations on indices is `Start/EffectiveOperation.lean`
(M11-MYHILL-SHEPHERDSON).
