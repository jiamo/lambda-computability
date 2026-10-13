# M28-STARHEIGHT-TWO — generalized star height at most two (open)

## Status

`GeneralizedStarHeight.main_two` is **not proved**. No declaration of that name exists in the
library, and no weaker statement carries the name. The definitions in
`Start/StarHeightModel.lean` are unchanged. No negative result was proved.

## What is available

* `main_two_of_singleSplit` (`Start/StarHeightSingleSplit.lean`): `main_two` follows from
  `SingleSplit T` for every morphism `T` into a finite monoid.
* `singleSplit_of_comm` (`Start/StarHeightCommutative.lean`): `SingleSplit T` holds for every
  finite commutative monoid. `singleSplit_of_fiber_height` gives it whenever all fibers of
  `T` already have height one, which is circular for the general case.

## Routes considered

* **Route 1 (merge the two upstream splits).** The outer tests
  (`OuterStream.prefixLanguage`, `OuterStream.suffixLanguage`) are sound on all complete
  episodes but available only off `failedDomain`; the inner tests (`InnerStream`) are sound
  and available on `failedDomain` only, over a different state space (`V × K` instead of `V`).
  Taking the union of the two test families on the state space `V ⊕ (V × K)` is not sound: a
  prefix accepted by an outer test can pair with a suffix accepted by an inner test on an
  episode outside `failedDomain`. Making the tests certify their mode from their own side (in
  the manner of the end guard of section 6.3) requires a mode guard of height ≤ 1 that decides
  membership in `failedDomain` from inside a prefix and from inside a suffix independently. I
  did not find such a guard, and could not write the route as a list of Lean lemma statements
  whose proofs I could see.
* **Route 2 (generalized split identity).** A variant of `split_identity` whose middle factor
  is intersected with a boundary constraint, or whose tests read into neighbouring episodes,
  is plausible as algebra, but each variant still needs tests available on every episode of
  `E`, which is the same missing ingredient.

## Stop rule: first missing lemma

Under the stop rule I stopped with no route written as Lean lemma statements. The first
missing lemma is:

```lean
theorem GeneralizedStarHeight.singleSplit_of_finite {Alphabet : Type u} [Finite Alphabet]
    [Nonempty Alphabet] (M : Type) [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) : SingleSplit T
```

With it, `main_two` is `main_two_of_singleSplit` (the empty alphabet being handled separately
there). For route 1 specifically, the missing piece within it is availability of a sound
height-one test family on the failed episodes:

```lean
-- with A := S.parameters g L hB, E := L.endRule.complete L.lag, as in outer_graph_height
∃ (S' : Type) (_ : Fintype S') (G' : List Alphabet → S' → S') (P' Q' : S' → Language Alphabet),
  SplitSound E G' P' Q' ∧ SplitAvailable E 0 G' P' Q' ∧
  (∀ x, HasHeightAtMost (P' x) 1) ∧ (∀ y, HasHeightAtMost (Q' y) 1) ∧
  ∀ x y, ∃ R, graph E (OuterStream.wordUpdate A clock T ρ β L.lag) x y =
    ⨆ r ∈ R, graph E G' r.1 r.2.1 ⊓ graph E G' r.2.2.1 r.2.2.2
```

## Literature

The upstream paper ("Generalized Star Height at Most Three") states that it does not decide
whether height one always suffices; two is not known. The question remains open here.
