# M10-CREATIVE-ISO

**Status:** DONE_STRONG

Module `Start/CreativeIso.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/PostCreative.lean` proves Myhill's completeness theorem — a creative set is *many-one*
complete — and `Start/MyhillIso.lean` proves Myhill's isomorphism theorem — *one-one* equivalent
sets are recursively isomorphic.  This task joins the two by upgrading the reduction from many-one
to one-one, which yields the classification of the creative sets.

## What is proved

* The chase (`Lambda.Post.chaseIdx`, `Lambda.Post.prodStep`, `Lambda.Post.prodRun`,
  `Lambda.Post.prodEsc`): to produce an element of a productive set `P` outside a finite list `L`,
  apply the production function `p` to the current index; if the value lies in `L`, adjoin it to
  the current r.e. set (`Lambda.Post.exists_adjoin`) and repeat.
  - `Lambda.Post.chase_sub` — every stage of the chase names a subset of `P`, so the production
    function may be applied to it again;
  - `Lambda.Post.chase_val_injective` — the values produced along the chase are pairwise distinct,
    since each one avoids the set of its own stage, which contains all the earlier ones;
  - `Lambda.Post.exists_chase_escape` — hence the chase escapes `L` within `L.length + 1` steps;
  - `Lambda.Post.prodEsc_notMem`, `Lambda.Post.prodEsc_prod` — the value returned is outside `L`
    unconditionally (a fresh number is returned if the search fails), and it is an element of `P`
    outside the starting set whenever the starting set is a subset of `P`.
* `Lambda.Post.prodInj`, `Lambda.Post.prodInj_injective`, `Lambda.Post.computable_prodInj` — the
  chase run at input `n` against the list of the values already produced at `0, …, n - 1` is a
  computable injective function, giving
  `Lambda.Post.exists_injective_productive`: **a productive set has an injective computable
  production function.**
* `Lambda.Post.exists_recursion_index_inj` — the recursion theorem with parameters, with an
  injective indexing (the indices are `Code.curry c x`, injective in `x`).
* `Lambda.Post.oneOneReducible_of_productive_compl` — **Myhill's theorem, one-one form**: if the
  complement of `C` is productive then every r.e. set reduces to `C` by an *injective* computable
  function.
* `Lambda.Post.Creative.oneOneComplete`, `Lambda.Post.Creative.oneOneEquiv_haltK`,
  `Lambda.Post.creative_iff_oneOneComplete` — every creative set is one-one complete, hence
  one-one equivalent to Kleene's `K`, and for r.e. sets creativity *is* one-one completeness.
* `Lambda.Post.Creative.recIso_haltK`, `Lambda.Post.Creative.recIso` — with Myhill's isomorphism
  theorem: **every creative set is recursively isomorphic to `K`**, and any two creative sets are
  recursively isomorphic.
* `Lambda.Post.creative_of_recIso_haltK`, `Lambda.Post.creative_iff_recIso_haltK` — the converse
  and hence the classification: a set of numbers is creative exactly when it is recursively
  isomorphic to `K`.
* The lambda-calculus instances `Lambda.recIso_codeHasNormalForm_haltK`,
  `Lambda.recIso_codeConverges_haltK` and `Lambda.recIso_codeSet_conv_church_haltK`: normalization,
  convergence to a numeral and convertibility with a Church numeral are, as sets of codes,
  recursively isomorphic to `K`.

## Boundary

None.  The classification is proved for arbitrary predicates on `ℕ`; creativity is the notion of
`Start/PostCreative.lean` (r.e. with productive complement) and `RecIso` is the notion of
`Start/MyhillIso.lean` (a computable bijection of `ℕ` carrying one set onto the other).

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
