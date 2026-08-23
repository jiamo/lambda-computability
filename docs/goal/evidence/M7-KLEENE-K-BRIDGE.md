# M7-KLEENE-K-BRIDGE

**Status:** DONE_STRONG

Module `Start/KleeneK.lean`, imported by `Start.lean`.  `Start/HaltingComplete.lean` places the
lambda halting set in the arithmetical hierarchy; this module does the same for the *classical*
halting problem and then identifies the two.

## Definition

* `Lambda.HaltK n` — Kleene's diagonal halting set: the `n`-th partial recursive code of
  mathlib's `Nat.Partrec.Code`, run on the input `n`, halts.

## Theorems

* `Lambda.rePred_haltK` — `K` is recursively enumerable.
* `Lambda.rePred_le_one_haltK` — every r.e. predicate one-one reduces to `K`.  The reduction is
  the s-m-n theorem in the form of `Nat.Partrec.Code.curry`, whose injectivity
  (`Nat.Partrec.Code.curry_inj`) is what makes the reduction one-one rather than merely
  many-one.
* `Lambda.haltK_one_complete`, `Lambda.haltK_sigma1_complete` — `K` is one-one complete, hence
  Σ₁-complete.
* `Lambda.oneOneEquiv_haltK_codeHasNormalForm`, `Lambda.oneOneEquiv_haltK_codeConverges`,
  `Lambda.manyOneEquiv_haltK_codeHasNormalForm` — **the bridge**: the halting problem of the
  lambda calculus and the halting problem of the classical model are the *same* problem, not
  merely two undecidable problems.
* `Lambda.not_rePred_not_haltK` — the complement of `K` is not r.e.

On the lambda side the corresponding one-one statements are also proved in
`Start/HaltingComplete.lean`: `Lambda.reduceCode_injective`,
`Lambda.rePred_le_one_codeHasNormalForm`, `Lambda.rePred_le_one_codeConverges`,
`Lambda.codeHasNormalForm_one_complete`, and
`Lambda.oneOneEquiv_codeHasNormalForm_codeConverges`.

## Boundary

Computable *isomorphism* (Myhill's theorem: mutually one-one reducible sets are recursively
isomorphic) is not formalized; only one-one equivalence is.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.
