# M10-ARITH-HIERARCHY

**Status:** DONE_STRONG

Module `Start/ArithHierarchy.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

Define the arithmetical hierarchy over the computable predicates and develop its structural
theory, up to the identification of the bottom levels with the computable, r.e. and co-r.e.
predicates.

## What is proved

* `Lambda.Arith.qAlt` — the alternating quantifier prefix as a predicate transformer, the
  witnesses being accumulated by pairing, and `Lambda.Arith.qAlt_not` — the prefix dualises.
* `Lambda.Arith.SigmaAt`, `Lambda.Arith.PiAt`, `Lambda.Arith.DeltaAt` — the classes `Σ⁰ₙ`, `Π⁰ₙ`,
  `Δ⁰ₙ`, with `Lambda.Arith.piAt_iff_sigmaAt_not`, `Lambda.Arith.sigmaAt_iff_piAt_not`.
* `Lambda.Arith.qAlt_shift`, `Lambda.Arith.SigmaAt.subst`, `Lambda.Arith.PiAt.subst` —
  substituting a computable function into the base argument stays in the class.
* `Lambda.Arith.SigmaAt.succ`, `Lambda.Arith.PiAt.succ`, `Lambda.Arith.SigmaAt.of_piAt`,
  `Lambda.Arith.PiAt.of_sigmaAt`, `Lambda.Arith.DeltaAt.of_sigmaAt`,
  `Lambda.Arith.DeltaAt.of_piAt` — the inclusions `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁`.
* `Lambda.Arith.sigmaAt_succ_iff`, `Lambda.Arith.piAt_succ_iff` — peeling the outermost
  quantifier.
* `Lambda.Arith.sigmaAt_closure`, `Lambda.Arith.SigmaAt.and`, `.or`, `Lambda.Arith.PiAt.and`,
  `.or` — every level is closed under conjunction and disjunction, proved by a single induction
  whose step uses the dual closure of `Π⁰ₙ` obtained from the induction hypothesis by de Morgan.
* `Lambda.Arith.SigmaAt.exists`, `Lambda.Arith.PiAt.forall` — `Σ⁰ₙ₊₁` is closed under existential
  and `Π⁰ₙ₊₁` under universal quantification, by contracting two witnesses into one pair.
* `Lambda.Arith.sigmaAt_zero_iff`, `Lambda.Arith.piAt_zero_iff` — level `0` is the computable
  predicates; `Lambda.Arith.rePred_of_exists_computable`, `Lambda.Arith.sigmaAt_one_iff` — `Σ⁰₁`
  is the r.e. predicates; `Lambda.Arith.piAt_one_iff` — `Π⁰₁` the co-r.e. ones; and
  `Lambda.Arith.deltaAt_one_iff` — `Δ⁰₁` is exactly the computable predicates.

`Lambda.Post.exists_test_of_rePred` moved from `Start/ChaitinIncompleteness.lean` to
`Start/PostSimple.lean`, next to the numbering of the r.e. sets it is proved from, so that the
hierarchy module can reuse it; `Start/ChaitinIncompleteness.lean` still obtains it by import.

## Boundary

None.

## Gates

* `lake build` — the whole library, no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
