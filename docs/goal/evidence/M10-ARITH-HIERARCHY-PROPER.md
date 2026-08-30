# M10-ARITH-HIERARCHY-PROPER

**Status:** DONE_STRONG

Module `Start/ArithHierarchyProper.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

Show that the classes of `Start/ArithHierarchy.lean` do not collapse: separate each level from
its dual and from the level below, by the classical route through universal predicates and
diagonalisation.

## What is proved

* `Lambda.Arith.UnivSigma`, `Lambda.Arith.UnivPi` — universality for a level: a predicate of one
  number that is itself at that level, and into which every predicate at that level is
  substituted by fixing the first component of the argument pair.
* `Lambda.Arith.univOne`, `Lambda.Arith.rePred_univOne`, `Lambda.Arith.univSigma_one` — the
  universal `Σ⁰₁` predicate `⟨e, x⟩ ↦ x ∈ Wₑ`, universal because the numbering of the r.e. sets
  (`Lambda.Post.Wset`, `Lambda.Post.exists_index`) exhausts the r.e. predicates and is itself
  r.e.
* `Lambda.Arith.UnivSigma.not` — negation turns a universal `Σ⁰ₙ` predicate into a universal
  `Π⁰ₙ` one; `Lambda.Arith.sigmaSucc`, `Lambda.Arith.computable_sigmaSuccArg`,
  `Lambda.Arith.UnivPi.sigmaSucc` — one existential quantifier in front of a universal `Π⁰ₙ`
  predicate, with the index carried along, gives a universal `Σ⁰ₙ₊₁` one.
* `Lambda.Arith.exists_univSigma`, `Lambda.Arith.exists_univPi` — hence **every level `n + 1`
  has a universal predicate**.
* `Lambda.Arith.UnivSigma.piAt_diag`, `Lambda.Arith.UnivSigma.not_sigmaAt_diag`,
  `Lambda.Arith.UnivSigma.not_piAt` — the diagonalisation: the diagonal complement
  `x ↦ ¬ U ⟨x, x⟩` of a universal `Σ⁰ₙ` predicate is `Π⁰ₙ` but not `Σ⁰ₙ`, and `U` itself is not
  `Π⁰ₙ`.
* The separations, for every level `n + 1`: `Lambda.Arith.exists_piAt_not_sigmaAt`,
  `Lambda.Arith.exists_sigmaAt_not_piAt`, `Lambda.Arith.sigmaAt_ne_piAt`,
  `Lambda.Arith.not_sigmaAt_closed_under_not`, `Lambda.Arith.exists_sigmaAt_not_deltaAt`,
  `Lambda.Arith.exists_piAt_not_deltaAt`.
* The properness of the hierarchy: `Lambda.Arith.sigmaAt_proper`, `Lambda.Arith.piAt_proper`,
  `Lambda.Arith.deltaAt_proper` — each of `Σ⁰ₙ`, `Π⁰ₙ`, `Δ⁰ₙ` grows strictly with `n`.
* `Lambda.Arith.Arithmetical`, `Lambda.Arith.Arithmetical.not`,
  `Lambda.Arith.Arithmetical.subst`, `Lambda.Arith.exists_arithmetical_not_sigmaAt` and
  `Lambda.Arith.not_exists_univ_arithmetical` — no level exhausts the arithmetical predicates,
  and the union of the levels, unlike each single level, has no universal predicate.
* At level one this reads as `Lambda.Arith.exists_rePred_not_rePred_compl` (the r.e. predicates
  are not closed under complement) and `Lambda.Arith.exists_rePred_not_computablePred`.

## Boundary

None.

## Gates

* `lake build Start.ArithHierarchyProper` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
