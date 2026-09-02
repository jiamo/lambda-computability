# M10-ARITH-INDEX-SETS

**Status:** DONE_STRONG

Module `Start/ArithIndexSets.lean`, imported by `Start.lean` and registered in
`Start/Capstones.lean`.  It builds without `sorry` and without linter warnings.

## What the task asked

`Start/ArithComplete.lean` makes completeness available at every level of the arithmetical
hierarchy, but exhibits a concrete complete predicate only at level one, where it is the halting
problem.  Do the same at level two with the classical example: the index set of the total
functions.

## What is proved

* `Lambda.Arith.Tot` — the index set: `Tot e` says that every number lies in the `e`-th
  recursively enumerable set, that is, that the `e`-th partial recursive function is total.
  `Lambda.Arith.tot_iff_forall_dom` unfolds this to the domain of `Code.eval`.
* `Lambda.Arith.piAt_two_tot` — totality is `Π⁰₂`.  Membership in the `e`-th r.e. set is the
  universal `Σ⁰₁` predicate of `Start/ArithHierarchyProper.lean` applied to the pair `⟨e, x⟩`; a
  universal quantifier in front of a `Σ⁰₁` matrix stays at level two by the closure of `Π⁰₂`
  under universal quantification.
* `Lambda.Arith.piAt_two_le_one_tot` — totality is hard for `Π⁰₂` **under one-one reducibility**.
  Peeling the outer quantifier writes a `Π⁰₂` predicate as `P x ↔ ∀ y, Q ⟨x, y⟩` with `Q`
  recursively enumerable; taking a partial recursive `f` whose domain is `Q` and a code `c` for
  it, the s-m-n function `x ↦ ⌜curry c x⌝` is computable and injective (`Code.curry_inj`), and the
  function it indexes is total exactly when every `⟨x, y⟩` is in the domain of `f`.
* `Lambda.Arith.tot_piComplete` — hence totality is `Π⁰₂`-complete, and
  `Lambda.Arith.notTot_sigmaComplete` — its complement is `Σ⁰₂`-complete.
* The negative consequences, all read off from `Start/ArithComplete.lean`:
  `Lambda.Arith.not_sigmaAt_two_tot`, `Lambda.Arith.not_deltaAt_two_tot`,
  `Lambda.Arith.not_piAt_one_tot`, `Lambda.Arith.not_sigmaAt_one_tot`,
  `Lambda.Arith.not_rePred_tot`, `Lambda.Arith.not_rePred_compl_tot`,
  `Lambda.Arith.not_computablePred_tot`.
* `Lambda.Arith.haltK_le_tot`, `Lambda.Arith.not_manyOne_tot_haltK` — the halting problem
  many-one reduces to totality, because it is `Σ⁰₁` and therefore `Π⁰₂`, but totality does not
  reduce to the halting problem, since a reduction would make it recursively enumerable.  So
  totality is strictly harder than halting.

## Boundary

None.

## Gates

* `lake build Start.ArithIndexSets` — no error and no warning.
* `python3 scripts/check_closure.py`.
* `python3 scripts/goal_state.py validate`.
* Axiom audit: the results above depend only on `propext`, `Classical.choice` and `Quot.sound`.
