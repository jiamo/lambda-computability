# M10-LAMBDA-THEORY-LATTICE

**Status:** DONE_STRONG

The λ-theories of this development, ordered, and the infinite Böhm tree.

## λ-theories — `Start/LambdaTheory.lean`

`Lambda.LambdaTheory` is an equivalence relation on the untyped terms which contains
β-conversion and is closed under filling a one-hole context (`Lambda.Ctx.comp`,
`Lambda.Ctx.fill_comp`, `Lambda.reduces_fill`, `Lambda.Conv.fill`, `Lambda.ObsEqHnf.fill`).
Four instances:

* `Lambda.LambdaTheory.beta` — β-conversion, the least λ-theory (`Lambda.LambdaTheory.beta_le`);
* `Lambda.LambdaTheory.graph` — `Th(𝒫ω)`, by soundness and compositionality of the graph model;
* `Lambda.LambdaTheory.dinf` — `Th(D∞)`;
* `Lambda.LambdaTheory.hstar` — `H*`, observational equivalence at head normalisation.

Comparison is on closed terms (`Lambda.LambdaTheory.LeClosed`, `LtClosed`), and the chain is

* **`Lambda.LambdaTheory.beta_lt_graph`** — strict, witnessed by `Ω` and `Ω I`: the graph model
  sends both to the empty denotation (`Lambda.LambdaTheory.graph_omega_app_omega_I`) while they
  are not β-convertible (`Lambda.LambdaTheory.not_conv_omega_app_omega_I`, proved from the fact
  that each of the two reduces only to itself);
* **`Lambda.LambdaTheory.graph_lt_dinf`** — strict, witnessed by `λx. x` and `λx λy. x y`
  (`Start/GraphNotFullyAbstract.lean`); the inclusion itself is adequacy of the graph model
  composed with full abstraction of `D∞`;
* **`Lambda.LambdaTheory.dinf_eq_hstar_closed`** — `Th(D∞) = H*`, a restatement of Wadsworth's
  theorem `ScottDinf.obsEqHnf_iff_ddenot_eq`;
* `Lambda.LambdaTheory.theory_chain` packages `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*`.

## Infinite Böhm trees — `Start/InfiniteBohmTree.lean`

`Lambda.BohmTree M = { ω(M') | M ↠ M' }` is the Böhm tree of `M` presented by its finite
approximants, and `Lambda.BohmLe` / `Lambda.BohmEq` are domination and equality of Böhm trees
(cofinality of the approximant sets in the approximation order).

The approximation order `Lambda.Approx` uses `Ω` as its bottom element, and `Ω` is itself an
application, so `Approx` is not transitive in general.  It is transitive on direct approximants,
and that is proved here:

* `Lambda.direct_ne_lam_of_headVar`, `Lambda.direct_ne_omega_of_headVar` — the function part of
  an application inside a direct approximant is never an abstraction and never `Ω`;
* `Lambda.eq_omega_of_approx_direct_omega` — a direct approximant below `Ω` is `Ω`;
* **`Lambda.approx_direct_trans`**, `Lambda.approx_direct_reduces`.

Consequences:

* `Lambda.BohmEq.trans` — Böhm tree equality is an equivalence relation;
* `Lambda.bohmEq_of_conv` — it contains β-conversion;
* **`Lambda.graph_of_bohmEq`** — it is contained in `Th(𝒫ω)`, by the approximation theorem;
* `Lambda.exists_bohmEq_not_conv` — the first containment is strict: `Ω` and `Ω I` have the same
  Böhm tree, namely `⊥` (`Lambda.bohmTree_omega`, `Lambda.bohmTree_app_omega_I`);
* `Lambda.bohmEq_between_beta_and_graph` packages `B ⊊ BT ⊆ Th(𝒫ω)`.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.LambdaTheory Start.InfiniteBohmTree`
* Axioms of `Lambda.LambdaTheory.theory_chain`, `Lambda.bohmEq_between_beta_and_graph`:
  `propext, Classical.choice, Quot.sound`.
