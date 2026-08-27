# M9-UNTYPED-FULL-ABSTRACTION

**Status:** BACKEND_PARTIAL

This task records the question that adequacy leaves open for the untyped models, so that the state
of the project is not overstated.

`M9-GRAPH-ADEQUACY` and `M9-DINF-ADEQUACY` prove *adequacy* for Scott's graph model and for `D∞`:
a term whose denotation is not the least element has a head normal form, the least element is
exactly the unsolvable closed terms, and denotational equality implies observational equivalence at
the level of head normalization (`GraphModel.obsEqHnf_of_denot_eq`,
`ScottDinf.obsEqHnf_of_ddenot_eq`).

What is **not** proved anywhere in the project is the converse inclusion — *full abstraction*:

* if `M` and `N` are observationally equivalent (`Lambda.ObsEqHnf`), are their denotations equal in
  every environment?

## Intended design

The classical route goes through the approximation (Böhm-tree) theory of the model: one shows that
the denotation of a term is the supremum of the denotations of its finite approximants, so that two
terms with the same denotation-theoretic behaviour under all contexts have the same tree up to the
identification the model makes.  The project has the syntactic ingredients this needs — head
reduction and its normalization theorem (`Start/HeadReduction.lean`), standardization
(`Start/Standardization.lean`), solvability (`Start/Solvability.lean`) and Böhm's theorem
(`Start/Bohm.lean`) — but no approximation theorem: nothing yet expresses the denotation of a term
as a supremum over its finite approximants, which is the missing step for either model.

## Settled for the graph model: full abstraction fails

One half of the question is now answered, negatively, in `Start/GraphNotFullyAbstract.lean`:
**Scott's graph model is not fully abstract.**

The witnesses are the identity `GraphNotFullyAbstract.idTm = λx. x` and its eta-expansion
`GraphNotFullyAbstract.etaTm = λx. λy. x y`, both closed.

* They have *different* denotations in the graph model, in every environment
  (`GraphNotFullyAbstract.denot_idTm_ne_denot_etaTm`).  The graph model is not extensional: the
  token `[atom 0] ⇒ atom 0` lies in the graph of the identity, while every token in the
  denotation of the eta-expansion is a step function whose output is again a step function, never
  an atom (`tok_mem_denot_idTm`, `tok_notMem_denot_etaTm`).
* No context distinguishes them (`GraphNotFullyAbstract.obsEqHnf_idTm_etaTm`).  This is where the
  second model does the work: `D∞` *does* validate eta (`ScottDinf.ddenot_eta`), so the two terms
  have the same `D∞` denotation in every environment (`GraphNotFullyAbstract.ddenot_etaTm`), and
  `D∞` is adequate, so equal denotations there imply observational equivalence at head
  normalization (`ScottDinf.obsEqHnf_of_ddenot_eq`).

Hence `GraphNotFullyAbstract.graph_not_fully_abstract`: there are closed terms `M`, `N` with
`Lambda.ObsEqHnf M N` and `GraphModel.denot M ρ ≠ GraphModel.denot N ρ` for every `ρ`.  The
inclusion proved in `Start/GraphObs.lean` — denotational equality implies observational
equivalence — is therefore *strict* for the graph model.

What remains open is full abstraction for `D∞` (Wadsworth's theorem), and with it the
approximation theorem that the classical proof needs; the argument above does not settle it, since
it only uses that `D∞` identifies more terms than the graph model does.

## Progress on the approximation theory: `Start/GraphApprox.lean`

The syntactic side of the approximation theory is now in place, together with the soundness half
of the approximation theorem and its consequence at the least element.

* `Lambda.Approx` — the approximation order `A ⊑ M`: `A` is obtained from `M` by replacing
  subterms with `Ω`.  `Lambda.direct` is the direct approximant `ω(M)`, which keeps the
  abstraction prefix and the variable head of `M` and erases everything under a head redex to
  `Ω`; `Lambda.approx_direct` says `ω(M) ⊑ M`, `Lambda.isHnf_direct` that the direct approximant
  of a head normal form is again one, and `Lambda.IsClosed.direct` that it stays closed.
* `GraphModel.denot_approx_subset` — the denotation is monotone for `⊑`, so
  `GraphModel.denot_direct_subset` and `GraphModel.denot_direct_reduct_subset` hold, and
  `GraphModel.iUnion_denot_direct_subset` gives the *soundness* inclusion
  `⋃ {⟦ω(M')⟧ρ : M ↠ M'} ⊆ ⟦M⟧ρ`.
* `GraphModel.denot_ne_empty_iff_exists_reduct_direct` — for a closed term the two sides are
  empty together: `⟦M⟧ρ ≠ ∅` exactly when `⟦ω(M')⟧ρ ≠ ∅` for some reduct `M'`.  This uses
  adequacy in one direction and soundness of approximation in the other.

## The approximation theorem: `Start/GraphApproxTheorem.lean`

The reverse inclusion `⟦M⟧ρ ⊆ ⋃ {⟦ω(M')⟧ρ : M ↠ M'}` — that *every* token of the denotation is
already produced by a finite approximant — is now proved as well, so the approximation theorem
holds in the graph model:

* `GraphModel.exists_reduct_mem_denot_direct` — every token of `⟦M⟧ρ` lies in `⟦ω(M')⟧ρ` for
  some reduct `M'` of `M`;
* `GraphModel.denot_eq_iUnion_denot_direct` — hence `⟦M⟧ρ = ⋃ {⟦ω(M')⟧ρ : M ↠ M'}`.

The proof is a Kripke-style computability (logical relations) argument, in the same shape as the
adequacy proof of `Start/GraphAdequacy.lean` but carrying the approximant information.
`GraphModel.ARealAux b ρ t` says that `t` reduces to a term whose direct approximant already
contains the token `b`, and — for a step function `a ⇒ c` — that applying `t` to any term
satisfying every token of `a` produces a term satisfying `c`; the recursion is on the size of the
token.  `GraphModel.AReal` closes the predicate under weakening of the environment.  Unlike in
the adequacy proof the *semantic* environment has to be weakened alongside the syntactic one, so
the fundamental lemma `GraphModel.arealAux_substEnv` relates two environments: one interpreting
the free variables of the term, one interpreting the target context of the substitution.
Instantiating it at the identity substitution gives the theorem.

Two syntactic ingredients feed the argument, both proved in the same file:

* `GraphModel.denot_direct_reduces_mono` — direct approximants only grow along reduction, via
  `Lambda.approx_direct_step` (`ω(M) ⊑ ω(M')` for a single step `M → M'`) and monotonicity of the
  denotation for `⊑`.  Note that `Lambda.Approx` is *not* transitive here, because `Ω` is an
  ordinary term rather than a constant, so the chaining is done at the level of the denotations.
* `GraphModel.exists_reduct_lset_subset` — by confluence (`Lambda.confluence_theorem`), finitely
  many reducts of a term can be merged into a single reduct that sees all of their tokens.

Still open: full abstraction for `D∞` (Wadsworth's theorem).  The corresponding approximation
theorem for `D∞`, which the classical proof needs, is not proved here.

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on the results above
reports only `propext`, `Classical.choice`, `Quot.sound`.
