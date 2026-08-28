# M9-UNTYPED-FULL-ABSTRACTION

**Status:** DONE_STRONG

Full abstraction is settled for both untyped models: **negatively** for Scott's graph model and
**positively** for `D∞`, where Wadsworth's theorem is proved outright in
`Start/DinfTagBelowSound.lean` (last section).  The sections in between record how the argument was
built up, and are kept as written; where they say that a statement is open or conditional, they
describe the state of the development at the time and are superseded by the last section.

`M9-GRAPH-ADEQUACY` and `M9-DINF-ADEQUACY` prove *adequacy* for Scott's graph model and for `D∞`:
a term whose denotation is not the least element has a head normal form, the least element is
exactly the unsolvable closed terms, and denotational equality implies observational equivalence at
the level of head normalization (`GraphModel.obsEqHnf_of_denot_eq`,
`ScottDinf.obsEqHnf_of_ddenot_eq`).

The converse inclusion — *full abstraction* — asks:

* if `M` and `N` are observationally equivalent (`Lambda.ObsEqHnf`), are their denotations equal in
  every environment?

It is settled negatively for the graph model and positively for `D∞`, for arbitrary closed terms:
`ScottDinf.obsEqHnf_iff_ddenot_eq`.

## Intended design

The classical route goes through the approximation (Böhm-tree) theory of the model: one shows that
the denotation of a term is the supremum of the denotations of its finite approximants, so that two
terms with the same denotation-theoretic behaviour under all contexts have the same tree up to the
identification the model makes.  The project has the syntactic ingredients this needs — head
reduction and its normalization theorem (`Start/HeadReduction.lean`), standardization
(`Start/Standardization.lean`), solvability (`Start/Solvability.lean`) and Böhm's theorem
(`Start/Bohm.lean`), and the approximation theorem is now proved for both models
(`GraphModel.denot_eq_iUnion_denot_direct`, `ScottDinf.isLUB_ddenot_direct`).

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

This says nothing about `D∞`, since the argument only uses that `D∞` identifies more terms than
the graph model does; `D∞` is treated in the last two sections below.

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

## The approximation theorem for `D∞`: `Start/DinfApprox.lean`

The same theorem is now available for `D∞`, in the order-theoretic form the continuous model
calls for:

* `ScottDinf.isLUB_ddenot_direct` — the denotation `⟦M⟧ρ` is the **least upper bound** of the
  set `{⟦ω(M')⟧ρ : M ↠ M'}` of denotations of the direct approximants of the reducts of `M`;
* `ScottDinf.exists_reduct_app_le` — the level-wise form the proof rests on, and
  `ScottDinf.exists_reduct_ddenot_direct_sup`, `ScottDinf.ddenot_eq_of_approx_reducts` — the
  usual consequences.

The proof is again a logical-relations argument, this time indexed by the finite levels `D n` of
the inverse-limit tower: `ScottDinf.ARelD n z ρ t` says that the level-`n` element `z` is already
below the denotation of the direct approximant of some reduct of `t`, with the function levels
handled by quantifying over related arguments.  Every level is finite (`ScottDinf.finite_D`), so a
supremum along a chain is attained (`ScottDinf.exists_ωSup_eq`), and confluence merges the finitely
many reducts produced at the different levels (`ScottDinf.exists_reduct_forall`).  The fundamental
lemma is `ScottDinf.arealD_substEnv`.

## Full abstraction of `D∞` on closed normal forms

Böhm's separation theorem is available in its η-general form (`Start/BohmEta.lean`): two closed
normal forms whose Böhm trees are not η-equal — `Lambda.TagEq` being η-equality of tagged trees —
are separable.  The two remaining files turn this into full abstraction on normal forms.

* `Start/DinfBohmEta.lean`: `ScottDinf.ddenot_toTerm_eq_of_tagEq` — **η-equal Böhm trees have the
  same `D∞` denotation**.  The proof is a size induction mirroring the syntactic descent of
  `Start/BohmEta.lean`: at each node both denotations are fed the same stack of arguments, which
  is legitimate because `D∞` is extensional (`ScottDinf.dinf_ext_dappN`, proved in
  `Start/DinfApply.lean` together with the calculus of iterated application `ScottDinf.dappSeq`,
  `ScottDinf.dappN`, `ScottDinf.envStack`), and the induction hypothesis applies to the arguments,
  the tags guaranteeing that matching variables denote matching values
  (`ScottDinf.envStack_match`).
* `Start/DinfNormalFullAbstraction.lean`: `ScottDinf.not_obsEqHnf_of_separable` — separable terms
  are observationally distinguishable, by the context `C[X] = X a₁ … aₖ Ω I`, which reduces to `Ω`
  on the `true` side and to `I` on the `false` side.  Together with the previous item this gives
  `ScottDinf.ddenot_eq_of_obsEqHnf_normal` and
  `ScottDinf.obsEqHnf_iff_ddenot_eq_normal`: **for closed β-normal forms, observational
  equivalence and equality of `D∞` denotations coincide.**  Soundness of the interpretation and
  adequacy extend this to every closed term that *has* a β-normal form
  (`ScottDinf.obsEqHnf_iff_ddenot_eq_of_normalizes`), and at the other extreme
  `ScottDinf.ddenot_eq_of_obsEqHnf_of_not_hasHnf` settles the head-divergent terms.

## The reduction to a separation principle: `Start/DinfWadsworth.lean`

*(Written while full abstraction for arbitrary terms was still open; it is proved in the last
section.)*  The argument of the previous section is confined to the finite case.
It uses Böhm's separation theorem, which applies to β-normal forms, whereas the general statement
needs separation for the finite approximants `ω(M')`, which contain `Ω`.
`Start/DinfWadsworth.lean` isolates exactly that gap:

* `ScottDinf.ddenot_fill_mono` — contexts are monotone in the denotation of the term in the hole
  (proved);
* `ScottDinf.SeparatesApprox` — the separation principle for approximants: if a closed
  approximant `A` is not below a closed term `N` in `D∞`, some context makes `A` semantically
  nontrivial while sending `N` to a head-divergent term.  This proposition is **stated, not
  proved**;
* `ScottDinf.obsEqHnf_iff_ddenot_eq_of_separatesApprox` — full abstraction of `D∞` for all closed
  terms, *conditional* on that principle (proved).  Given a reduct whose approximant escapes
  `⟦N⟧`, the separating context together with monotonicity of contexts and adequacy contradicts
  observational equivalence; the approximation theorem then closes the argument.

`ScottDinf.SeparatesApprox` is an ordinary proposition appearing as an explicit hypothesis — no
axiom is introduced anywhere.

Gates: `lake build` succeeds; no `sorry`; no linter warnings; `#print axioms` on the results above
reports only `propext`, `Classical.choice`, `Quot.sound`.

## Narrowing the gap: the Böhm-out for approximants is now proved

`ScottDinf.SeparatesApprox` mixes two independent ingredients: a *syntactic* Böhm-out (produce a
separating context) and a *semantic* recognition step (decide when one denotation fails to be
below another).  The syntactic ingredient is now available, so the gap is purely semantic.

* `Start/HeadSpine.lean` supplies the syntactic facts the term-level Böhm-out needs that the
  tree-level development did not: `Lambda.exists_spine_of_hasHnf` (a head normalizing term reduces
  to a spine `λx₁ … x_b. x_h M₁ … M_k`) and its converse `Lambda.hasHnf_lamN_appList`;
  `Lambda.HasHnf.reduces`, head normalizability inherited *forwards* along a reduction, by
  confluence; `Lambda.not_hasHnf_appList` and `Lambda.hasHnf_of_hasHnf_csub`, unsolvability being
  preserved by application and by substitution of closed terms; and the one-sided separation
  `Lambda.SepDiv M N` — some list of closed arguments makes `M` head-converge and `N`
  head-diverge — with `Lambda.SepDiv.of_reduces` and `Lambda.SepDiv.of_separable`.
* `Start/TagFail.lean` defines `Lambda.TagFail`, a *finite failure witness* for the comparison of
  two arbitrary terms: along a path on which the η-expanded head normal forms agree, either the
  second term head-diverges where the first has a node, or the two η-expanded nodes have different
  head tags or different arities.  Its main theorem `Lambda.sepDiv_of_tagFail` is the **Böhm-out
  against an arbitrary term**: a failure witness yields closed arguments realising `Lambda.SepDiv`
  for the tagged instantiations.  Unlike `Lambda.separable_of_tagDiffer` of `Start/BohmEta.lean`,
  where both objects were Böhm trees of β-normal forms with a priori arity and binder bounds, the
  nodes of the second object here are produced by head reduction, so the tag bound `B` and the
  arity bound `K` have to be produced *bottom-up* from the witness.
* `Start/DinfWadsworthSharp.lean` feeds this into the reduction.
  `ScottDinf.sepDiv_of_closed_of_tagFail` instantiates the bounds for closed terms (where the
  tagged substitution is the identity), `ScottDinf.separatesApprox_ctx_of_sepDiv` turns one-sided
  separation into a separating context, and
  `ScottDinf.separatesApprox_of_tagBelowSound` derives `ScottDinf.SeparatesApprox` from

  > `ScottDinf.TagBelowSound`: for closed `M`, `N`, if the comparison of `M` and `N` admits *no*
  > finite failure witness, then `⟦M⟧ρ ≤ ⟦N⟧ρ` in `D∞` for every `ρ`.

  Full abstraction is then conditional on this one proposition:
  `ScottDinf.obsEqHnf_iff_ddenot_eq_of_tagBelowSound`.

`ScottDinf.TagBelowSound` mentions no contexts and no separation, only the `D∞` order; it is what
is genuinely left of the Wadsworth theorem here.  It has to be phrased as the *negation* of the
inductive relation `Lambda.TagFail` rather than as a positive inductive "below" relation, because
`D∞` identifies a term with its infinite η-expansions (for instance `x` with `Y (λf y. x (f y))`),
which no inductively generated relation on finite witnesses reaches.  Like `SeparatesApprox`
before it, it is an ordinary proposition occurring as an explicit hypothesis — no axiom is
introduced.

The *converse* of `ScottDinf.TagBelowSound` is proved unconditionally in the same file:
`ScottDinf.not_ddenot_le_of_tagFail` shows that a finite failure witness for two closed terms does
refute `⟦M⟧ρ ≤ ⟦N⟧ρ`, by running the Böhm-out and combining it with monotonicity of contexts and
adequacy.  So the witnesses are never spurious, and `ScottDinf.TagBelowSound` is precisely the one
missing implication of the characterisation `ScottDinf.ddenot_le_iff_not_tagFail`.  A corollary
worth recording is `ScottDinf.not_tagFail_self`: no closed term admits a failure witness against
itself, so `Lambda.TagFail` is not vacuously satisfiable and the reduction is not degenerate.

Gates for the new modules `Start/HeadSpine.lean`, `Start/TagFail.lean` and
`Start/DinfWadsworthSharp.lean`: they build; no `sorry`; no linter warnings; `#print axioms` on
`Lambda.sepDiv_of_tagFail`, `ScottDinf.separatesApprox_of_tagBelowSound`,
`ScottDinf.obsEqHnf_iff_ddenot_eq_of_tagBelowSound`, `ScottDinf.not_ddenot_le_of_tagFail` and
`ScottDinf.not_tagFail_self` reports only `propext`, `Classical.choice`, `Quot.sound`.

## The infinite η-expansion, settled (`Start/DinfEtaLimit.lean`)

The obstruction quoted above — that `D∞` identifies a term with its infinite η-expansion, so that
no relation generated by finite witnesses can decide the `D∞` order — is now a *theorem* rather
than an informal remark.

Let `J = Θ (λ j x y. x (j y))`, a closed term built from Turing's fixed-point combinator, so that
`ScottDinf.Jterm_reduces` gives `J →* λx y. x (J y)`.  Unfolding, `J x = λy. x (J y) = λy. x (λ y'.
y (J y')) = …`: `J` is the identity η-expanded infinitely often, and is β-convertible to no finite
η-expansion of `λx. x`.

* `ScottDinf.eq_dId_of_eta_fixpoint` — **if `x : D∞` satisfies `x · y · z = y · (x · z)` for all
  `y, z` and `x · ⊥ = ⊥`, then `x` is the identity.**  These two equations are exactly what the
  infinite η-expansion of the identity satisfies; no finite amount of η-expansion is assumed.
* `ScottDinf.ddenot_Jterm_eq_ddenot_id` — hence `⟦J⟧ρ = ⟦λx. x⟧ρ` in every environment;
* `ScottDinf.obsEqHnf_Jterm_id` — and therefore, by adequacy, no context separates them.

The proof runs two simultaneous inductions over the levels of the inverse limit,
`ScottDinf.psi_le_Phi_of_eta_fixpoint` (`⟦I⟧ ≤ x`) and
`ScottDinf.theta_Phi_le_psi_of_eta_fixpoint` (`x ≤ ⟦I⟧`), the limit step being exactly the place
where a finite witness would be required.  The general machinery it needed is reusable:

* `ScottDinf.theta_le_iff` — `theta n x ≤ v` is decided at level `n` alone;
* `ScottDinf.theta_succ_le_of_forall_psi` — the criterion for `theta (n+1) x ≤ v` which only ever
  applies `x` and `v` to elements of the image of `psiFun n`;
* `ScottDinf.Phi_psi_succ_app` — an element coming from level `n+1` computes at level `n` exactly
  by its level-`(n+1)` component;
* `ScottDinf.Phi_bot_app_zero`, `ScottDinf.psiFun_botD` — the base level of application.

Note that the naive strengthening `theta n (x · z) ≤ x · theta n z` is *false* in `D∞`
(application is a supremum over the approximating chain, and only the inequality
`ScottDinf.toFn_app_le_Phi` holds unconditionally); this is why every step above restricts either
the argument or the function to the image of a `psiFun`.

Gates for `Start/DinfEtaLimit.lean`: it builds; no `sorry`; no linter warnings; `#print axioms` on
`ScottDinf.eq_dId_of_eta_fixpoint`, `ScottDinf.ddenot_Jterm_eq_ddenot_id` and
`ScottDinf.obsEqHnf_Jterm_id` reports only `propext`, `Classical.choice`, `Quot.sound`.

An extra criterion extracted from the same engine, `ScottDinf.le_of_forall_psi`, states
extensionality at the finite levels: `x ≤ v` follows from
`theta n (x · psiFun n z) ≤ v · psiFun n z` for all `n` and `z : D n`.

## Wadsworth's theorem, proved: `Start/DinfTagBelowSound.lean`

The one remaining statement, `ScottDinf.TagBelowSound`, is now a theorem, so every conditional
result above becomes unconditional.

* `ScottDinf.tagBelowSound` — for closed terms, absence of a finite failure witness
  `Lambda.TagFail` implies `⟦M⟧ρ ≤ ⟦N⟧ρ` in `D∞`.
* `ScottDinf.separatesApprox` — hence `ScottDinf.SeparatesApprox`, the separation principle of
  `Start/DinfWadsworth.lean`.
* `ScottDinf.ddenot_le_iff_not_tagFail_unconditional` — combined with the converse
  `ScottDinf.not_ddenot_le_of_tagFail`, the `D∞` order between closed terms *is* the absence of a
  failure witness.
* `ScottDinf.obsEqHnf_iff_ddenot_eq` — **Wadsworth's theorem**: two closed terms are
  observationally equivalent, by head normalisation, exactly when they have the same denotation in
  `D∞`.
* `ScottDinf.obsEqHnf_iff_not_tagFail` — hence a finite-witness characterisation of observational
  equivalence itself: two closed terms are observationally equivalent exactly when neither
  comparison admits a failure witness.  Neither side of that equivalence mentions the model.

The proof has two halves, either side of the approximation theorem
`ScottDinf.isLUB_ddenot_direct`, which reduces the claim to putting each finite approximant of a
reduct of `M` below `N`.

* **An approximant below a term** — `ScottDinf.le_ddenot_of_not_tagFail_approx`
  (`Start/DinfTagBelowSound.lean`).  A size induction on the approximant.  The shape lemma
  `Lambda.approx_direct_shape` (`Start/ApproxShape.lean`) says that an approximant of a direct
  approximant is either dominated by an unsolvable term — in which case it denotes `⊥` by
  adequacy — or is a spine `λx₁ … x_b. x_h A₁ … A_k` whose binders and head variable are copied
  from the term, with its arguments related in the same way.  Absence of a failure witness then
  gives a head normal form for `N`, equal head tags and equal η-expanded arities, and the two
  nodes are compared after feeding both sides the same stack of arguments — legitimate because
  `D∞` is order-extensional (`ScottDinf.le_of_forall_dappN`).  Matching tags name equal values
  (`ScottDinf.envStack_match`, `ScottDinf.argEnvD_match_len`), which is what carries the
  environments through the descent.
* **A variable below a term** — `ScottDinf.le_ddenot_of_not_tagFail_var`
  (`Start/DinfTagBelow.lean`).  The arguments supplied by the η-expansion are variables, and there
  the right hand side may be an *infinite* η-expansion of the variable, which no structural
  induction reaches; the comparison is carried out level by level in the inverse limit, with
  `ScottDinf.theta_add_le_of_forall_dappN` paying one level per binder and
  `ScottDinf.app_zero_dappSeq_le` bottoming out at level `0` when the node has more binders than
  there are levels left (`Start/DinfSpine.lean`).

Gates for `Start/ApproxShape.lean`, `Start/DinfSpine.lean`, `Start/DinfTagBelow.lean` and
`Start/DinfTagBelowSound.lean`: they build; no `sorry`; no linter warnings; `#print axioms` on
`ScottDinf.tagBelowSound`, `ScottDinf.le_ddenot_of_not_tagFail_approx`,
`ScottDinf.separatesApprox` and `ScottDinf.obsEqHnf_iff_ddenot_eq` reports only `propext`,
`Classical.choice`, `Quot.sound`.
