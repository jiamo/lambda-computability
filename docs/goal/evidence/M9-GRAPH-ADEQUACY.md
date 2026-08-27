# M9-GRAPH-ADEQUACY

**Status:** DONE_STRONG

Scott's graph model was already built (`Start/GraphModel.lean`) and the interpretation of the
untyped calculus in it proved *sound* (`Start/GraphModelSemantics.lean`): β-conversion preserves
denotations and `Ω` denotes the least element `∅`.  Soundness alone leaves open the possibility
that other, computationally meaningful, terms also denote `∅`.  This task closes that gap: the
denotation is nonempty exactly for the terms that have a head normal form, equivalently — for
closed terms — exactly for the solvable ones.

## Head normal forms — `Start/HeadNormal.lean`

* `Lambda.IsHnf` — `λx₁ … xₙ. y M₁ … Mₘ`, defined over the neutral terms `Lambda.Neutral` of
  `Start/Leftmost.lean`;
* `Lambda.HasHnf` — reducing to one, with `Lambda.HasHnf.of_reduces` (backwards closure along a
  reduction), `Lambda.hasHnf_lam`, `Lambda.hasHnf_of_neutral`.

## Realizability and the fundamental lemma — `Start/GraphAdequacy.lean`

The proof is the classical computability (logical-relations) argument, carried out directly on
the tokens of the model.

* **`GraphModel.RealAux b t`** — the term `t` *realizes* the token `b`: it has a head normal
  form, and if `b` is a step function `a ⇒ c` then applying `t` to any term realizing all of `a`
  realizes `c`.  The definition recurses on `Tok.size`.
* **`GraphModel.Real b t`** — realizability of *every lifting* of `t`.  Quantifying over the
  liftings is what makes the relation stable under the shift that de Bruijn parallel substitution
  performs at a binder (`GraphModel.Real.lift`), and it is exactly the hypothesis the step
  function clause consumes.
* `GraphModel.realAux_expand` (realizability is inherited backwards along a reduction) and
  `GraphModel.realAux_of_neutral` (a neutral term realizes every token) are proved by induction
  on the size of the token.
* **`GraphModel.realAux_substEnv`** — the fundamental lemma: if the terms of `u` realize the
  values of `ρ`, then every token of `⟦t⟧ρ` is realized by `t[u]`.  The abstraction case uses the
  β-equation for parallel substitution `Lambda.subst_zero_substEnv` and the application case the
  commutation `Lambda.lift_substEnv` (both in `Start/ParallelSubst.lean`, which now also hosts the
  composition lemmas previously proved inside `Start/SimpleTypes.lean`).

## Adequacy and its converse — `Start/GraphAdequacy.lean`

* **`GraphModel.hasHnf_of_mem_denot`** — *adequacy*: if `⟦t⟧ρ` contains a token, for **any**
  environment `ρ`, then `t` has a head normal form.  The identity substitution realizes every
  environment, because variables are neutral.
* `GraphModel.denot_eq_empty_of_not_hasHnf` — the contrapositive.
* **`GraphModel.exists_denot_ne_empty_of_hasHnf`** — the converse: a head normal form has a
  nonempty denotation in a suitable environment (a neutral term realizes any prescribed token
  after choosing the environment, and continuity `GraphModel.denot_fin` supplies the finite
  approximation needed to go under a binder).
* `GraphModel.denot_congr`, `GraphModel.denot_closed_congr` — the denotation only depends on the
  values of the free variables, so for a closed term the environment is irrelevant, whence
  **`GraphModel.denot_ne_empty_iff_hasHnf`**: a closed term denotes `∅` exactly when it has no
  head normal form.
* `GraphModel.not_hasHnf_omega` — the statement is not vacuous in either direction: `Ω` has no
  head normal form, because it denotes `∅`.
* **`GraphModel.hasHnf_of_solvable`** — every solvable term has a head normal form, by adequacy
  and soundness: a solvable term is driven to `I`, whose denotation is not `∅`, and applying a
  term of empty denotation to arguments cannot produce anything
  (`GraphModel.denot_appList_eq_empty`).

## Solvability — `Start/HnfSolvable.lean`

The syntactic converse of the last item, which completes the characterization:

* `Lambda.exists_lamN_neutral`, `Lambda.exists_appList_var` — a head normal form is
  `λx₁ … xₙ. y M₁ … Mₘ`;
* **`Lambda.solvable_of_isHnf`** — a *closed* head normal form is solvable.  Applying it to `n`
  copies of `λy₁ … y_m. I` performs `Lambda.substDown` (the substitution calculus of
  `Start/Bohm.lean`), which replaces the head variable — necessarily one of the `n` bound ones,
  since the term is closed — by a term that eats its `m` arguments and returns the identity;
* **`Lambda.solvable_iff_hasHnf`** — hence for closed terms solvability and head normalizability
  coincide, and **`GraphModel.denot_ne_empty_iff_solvable`** — both coincide with having a
  nonempty denotation: the least element of the graph model is exactly the unsolvable terms.

`Start/FreeVars.lean` collects what this needs about free variables: the structural helpers that
were previously proved inside `Start/BohmOut.lean` (now shared from here) together with
`Lambda.freeBelow_subst`, `Lambda.freeBelow_step`, `Lambda.freeBelow_reduces` and
`Lambda.IsClosed.reduces` — a reduct of a closed term is closed.

## Observational equivalence — `Start/GraphObs.lean`

* `Lambda.Ctx`, `Lambda.Ctx.fill` — one-hole contexts; `GraphModel.denot_fill_congr` —
  compositionality: a context sees a term only through its denotation;
* `Lambda.ObsEqHnf` — no context distinguishes the two terms by whether it head normalizes;
* **`GraphModel.obsEqHnf_of_denot_eq`** — denotational equality implies observational
  equivalence;
* `GraphModel.obsEqHnf_of_not_hasHnf`, `GraphModel.obsEqHnf_omega_app_omega_I` — in particular
  all head-divergent terms are observationally equivalent.

## Gates

* `lake build` — the whole library builds, with no `linter.*` warning;
* `python3 scripts/goal_state.py validate`;
* no `sorry` in the new modules; `#print axioms` on `GraphModel.hasHnf_of_mem_denot`,
  `GraphModel.denot_ne_empty_iff_hasHnf`, `GraphModel.hasHnf_of_solvable`,
  `Lambda.solvable_iff_hasHnf` and `GraphModel.denot_ne_empty_iff_solvable` reports only
  `propext`, `Classical.choice`, `Quot.sound`.

## Boundary

The results are for the **graph** model.  The corresponding statements for `D∞` are not claimed:
its interpretation is proved sound but no computability relation on the finite stages of the
tower is built (that is what `M9-DINF-ADEQUACY` still records).  **Full abstraction** — the
converse of `GraphModel.obsEqHnf_of_denot_eq` — is not claimed either; it is known to fail for
the continuous models.
