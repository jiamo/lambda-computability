# M9-DINF-ADEQUACY

**Status:** DONE_STRONG

Adequacy for the untyped models is proved: for the graph model in `M9-GRAPH-ADEQUACY`, and for
`D∞` in `Start/DinfAdequacy.lean`, which is what this task asked for.

## What is proved for `D∞` — `Start/DinfAdequacy.lean`

`M9-SCOTT-DINF` builds the inverse limit `D∞`, its isomorphism with its own function space and the
interpretation `ScottDinf.ddenot` of untyped lambda terms in it, and proves that interpretation
*sound* (β and η hold, `Omega` denotes the least element).  `M9-DINF-HNF` proves the easy converse:
a head normalizable term is somewhere different from the least element.  This file supplies the
missing half, by the classical computability argument carried out along the *tower*
`D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]`, the level of the tower being what makes the logical relation
well founded.

* **`ScottDinf.RelD n z t`** — the computability (logical-relations) predicate: the term `t`
  realizes the stage-`n` value `z`.  At level `0` a nonbottom value means that `t` head normalizes
  after being applied to any list of arguments; at level `n+1` it means that applying `t` to a
  realizer of `x` realizes `toFn z x`.  `ScottDinf.RealD` and `ScottDinf.Real` lift this to `D∞`,
  componentwise.
* **`ScottDinf.relD_emb`, `ScottDinf.relD_prj`** — the relation is compatible with the
  embedding–projection pairs of the tower, by simultaneous induction on the level; the stronger
  level-`0` clause (head normalization *after any number of arguments*) is exactly what makes the
  embedding case go through.
* **`ScottDinf.relD_ωSup`** — the relation is admissible, i.e. closed under suprema of chains,
  which is what the application map `Φ` — a supremum of finite-stage approximations — needs
  (`ScottDinf.realD_app`).
* **`ScottDinf.realD_substEnv`** — the fundamental lemma: if the terms of `σ` realize the values of
  `ρ`, then `t[σ]` realizes `⟦t⟧ρ`.  So the relation is preserved by the interpretation.
* **`ScottDinf.hasHnf_of_relD`** — a term realizing a nonbottom value has a head normal form.
* **`ScottDinf.hasHnf_of_ddenot_ne_botDinf`** — **adequacy**: a term whose denotation in `D∞` is
  not the least element, in any environment at all, has a head normal form.
* **`ScottDinf.exists_ddenot_ne_botDinf_iff_hasHnf`** — combined with `M9-DINF-HNF`: the denotation
  is the least element in every environment exactly when the term has no head normal form; and
  **`ScottDinf.ddenot_eq_botDinf_iff_not_solvable`** — for a closed term, exactly when it is
  unsolvable.
* **`ScottDinf.ddenot_fill_congr`** (compositionality) and
  **`ScottDinf.obsEqHnf_of_ddenot_eq`** — denotational equality implies observational equivalence
  at the level of head normalization.

## The graph model

`M9-GRAPH-ADEQUACY` carries out the same programme for Scott's **graph** model, where the finite
elements are the tokens themselves: `GraphModel.hasHnf_of_mem_denot`,
`GraphModel.denot_ne_empty_iff_hasHnf`, `GraphModel.denot_ne_empty_iff_solvable` and
`GraphModel.obsEqHnf_of_denot_eq`.  `Lambda.solvable_iff_hasHnf` records the syntactic half.

## Boundary

Empty for this task.  *Full abstraction* — the converse of the last item, that observationally
equivalent terms have equal denotations — is a separate question and is tracked by
`M9-UNTYPED-FULL-ABSTRACTION`; nothing here claims it.
