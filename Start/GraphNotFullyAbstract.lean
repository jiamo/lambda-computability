/-
**Scott's graph model is not fully abstract.**

`Start/GraphObs.lean` proves the easy half of full abstraction for the graph model: terms with
the same denotation are observationally equivalent at head normalization
(`GraphModel.obsEqHnf_of_denot_eq`).  This file settles the converse, negatively: there are two
*closed* terms which no context distinguishes, but whose graph-model denotations differ.

The witnesses are the identity and its eta-expansion,

* `GraphNotFullyAbstract.idTm  = λx. x`,
* `GraphNotFullyAbstract.etaTm = λx. λy. x y`.

They are separated by the graph model because it is not extensional
(`GraphNotFullyAbstract.denot_idTm_ne_denot_etaTm`: the token `[atom 0] ⇒ atom 0` belongs to the
denotation of the identity but not to that of its eta-expansion, whose elements are all step
functions producing step functions).  They are *not* separated by any context, because Scott's
`D∞` does validate eta (`ScottDinf.ddenot_eta`) and is adequate
(`ScottDinf.obsEqHnf_of_ddenot_eq`), so the two terms are observationally equivalent.

* `GraphNotFullyAbstract.obsEqHnf_idTm_etaTm` — no context distinguishes them;
* `GraphNotFullyAbstract.graph_not_fully_abstract` — **the graph model is not fully abstract**:
  observational equivalence does not imply equality of denotations, even for closed terms;
* `GraphNotFullyAbstract.dinf_identifies_more_than_graph` — the same pair shows that `D∞`
  identifies strictly more terms than the graph model does.

So the two untyped models of this development are genuinely different: the inclusion of
denotational into observational equality proved in `Start/GraphObs.lean` is strict.
-/

import Start.DinfAdequacy

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace GraphNotFullyAbstract

open Lambda GraphModel ScottDinf

/-- The identity `λx. x`. -/
def idTm : Lambda := Lambda.lam (Lambda.var 0)

/-- Its eta-expansion `λx. λy. x y`. -/
def etaTm : Lambda := Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.var 0)))

theorem idTm_isClosed : Lambda.IsClosed idTm := by
  intro s x
  simp [idTm, Lambda.subst]

theorem etaTm_isClosed : Lambda.IsClosed etaTm := by
  intro s x
  simp [etaTm, Lambda.subst]

/-! ### `D∞` identifies the two terms -/

/-- In `D∞` the eta-expansion has the same denotation as the identity, in every environment. -/
theorem ddenot_etaTm (ρ : DEnv) : ddenot etaTm ρ = ddenot idTm ρ := by
  rw [etaTm, idTm, ddenot_lam, ddenot_lam]
  refine dlamAny_congr fun X => ?_
  exact ddenot_eta (Lambda.var 0) (dcons X ρ)

/-- **No context distinguishes the identity from its eta-expansion**, as far as head
normalization is concerned: `D∞` is adequate and validates eta. -/
theorem obsEqHnf_idTm_etaTm : Lambda.ObsEqHnf idTm etaTm :=
  ScottDinf.obsEqHnf_of_ddenot_eq fun ρ => (ddenot_etaTm ρ).symm

/-! ### The graph model separates them -/

/-- The token `[atom 0] ⇒ atom 0` is in the denotation of the identity. -/
theorem tok_mem_denot_idTm (ρ : Env) :
    Tok.arrow [Tok.atom 0] (Tok.atom 0) ∈ denot idTm ρ := by
  rw [idTm, denot_lam]
  exact mem_graph.2 (by simp [lset])

/-- It is not in the denotation of the eta-expansion: every token there is a step function
producing a step function, never an atom. -/
theorem tok_notMem_denot_etaTm (ρ : Env) :
    Tok.arrow [Tok.atom 0] (Tok.atom 0) ∉ denot etaTm ρ := by
  rw [etaTm, denot_lam]
  intro h
  have h' := mem_graph.1 h
  rw [denot_lam] at h'
  exact atom_notMem_graph h'

/-- **The graph model is not extensional**: the identity and its eta-expansion have different
denotations. -/
theorem denot_idTm_ne_denot_etaTm (ρ : Env) : denot idTm ρ ≠ denot etaTm ρ := by
  intro h
  exact tok_notMem_denot_etaTm ρ (h ▸ tok_mem_denot_idTm ρ)

/-- **Scott's graph model is not fully abstract**: there are closed terms that no context
distinguishes by head normalization, yet whose denotations differ in every environment. -/
theorem graph_not_fully_abstract :
    ∃ M N : Lambda, Lambda.IsClosed M ∧ Lambda.IsClosed N ∧ Lambda.ObsEqHnf M N ∧
      ∀ ρ : Env, denot M ρ ≠ denot N ρ :=
  ⟨idTm, etaTm, idTm_isClosed, etaTm_isClosed, obsEqHnf_idTm_etaTm, denot_idTm_ne_denot_etaTm⟩

/-- **`D∞` identifies strictly more terms than the graph model**: the eta rule holds in the
inverse limit and fails in the graph model. -/
theorem dinf_identifies_more_than_graph :
    ∃ M N : Lambda, Lambda.IsClosed M ∧ Lambda.IsClosed N ∧
      (∀ ρ : DEnv, ddenot M ρ = ddenot N ρ) ∧ (∀ ρ : Env, denot M ρ ≠ denot N ρ) :=
  ⟨idTm, etaTm, idTm_isClosed, etaTm_isClosed, fun ρ => (ddenot_etaTm ρ).symm,
    denot_idTm_ne_denot_etaTm⟩

end GraphNotFullyAbstract

end
