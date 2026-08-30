/-
The lattice of λ-theories, and the place of the two models in it.

A **λ-theory** is a congruence on the untyped terms that contains β-conversion: an equational
theory of the λ-calculus.  This file introduces them (`Lambda.LambdaTheory`), exhibits the four
that this development has the material to define, and orders them.

* `Lambda.LambdaTheory.beta` — pure β-conversion, the least λ-theory (`B`);
* `Lambda.LambdaTheory.graph` — the theory of Scott's graph model, `Th(𝒫ω)`;
* `Lambda.LambdaTheory.dinf` — the theory of Scott's inverse limit, `Th(D∞)`;
* `Lambda.LambdaTheory.hstar` — observational equivalence at head normalisation, `H*`.

The comparisons are made on **closed** terms (`Lambda.LambdaTheory.LeClosed`), which is where the
observational theory is defined, and the result is the classical picture

    B  ⊊  Th(𝒫ω)  ⊊  Th(D∞)  =  H* .

* `Lambda.LambdaTheory.beta_lt_graph` — the first inclusion is strict: the graph model equates
  the two unsolvable terms `Ω` and `Ω I`, which are not β-convertible
  (`Lambda.not_conv_omega_app_omega_I`).  So the graph model is a *nontrivial* λ-theory, not just
  a restatement of conversion.
* `Lambda.LambdaTheory.graph_lt_dinf` — the second inclusion is strict: `D∞` validates η and the
  graph model does not, so `λx. x` and `λx λy. x y` are equated by one and separated by the
  other (`Start/GraphNotFullyAbstract.lean`).
* `Lambda.LambdaTheory.dinf_eq_hstar_closed` — **`Th(D∞) = H*`**, a restatement of Wadsworth's
  theorem `ScottDinf.obsEqHnf_iff_ddenot_eq`.

`Lambda.LambdaTheory.theory_chain` packages the whole picture as one statement.
-/

import Start.DinfTagBelowSound
import Start.GraphNotFullyAbstract
import Start.Solvability

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ### Contexts compose, and reduction is a congruence for them -/

/-- Composition of one-hole contexts: `(C.comp D).fill t = C.fill (D.fill t)`. -/
def Ctx.comp : Ctx → Ctx → Ctx
  | Ctx.hole, D => D
  | Ctx.appL C s, D => Ctx.appL (C.comp D) s
  | Ctx.appR s C, D => Ctx.appR s (C.comp D)
  | Ctx.lam C, D => Ctx.lam (C.comp D)

@[simp] theorem Ctx.fill_comp (C D : Ctx) (t : Lambda) :
    (C.comp D).fill t = C.fill (D.fill t) := by
  induction C with
  | hole => rfl
  | appL C s ih => simp [Ctx.comp, Ctx.fill, ih]
  | appR s C ih => simp [Ctx.comp, Ctx.fill, ih]
  | lam C ih => simp [Ctx.comp, Ctx.fill, ih]

theorem reduces_fill {M N : Lambda} (h : Lambda.reduces M N) :
    ∀ C : Ctx, Lambda.reduces (C.fill M) (C.fill N) := by
  intro C
  induction C with
  | hole => exact h
  | appL C s ih => exact Lambda.reduces_app_left ih
  | appR s C ih => exact Lambda.reduces_app_right ih
  | lam C ih => exact Lambda.reduces_lam ih

theorem Conv.fill {M N : Lambda} (h : Conv M N) (C : Ctx) : Conv (C.fill M) (C.fill N) := by
  obtain ⟨u, h₁, h₂⟩ := h
  exact ⟨C.fill u, reduces_fill h₁ C, reduces_fill h₂ C⟩

/-- Observational equivalence is a congruence: it is defined by quantifying over contexts, and
contexts compose. -/
theorem ObsEqHnf.fill {M N : Lambda} (h : ObsEqHnf M N) (D : Ctx) :
    ObsEqHnf (D.fill M) (D.fill N) := by
  intro C
  simpa using h (C.comp D)

/-! ### λ-theories -/

/-- A **λ-theory**: an equivalence relation on the untyped terms which contains β-conversion and
is a congruence, that is, closed under filling a one-hole context. -/
structure LambdaTheory where
  /-- The equational relation of the theory. -/
  Rel : Lambda → Lambda → Prop
  /-- Every λ-theory contains β-conversion. -/
  conv : ∀ {M N : Lambda}, Conv M N → Rel M N
  /-- Symmetry. -/
  symm : ∀ {M N : Lambda}, Rel M N → Rel N M
  /-- Transitivity. -/
  trans : ∀ {M N P : Lambda}, Rel M N → Rel N P → Rel M P
  /-- Congruence: the relation is preserved by every one-hole context. -/
  congr : ∀ {M N : Lambda} (C : Ctx), Rel M N → Rel (C.fill M) (C.fill N)

namespace LambdaTheory

theorem refl (T : LambdaTheory) (M : Lambda) : T.Rel M M := T.conv (conv_refl M)

/-- Inclusion of λ-theories, on closed terms: the observational theory only makes sense there,
so this is where the classical chain is stated. -/
def LeClosed (T U : LambdaTheory) : Prop :=
  ∀ M N : Lambda, IsClosed M → IsClosed N → T.Rel M N → U.Rel M N

/-- Strict inclusion of λ-theories on closed terms. -/
def LtClosed (T U : LambdaTheory) : Prop := LeClosed T U ∧ ¬ LeClosed U T

theorem LeClosed.refl (T : LambdaTheory) : LeClosed T T := fun _ _ _ _ h => h

theorem LeClosed.trans {T U V : LambdaTheory} (h₁ : LeClosed T U) (h₂ : LeClosed U V) :
    LeClosed T V := fun M N hM hN h => h₂ M N hM hN (h₁ M N hM hN h)

/-! ### The four theories -/

/-- `B`, the theory of pure β-conversion: the least λ-theory. -/
def beta : LambdaTheory where
  Rel := Conv
  conv h := h
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂
  congr C h := h.fill C

/-- `B` is the least λ-theory. -/
theorem beta_le (T : LambdaTheory) : LeClosed beta T := fun _ _ _ _ h => T.conv h

/-- `Th(𝒫ω)`, the theory of Scott's graph model. -/
def graph : LambdaTheory where
  Rel M N := ∀ ρ : GraphModel.Env, GraphModel.denot M ρ = GraphModel.denot N ρ
  conv h := fun ρ => GraphModel.denot_conv h ρ
  symm h := fun ρ => (h ρ).symm
  trans h₁ h₂ := fun ρ => (h₁ ρ).trans (h₂ ρ)
  congr C h := GraphModel.denot_fill_congr h C

/-- `Th(D∞)`, the theory of Scott's inverse limit. -/
def dinf : LambdaTheory where
  Rel M N := ∀ ρ : ScottDinf.DEnv, ScottDinf.ddenot M ρ = ScottDinf.ddenot N ρ
  conv h := fun ρ => ScottDinf.ddenot_conv h ρ
  symm h := fun ρ => (h ρ).symm
  trans h₁ h₂ := fun ρ => (h₁ ρ).trans (h₂ ρ)
  congr C h := ScottDinf.ddenot_fill_congr h C

/-- `H*`, observational equivalence at head normalisation: the maximal consistent sensible
theory. -/
def hstar : LambdaTheory where
  Rel := ObsEqHnf
  conv h := GraphModel.obsEqHnf_of_denot_eq fun ρ => GraphModel.denot_conv h ρ
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂
  congr C h := h.fill C

/-! ### `Ω` and `Ω I`: the graph model is strictly above `B` -/

theorem step_omega_app_I_eq {u : Lambda}
    (h : Lambda.step (Lambda.app Lambda.omega Lambda.I) u) :
    u = Lambda.app Lambda.omega Lambda.I := by
  cases h with
  | app_left _ t₁' _ hs => rw [Lambda.step_omega_eq _ hs]
  | app_right _ _ t₂' hs => exact absurd hs (is_normal_I t₂')

theorem reduces_omega_app_I_eq : ∀ {s u : Lambda}, Lambda.reduces s u →
    s = Lambda.app Lambda.omega Lambda.I → u = Lambda.app Lambda.omega Lambda.I := by
  intro s u h
  induction h with
  | refl t => exact fun ht => ht
  | step a b c hab _ ih => exact fun ha => ih (step_omega_app_I_eq (ha ▸ hab))

/-- `Ω` and `Ω I` are **not** β-convertible: each of them reduces only to itself. -/
theorem not_conv_omega_app_omega_I : ¬ Conv Lambda.omega (Lambda.app Lambda.omega Lambda.I) := by
  rintro ⟨u, h₁, h₂⟩
  have e₁ : u = Lambda.omega := reduces_omega_eq h₁ rfl
  have e₂ : u = Lambda.app Lambda.omega Lambda.I := reduces_omega_app_I_eq h₂ rfl
  rw [e₁] at e₂
  simp [Lambda.omega, Lambda.I] at e₂

theorem app_omega_I_closed : IsClosed (Lambda.app Lambda.omega Lambda.I) := by
  intro s x
  simp [Lambda.omega, Lambda.I, Lambda.subst]

/-- Both terms are unsolvable, so the graph model sends them to the empty denotation. -/
theorem graph_omega_app_omega_I : graph.Rel Lambda.omega (Lambda.app Lambda.omega Lambda.I) := by
  intro ρ
  rw [GraphModel.denot_omega, GraphModel.denot_app, GraphModel.denot_omega]
  ext b
  simp only [Set.mem_empty_iff_false, false_iff]
  rintro ⟨a, -, hb⟩
  exact hb

/-! ### The chain -/

theorem beta_le_graph : LeClosed beta graph := beta_le graph

/-- **The first inclusion is strict**: the graph model identifies the unsolvable terms `Ω` and
`Ω I`, which β-conversion does not. -/
theorem beta_lt_graph : LtClosed beta graph := by
  refine ⟨beta_le_graph, fun h => ?_⟩
  exact not_conv_omega_app_omega_I
    (h Lambda.omega (Lambda.app Lambda.omega Lambda.I) omega_closed app_omega_I_closed
      graph_omega_app_omega_I)

/-- Every closed pair identified by the graph model is identified by `D∞`: the graph model is
adequate, and `D∞` is fully abstract. -/
theorem graph_le_dinf : LeClosed graph dinf := by
  intro M N hM hN h
  exact (ScottDinf.obsEqHnf_iff_ddenot_eq hM hN).1 (GraphModel.obsEqHnf_of_denot_eq h)

/-- **The second inclusion is strict**: `D∞` validates η and the graph model does not. -/
theorem graph_lt_dinf : LtClosed graph dinf := by
  refine ⟨graph_le_dinf, fun h => ?_⟩
  obtain ⟨M, N, hM, hN, hd, hg⟩ := GraphNotFullyAbstract.dinf_identifies_more_than_graph
  exact hg (fun _ => (∅ : GraphModel.D)) (h M N hM hN hd (fun _ => (∅ : GraphModel.D)))

/-- **`Th(D∞) = H*`** — Wadsworth's theorem, read as an identity of λ-theories on closed
terms. -/
theorem dinf_eq_hstar_closed {M N : Lambda} (hM : IsClosed M) (hN : IsClosed N) :
    dinf.Rel M N ↔ hstar.Rel M N :=
  (ScottDinf.obsEqHnf_iff_ddenot_eq hM hN).symm

theorem dinf_le_hstar : LeClosed dinf hstar :=
  fun _ _ hM hN h => (dinf_eq_hstar_closed hM hN).1 h

theorem hstar_le_dinf : LeClosed hstar dinf :=
  fun _ _ hM hN h => (dinf_eq_hstar_closed hM hN).2 h

/-- **The classical picture**: `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*`. -/
theorem theory_chain :
    LtClosed beta graph ∧ LtClosed graph dinf ∧ LeClosed dinf hstar ∧ LeClosed hstar dinf :=
  ⟨beta_lt_graph, graph_lt_dinf, dinf_le_hstar, hstar_le_dinf⟩

end LambdaTheory

end Lambda

end
