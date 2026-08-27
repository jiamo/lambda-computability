/-
Observational equivalence from adequacy.

`Start/GraphAdequacy.lean` shows that in Scott's graph model a term has a nonempty denotation
exactly when it has a head normal form.  This file draws the standard consequence: the model is
*adequate*, so denotational equality is an observational equivalence.

* `Lambda.Ctx`, `Lambda.Ctx.fill` — one-hole term contexts and hole filling;
* `GraphModel.denot_fill_congr` — compositionality: contexts see a term only through its
  denotation;
* `Lambda.ObsEqHnf` — observational equivalence at the level of head normalization: no context
  distinguishes the two terms by whether it head normalizes;
* `GraphModel.obsEqHnf_of_denot_eq` — **denotational equality implies observational
  equivalence**;
* `GraphModel.obsEqHnf_of_not_hasHnf` — in particular all head-divergent terms are
  observationally equivalent, `Ω` and `Ω I` for instance
  (`GraphModel.obsEqHnf_omega_app_omega_I`).

The converse inclusion — full abstraction — is *not* claimed: it is known to fail for the
continuous models.
-/

import Start.GraphAdequacy

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- One-hole contexts over the untyped terms. -/
inductive Ctx : Type
  | hole : Ctx
  | appL : Ctx → Lambda → Ctx
  | appR : Lambda → Ctx → Ctx
  | lam : Ctx → Ctx

/-- Filling the hole of a context with a term. -/
def Ctx.fill : Ctx → Lambda → Lambda
  | Ctx.hole, t => t
  | Ctx.appL C s, t => Lambda.app (C.fill t) s
  | Ctx.appR s C, t => Lambda.app s (C.fill t)
  | Ctx.lam C, t => Lambda.lam (C.fill t)

/-- Two terms are *observationally equivalent at head normalization* when no context
distinguishes them by whether it has a head normal form. -/
def ObsEqHnf (M N : Lambda) : Prop := ∀ C : Ctx, HasHnf (C.fill M) ↔ HasHnf (C.fill N)

theorem ObsEqHnf.refl (M : Lambda) : ObsEqHnf M M := fun _ => Iff.rfl

theorem ObsEqHnf.symm {M N : Lambda} (h : ObsEqHnf M N) : ObsEqHnf N M := fun C => (h C).symm

theorem ObsEqHnf.trans {M N P : Lambda} (h₁ : ObsEqHnf M N) (h₂ : ObsEqHnf N P) :
    ObsEqHnf M P := fun C => (h₁ C).trans (h₂ C)

end Lambda

namespace GraphModel

open Lambda

/-- **Compositionality**: a context only sees the denotation of the term in its hole. -/
theorem denot_fill_congr {M N : Lambda} (h : ∀ ρ : Env, denot M ρ = denot N ρ) :
    ∀ (C : Ctx) (ρ : Env), denot (C.fill M) ρ = denot (C.fill N) ρ := by
  intro C
  induction C with
  | hole => exact h
  | appL C s ih => intro ρ; simp only [Ctx.fill, denot_app, ih ρ]
  | appR s C ih => intro ρ; simp only [Ctx.fill, denot_app, ih ρ]
  | lam C ih => intro ρ; exact graph_congr fun X => ih (cons X ρ)

/-- **Adequacy gives observational equivalence**: terms with the same denotation in every
environment are indistinguishable by contexts, as far as head normalization is concerned. -/
theorem obsEqHnf_of_denot_eq {M N : Lambda} (h : ∀ ρ : Env, denot M ρ = denot N ρ) :
    ObsEqHnf M N := by
  have key : ∀ (M N : Lambda), (∀ ρ : Env, denot M ρ = denot N ρ) → ∀ C : Ctx,
      HasHnf (C.fill M) → HasHnf (C.fill N) := by
    intro M N h C hM
    obtain ⟨ρ, hρ⟩ := exists_denot_ne_empty_of_hasHnf hM
    refine hasHnf_of_denot_ne_empty (ρ := ρ) ?_
    rw [← denot_fill_congr h C ρ]
    exact hρ
  exact fun C => ⟨key M N h C, key N M (fun ρ => (h ρ).symm) C⟩

/-- All head-divergent terms are observationally equivalent: the model sends them all to the
least element. -/
theorem obsEqHnf_of_not_hasHnf {M N : Lambda} (hM : ¬ HasHnf M) (hN : ¬ HasHnf N) :
    ObsEqHnf M N :=
  obsEqHnf_of_denot_eq fun ρ => by
    rw [denot_eq_empty_of_not_hasHnf hM ρ, denot_eq_empty_of_not_hasHnf hN ρ]

/-- `Ω` and `Ω I` are observationally equivalent, although they are not convertible. -/
theorem obsEqHnf_omega_app_omega_I :
    ObsEqHnf Lambda.omega (Lambda.app Lambda.omega Lambda.I) := by
  refine obsEqHnf_of_not_hasHnf not_hasHnf_omega ?_
  intro h
  obtain ⟨ρ, hρ⟩ := exists_denot_ne_empty_of_hasHnf h
  refine hρ ?_
  rw [denot_app, denot_omega]
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, -, hb⟩
  exact hb

end GraphModel
