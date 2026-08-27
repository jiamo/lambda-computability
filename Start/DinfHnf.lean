/-
Head normal forms have a nonbottom denotation in `D∞`.

`Start/ScottDinfModel.lean` interprets terms in Scott's inverse limit `D∞`, and
`Start/GraphAdequacy.lean` proves adequacy for the graph model: a term has a head normal form
exactly when its denotation there is nonempty.  This file proves the *easy* half of the
corresponding statement for `D∞`: every head normalizable term has an environment in which its
denotation is different from the least element `⊥`.

The construction is uniform.  For a neutral term `y M₁ … Mₘ` one picks for `y` the element
`λ_ … λ_. z` that ignores `m` arguments and returns a prescribed value `z`
(`ScottDinf.exists_const_env_ddenot_neutral`); since that element ignores its arguments, the
same constant environment can be reused underneath the abstraction prefix of a head normal
form, the abstraction case being handled by `ScottDinf.dlamAny_ne_botDinf`.

Main results:

* `ScottDinf.Phi_botDinf`                        — `⊥` denotes the everywhere-`⊥` function;
* `ScottDinf.exists_const_env_ddenot_neutral`    — a neutral term takes any prescribed value in
  a suitable constant environment;
* `ScottDinf.exists_ddenot_ne_botDinf_of_isHnf`  — a head normal form is nonbottom somewhere;
* `ScottDinf.exists_ddenot_ne_botDinf_of_hasHnf` — and so is a head normalizable term;
* `ScottDinf.not_hasHnf_of_ddenot_eq_botDinf`    — contrapositive: a term whose denotation is
  always `⊥` has no head normal form;
* `ScottDinf.exists_ddenot_ne_botDinf_of_solvable` — solvable terms are nonbottom somewhere.
-/

import Start.ScottDinfModel
import Start.HnfSolvable

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

------------------------------------------------------------------------
-- Bottom and abstraction
------------------------------------------------------------------------

/-- The bottom element of `D∞` denotes the function that is everywhere `⊥`. -/
theorem Phi_botDinf (y : Dinf) : Phi Dinf.botDinf y = Dinf.botDinf := by
  refine le_antisymm ?_ (Dinf.botDinf_le _)
  have h : Phi Dinf.botDinf ≤ ContinuousHom.const Dinf.botDinf :=
    Phi_le_iff.mpr (Dinf.botDinf_le _)
  exact h y

/-- `D∞` has an element other than `⊥`. -/
theorem exists_ne_botDinf : ∃ c : Dinf, c ≠ Dinf.botDinf := by
  refine ⟨psiFun 0 true, ?_⟩
  intro h
  have h0 : (true : D 0) = botD 0 := by
    rw [← psiFun_app_self 0 true, h, Dinf.botDinf_app]
  exact Bool.noConfusion h0

/-- An abstraction is nonbottom as soon as its body is nonbottom at some argument. -/
theorem dlamAny_ne_botDinf {g : Dinf → Dinf} (hg : ωScottContinuous g) {y : Dinf}
    (hy : g y ≠ Dinf.botDinf) : dlamAny g ≠ Dinf.botDinf := by
  intro h
  apply hy
  rw [← Phi_dlamAny hg y, h, Phi_botDinf]

------------------------------------------------------------------------
-- Neutral terms and head normal forms
------------------------------------------------------------------------

/-- The constant environment with value `A`. -/
def constEnv (A : Dinf) : DEnv := fun _ => A

@[simp] theorem constEnv_apply (A : Dinf) (i : ℕ) : constEnv A i = A := rfl

@[simp] theorem dcons_constEnv (A : Dinf) : dcons A (constEnv A) = constEnv A := by
  funext i
  cases i with
  | zero => rfl
  | succ j => rfl

/-- A neutral term `y M₁ … Mₘ` takes any prescribed value in a suitable constant environment:
interpret its head as the element that discards `m` arguments and returns that value. -/
theorem exists_const_env_ddenot_neutral {t : Lambda} (h : Lambda.Neutral t) :
    ∀ z : Dinf, ∃ A : Dinf, ddenot t (constEnv A) = z := by
  induction h with
  | var n => exact fun z => ⟨z, rfl⟩
  | app N _ ih =>
      intro z
      obtain ⟨A, hA⟩ := ih (dlamAny (fun _ => z))
      refine ⟨A, ?_⟩
      rw [ddenot_app, hA]
      exact Phi_dlamAny (g := fun _ => z) ωScottContinuous.const _

/-- **A head normal form is nonbottom in a suitable environment.** -/
theorem exists_ddenot_ne_botDinf_of_isHnf {t : Lambda} (h : Lambda.IsHnf t) :
    ∃ A : Dinf, ddenot t (constEnv A) ≠ Dinf.botDinf := by
  induction h with
  | neutral hn =>
      obtain ⟨c, hc⟩ := exists_ne_botDinf
      obtain ⟨A, hA⟩ := exists_const_env_ddenot_neutral hn c
      exact ⟨A, by rw [hA]; exact hc⟩
  | @lam s _ ih =>
      obtain ⟨A, hA⟩ := ih
      refine ⟨A, ?_⟩
      rw [ddenot_lam]
      refine dlamAny_ne_botDinf (ddenot_cons_cont s (constEnv A)) (y := A) ?_
      rwa [dcons_constEnv]

/-- **A head normalizable term is nonbottom in a suitable environment.** -/
theorem exists_ddenot_ne_botDinf_of_hasHnf {t : Lambda} (h : Lambda.HasHnf t) :
    ∃ ρ : DEnv, ddenot t ρ ≠ Dinf.botDinf := by
  obtain ⟨u, hu, hhnf⟩ := h
  obtain ⟨A, hA⟩ := exists_ddenot_ne_botDinf_of_isHnf hhnf
  exact ⟨constEnv A, by rwa [ddenot_reduces hu]⟩

/-- Contrapositive: a term that is `⊥` in every environment has no head normal form. -/
theorem not_hasHnf_of_ddenot_eq_botDinf {t : Lambda}
    (h : ∀ ρ : DEnv, ddenot t ρ = Dinf.botDinf) : ¬ Lambda.HasHnf t := by
  intro hhnf
  obtain ⟨ρ, hρ⟩ := exists_ddenot_ne_botDinf_of_hasHnf hhnf
  exact hρ (h ρ)

/-- A solvable term is nonbottom in a suitable environment. -/
theorem exists_ddenot_ne_botDinf_of_solvable {t : Lambda} (h : Lambda.Solvable t) :
    ∃ ρ : DEnv, ddenot t ρ ≠ Dinf.botDinf :=
  exists_ddenot_ne_botDinf_of_hasHnf (GraphModel.hasHnf_of_solvable h)

/-- A term that is `⊥` in every environment is unsolvable. -/
theorem not_solvable_of_ddenot_eq_botDinf {t : Lambda}
    (h : ∀ ρ : DEnv, ddenot t ρ = Dinf.botDinf) : ¬ Lambda.Solvable t := by
  intro hs
  obtain ⟨ρ, hρ⟩ := exists_ddenot_ne_botDinf_of_solvable hs
  exact hρ (h ρ)

end

end ScottDinf
