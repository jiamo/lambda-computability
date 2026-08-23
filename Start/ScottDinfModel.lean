/-
Scott's `D∞`, step five: `D∞` as a model of the untyped lambda calculus.

`Start/ScottDinfIso.lean` builds the isomorphism `Φ : D∞ ≃o [D∞ →𝒄 D∞]`.  This file uses it
to interpret de Bruijn terms and proves that the interpretation is a model of the
**beta-eta** calculus (unlike the graph model, `D∞` is extensional).

Main results:

* `ScottDinf.ddenot`        — the interpretation `⟦t⟧ρ : D∞` of a term in an environment;
* `ScottDinf.ddenot_cont`   — the interpretation is Scott continuous in the environment;
* `ScottDinf.ddenot_beta`   — the semantic beta rule;
* `ScottDinf.ddenot_step`, `ScottDinf.ddenot_reduces`, `ScottDinf.ddenot_conv` — soundness;
* `ScottDinf.ddenot_eta`    — the semantic eta rule, valid because `D∞` is extensional.
-/

import Start.ScottDinfIso
import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

/-- Environments assign an element of `D∞` to every de Bruijn index. -/
abbrev DEnv : Type := ℕ → Dinf

/-- Extend an environment with a new value for index `0`. -/
def dcons (X : Dinf) (ρ : DEnv) : DEnv := fun i =>
  match i with
  | 0 => X
  | (j + 1) => ρ j

@[simp] theorem dcons_zero (X : Dinf) (ρ : DEnv) : dcons X ρ 0 = X := rfl
@[simp] theorem dcons_succ (X : Dinf) (ρ : DEnv) (j : ℕ) : dcons X ρ (j + 1) = ρ j := rfl

theorem ωScottContinuous_dcons_left (ρ : DEnv) :
    ωScottContinuous (fun X : Dinf => dcons X ρ) := by
  refine ωScottContinuous.of_apply₂ ?_
  intro i
  cases i with
  | zero => exact ωScottContinuous.id
  | succ j => exact ωScottContinuous.const

theorem ωScottContinuous_dcons_right (X : Dinf) :
    ωScottContinuous (fun ρ : DEnv => dcons X ρ) := by
  refine ωScottContinuous.of_apply₂ ?_
  intro i
  cases i with
  | zero => exact ωScottContinuous.const
  | succ j => exact ωScottContinuous.apply j

/-- A family of continuous maps is continuous as soon as it is continuous pointwise. -/
theorem ωScottContinuous_hom {A : Type} [OmegaCompletePartialOrder A]
    (F : A → (Dinf →𝒄 Dinf)) (h : ∀ y : Dinf, ωScottContinuous (fun a => F a y)) :
    ωScottContinuous F := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ hab y => (h y).monotone hab, fun c => ?_⟩
  refine DFunLike.ext _ _ fun y => ?_
  rw [(h y).map_ωSup c, ωSup_hom_apply]
  exact le_antisymm (ωSup_le _ _ fun i => le_ωSup_of_le i (le_refl _))
    (ωSup_le _ _ fun i => le_ωSup_of_le i (le_refl _))

------------------------------------------------------------------------
-- Abstraction of an arbitrary function
------------------------------------------------------------------------

open Classical in
/-- Abstraction, totalised: on a continuous function it is `Ψ`, elsewhere it is junk.  This
lets the interpretation of terms be defined by plain structural recursion, the continuity
being established afterwards. -/
def dlamAny (g : Dinf → Dinf) : Dinf :=
  if h : ωScottContinuous g then Psi (ContinuousHom.ofFun g h) else Dinf.botDinf

theorem dlamAny_eq {g : Dinf → Dinf} (h : ωScottContinuous g) :
    dlamAny g = Psi (ContinuousHom.ofFun g h) := dif_pos h

theorem dlamAny_congr {g g' : Dinf → Dinf} (h : ∀ X, g X = g' X) : dlamAny g = dlamAny g' :=
  congrArg dlamAny (funext h)

/-- The beta rule for the totalised abstraction. -/
theorem Phi_dlamAny {g : Dinf → Dinf} (h : ωScottContinuous g) (y : Dinf) :
    Phi (dlamAny g) y = g y := by
  rw [dlamAny_eq h, Phi_Psi]
  rfl

/-- The eta rule: `D∞` is extensional. -/
theorem dlamAny_Phi (x : Dinf) : dlamAny (fun y => Phi x y) = x := by
  have h : ωScottContinuous (fun y => Phi x y) := (Phi x).ωScottContinuous
  rw [dlamAny_eq h]
  have hx : ContinuousHom.ofFun (fun y => Phi x y) h = Phi x := rfl
  rw [hx, Psi_Phi]

------------------------------------------------------------------------
-- The interpretation
------------------------------------------------------------------------

/-- The interpretation of a lambda term in an environment of `D∞`. -/
def ddenot : Lambda → DEnv → Dinf
  | Lambda.var i, ρ => ρ i
  | Lambda.app s t, ρ => Phi (ddenot s ρ) (ddenot t ρ)
  | Lambda.lam s, ρ => dlamAny (fun X => ddenot s (dcons X ρ))

@[simp] theorem ddenot_var (i : ℕ) (ρ : DEnv) : ddenot (Lambda.var i) ρ = ρ i := rfl
@[simp] theorem ddenot_app (s t : Lambda) (ρ : DEnv) :
    ddenot (Lambda.app s t) ρ = Phi (ddenot s ρ) (ddenot t ρ) := rfl
@[simp] theorem ddenot_lam (s : Lambda) (ρ : DEnv) :
    ddenot (Lambda.lam s) ρ = dlamAny (fun X => ddenot s (dcons X ρ)) := rfl

/-- **The interpretation is Scott continuous in the environment.** -/
theorem ddenot_cont : ∀ t : Lambda, ωScottContinuous (fun ρ : DEnv => ddenot t ρ) := by
  intro t
  induction t with
  | var i => exact ωScottContinuous.apply i
  | app s u ihs ihu =>
      exact ContinuousHom.ωScottContinuous_apply (Phi_continuous.comp ihs) ihu
  | lam s ih =>
      have hin : ∀ ρ : DEnv, ωScottContinuous (fun X : Dinf => ddenot s (dcons X ρ)) :=
        fun ρ => ih.comp (ωScottContinuous_dcons_left ρ)
      have hF : ωScottContinuous (fun ρ : DEnv =>
          ContinuousHom.ofFun (fun X => ddenot s (dcons X ρ)) (hin ρ)) := by
        refine ωScottContinuous_hom _ ?_
        intro y
        exact ih.comp (ωScottContinuous_dcons_right y)
      have heq : (fun ρ : DEnv => ddenot (Lambda.lam s) ρ)
          = fun ρ => Psi (ContinuousHom.ofFun (fun X => ddenot s (dcons X ρ)) (hin ρ)) := by
        funext ρ
        rw [ddenot_lam]
        exact dlamAny_eq (hin ρ)
      rw [heq]
      exact Psi_continuous.comp hF

/-- Continuity of the interpretation in the variable bound by a lambda. -/
theorem ddenot_cons_cont (t : Lambda) (ρ : DEnv) :
    ωScottContinuous (fun X : Dinf => ddenot t (dcons X ρ)) :=
  (ddenot_cont t).comp (ωScottContinuous_dcons_left ρ)

theorem ddenot_mono (t : Lambda) {ρ ρ' : DEnv} (h : ∀ i, ρ i ≤ ρ' i) :
    ddenot t ρ ≤ ddenot t ρ' := (ddenot_cont t).monotone h

/-- Semantic application of an abstraction. -/
theorem ddenot_lam_apply (s : Lambda) (ρ : DEnv) (X : Dinf) :
    Phi (ddenot (Lambda.lam s) ρ) X = ddenot s (dcons X ρ) := by
  rw [ddenot_lam]
  exact Phi_dlamAny (ddenot_cons_cont s ρ) X

------------------------------------------------------------------------
-- Lifting and substitution
------------------------------------------------------------------------

theorem ddenot_lift (t : Lambda) (n k : ℕ) (ρ : DEnv) :
    ddenot (Lambda.lift n k t) ρ = ddenot t (fun i => if i < k then ρ i else ρ (i + n)) := by
  induction t generalizing k ρ with
  | var y => by_cases hy : y < k <;> simp [Lambda.lift, hy]
  | app s u ihs ihu => simp [Lambda.lift, ihs, ihu]
  | lam s ih =>
      simp only [Lambda.lift, ddenot_lam]
      refine dlamAny_congr ?_
      intro X
      rw [ih]
      congr 1
      funext i
      cases i with
      | zero => simp
      | succ j =>
          by_cases hj : j < k
          · have hj1 : j + 1 < k + 1 := by omega
            simp [hj1, hj]
          · have h1 : ¬ (j + 1 < k + 1) := by omega
            have h2 : j + 1 + n = (j + n) + 1 := by omega
            simp [h1, hj, h2]

theorem ddenot_subst (t : Lambda) : ∀ (s : Lambda) (x : ℕ) (ρ : DEnv),
    ddenot (Lambda.subst s x t) ρ =
      ddenot t (fun i => if i = x then ddenot s ρ else if x < i then ρ (i - 1) else ρ i) := by
  induction t with
  | var y =>
      intro s x ρ
      by_cases h1 : y = x
      · simp [Lambda.subst, h1]
      · by_cases h2 : y > x
        · simp [Lambda.subst, h1, h2]
        · simp [Lambda.subst, h1, h2]
  | app u v ihu ihv =>
      intro s x ρ
      simp [Lambda.subst, ihu, ihv]
  | lam u ih =>
      intro s x ρ
      simp only [Lambda.subst, ddenot_lam]
      refine dlamAny_congr ?_
      intro X
      rw [ih]
      have hs : ddenot (Lambda.lift 1 0 s) (dcons X ρ) = ddenot s ρ := by
        rw [ddenot_lift]
        congr 1
      rw [hs]
      congr 1
      funext i
      cases i with
      | zero => simp
      | succ j =>
          by_cases h1 : j = x
          · subst h1
            simp
          · by_cases h2 : x < j
            · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
              have e2 : x + 1 < j' + 1 + 1 := by omega
              have e3 : j' + 1 + 1 - 1 = j' + 1 := by omega
              simp [e2, e3, h1, h2]
            · have e2 : ¬ (x + 1 < j + 1) := by omega
              simp [e2, h1, h2]

/-- The semantic beta rule. -/
theorem ddenot_beta (t s : Lambda) (ρ : DEnv) :
    ddenot (Lambda.app (Lambda.lam t) s) ρ = ddenot (Lambda.subst s 0 t) ρ := by
  rw [ddenot_app, ddenot_lam_apply, ddenot_subst]
  congr 1
  funext i
  cases i with
  | zero => simp
  | succ j => simp

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

/-- **Soundness**: one step of beta reduction preserves the denotation. -/
theorem ddenot_step {t t' : Lambda} (h : Lambda.step t t') (ρ : DEnv) :
    ddenot t ρ = ddenot t' ρ := by
  induction h generalizing ρ with
  | beta t₁ t₂ => exact ddenot_beta t₁ t₂ ρ
  | app_left t₁ t₁' t₂ _ ih => simp [ih ρ]
  | app_right t₁ t₂ t₂' _ ih => simp [ih ρ]
  | lam t t' _ ih =>
      simp only [ddenot_lam]
      exact dlamAny_congr fun X => ih (dcons X ρ)

theorem ddenot_reduces {t t' : Lambda} (h : Lambda.reduces t t') (ρ : DEnv) :
    ddenot t ρ = ddenot t' ρ := by
  induction h with
  | refl t => rfl
  | step t₁ t₂ t₃ hs _ ih => rw [ddenot_step hs ρ]; exact ih

/-- Convertible terms have the same denotation. -/
theorem ddenot_conv {s t : Lambda} (h : Lambda.Conv s t) (ρ : DEnv) :
    ddenot s ρ = ddenot t ρ := by
  obtain ⟨u, hs, ht⟩ := h
  rw [ddenot_reduces hs ρ, ddenot_reduces ht ρ]

------------------------------------------------------------------------
-- Extensionality: the eta rule
------------------------------------------------------------------------

/-- **The model validates eta**: `⟦λ. (t↑) 0⟧ρ = ⟦t⟧ρ`. -/
theorem ddenot_eta (t : Lambda) (ρ : DEnv) :
    ddenot (Lambda.lam (Lambda.app (Lambda.lift 1 0 t) (Lambda.var 0))) ρ = ddenot t ρ := by
  rw [ddenot_lam]
  have hstep : ∀ X : Dinf,
      ddenot (Lambda.app (Lambda.lift 1 0 t) (Lambda.var 0)) (dcons X ρ)
        = Phi (ddenot t ρ) X := by
    intro X
    rw [ddenot_app, ddenot_var, dcons_zero, ddenot_lift]
    congr 2
  rw [dlamAny_congr hstep, dlamAny_Phi]

end

end ScottDinf
