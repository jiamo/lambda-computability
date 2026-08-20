/-
# Solvability

A term is *solvable* when some closed arguments turn it into the identity: `M N₁ … Nₖ` is
convertible with `I`.  Solvability is the standard dividing line between terms that carry
computational information and terms that carry none, and it is the setting in which separation
results (Böhm's theorem and its relatives) are stated.

This module develops the basic theory that the rest of the repository can build on:

* `Lambda.appList` — application to a list of arguments, with its reduction and convertibility
  congruences;
* `Lambda.Solvable`, `Lambda.Solvable.of_conv` — the definition and its invariance under
  convertibility;
* `Lambda.solvable_I`, `Lambda.solvable_church` — closed normal terms that are solvable;
* `Lambda.not_solvable_omega` — `Ω` is unsolvable.  The proof isolates the shape "an application
  whose head is `Ω`" (`Lambda.OmegaApp`), shows it is preserved by reduction, and observes that
  `I` does not have that shape;
* `Lambda.exists_args_conv_of_solvable` — *generic reachability*: a solvable term can be driven to
  **any** closed term by suitable closed arguments.  This is the sense in which solvable terms are
  computationally universal and unsolvable ones are inert;
* `Lambda.not_decides_solvable`, `Lambda.not_computablePred_codeSet_solvable` — solvability is
  undecidable, both by a lambda term and as a predicate on codes.  These follow from Scott's
  theorem, since solvability is convertibility-invariant with a closed solvable witness (`I`) and
  a closed unsolvable one (`Ω`).
-/

import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Application to a list of arguments -/

/-- `appList t [a₁, …, aₖ] = t a₁ … aₖ`. -/
def appList (t : Lambda) : List Lambda → Lambda
  | [] => t
  | a :: rest => appList (Lambda.app t a) rest

theorem appList_nil (t : Lambda) : appList t [] = t := rfl

theorem appList_cons (t a : Lambda) (rest : List Lambda) :
    appList t (a :: rest) = appList (Lambda.app t a) rest := rfl

theorem appList_concat (t a : Lambda) : ∀ args : List Lambda,
    appList t (args ++ [a]) = Lambda.app (appList t args) a
  | [] => rfl
  | b :: rest => by
      rw [List.cons_append, appList_cons, appList_cons, appList_concat (Lambda.app t b) a rest]

theorem reduces_appList {s t : Lambda} (h : Lambda.reduces s t) :
    ∀ args : List Lambda, Lambda.reduces (appList s args) (appList t args)
  | [] => h
  | _ :: rest => reduces_appList (Lambda.reduces_app_left h) rest

theorem conv_appList {s t : Lambda} (h : Conv s t) (args : List Lambda) :
    Conv (appList s args) (appList t args) := by
  obtain ⟨u, h1, h2⟩ := h
  exact ⟨appList u args, reduces_appList h1 args, reduces_appList h2 args⟩

theorem conv_app_left {s t : Lambda} (h : Conv s t) (a : Lambda) :
    Conv (Lambda.app s a) (Lambda.app t a) := by
  obtain ⟨u, h1, h2⟩ := h
  exact ⟨Lambda.app u a, Lambda.reduces_app_left h1, Lambda.reduces_app_left h2⟩

/-! ## Solvability -/

/-- A term is *solvable* when closed arguments turn it into the identity. -/
def Solvable (t : Lambda) : Prop :=
  ∃ args : List Lambda, (∀ a ∈ args, Lambda.IsClosed a) ∧ Conv (appList t args) Lambda.I

/-- Solvability only depends on the convertibility class of a term. -/
theorem Solvable.of_conv {s t : Lambda} (hst : Conv s t) (hs : Solvable s) : Solvable t := by
  obtain ⟨args, hargs, hconv⟩ := hs
  exact ⟨args, hargs, ((conv_appList hst args).symm).trans hconv⟩

theorem convInvariant_solvable : ConvInvariant Solvable :=
  fun _ _ hst hs => Solvable.of_conv hst hs

/-- The identity is solvable: no arguments are needed. -/
theorem solvable_I : Solvable Lambda.I :=
  ⟨[], by simp, conv_refl _⟩

/-- Church numerals are solvable: applied to `I` twice they return `I`. -/
theorem solvable_church (k : ℕ) : Solvable (Lambda.church k) := by
  refine ⟨[Lambda.I, Lambda.I], ?_, conv_of_reduces ?_⟩
  · intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Lambda.I_closed
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact Lambda.I_closed
      · exact absurd ha (by simp)
  · exact church_force k Lambda.I

/-! ## `Ω` is unsolvable -/

/-- The shape "an application whose head is `Ω`". -/
inductive OmegaApp : Lambda → Prop
  | base : OmegaApp Lambda.omega
  | app {t : Lambda} (a : Lambda) : OmegaApp t → OmegaApp (Lambda.app t a)

theorem OmegaApp.exists_app {t : Lambda} (h : OmegaApp t) :
    ∃ f x : Lambda, t = Lambda.app f x := by
  cases h with
  | base => exact ⟨_, _, rfl⟩
  | app a h => exact ⟨_, _, rfl⟩

theorem omegaApp_appList : ∀ (t : Lambda), OmegaApp t → ∀ args : List Lambda,
    OmegaApp (appList t args) := by
  intro t ht args
  induction args generalizing t with
  | nil => exact ht
  | cons a rest ih => exact ih (Lambda.app t a) (OmegaApp.app a ht)

theorem omegaApp_of_step {t : Lambda} (h : OmegaApp t) :
    ∀ {u : Lambda}, Lambda.step t u → OmegaApp u := by
  induction h with
  | base =>
      intro u hu
      rw [Lambda.step_omega_eq u hu]
      exact OmegaApp.base
  | @app t a ht ih =>
      intro u hu
      cases hu with
      | beta t₁ t₂ =>
          obtain ⟨f, x, hfx⟩ := ht.exists_app
          exact absurd hfx (by simp)
      | app_left _ t₁' _ hstep => exact OmegaApp.app a (ih hstep)
      | app_right _ _ t₂' _ => exact OmegaApp.app _ ht

theorem omegaApp_of_reduces {t u : Lambda} (h : OmegaApp t) (hr : Lambda.reduces t u) :
    OmegaApp u := by
  induction hr with
  | refl t => exact h
  | step t₁ t₂ t₃ hstep _ ih => exact ih (omegaApp_of_step h hstep)

theorem not_omegaApp_I : ¬ OmegaApp Lambda.I := by
  intro h
  obtain ⟨f, x, hfx⟩ := h.exists_app
  exact absurd hfx (by simp [Lambda.I])

theorem is_normal_I : Lambda.is_normal Lambda.I := by
  intro t' h
  rw [Lambda.I] at h
  cases h with
  | lam _ _ hstep => cases hstep

/-- **`Ω` is unsolvable**: no closed arguments turn it into the identity. -/
theorem not_solvable_omega : ¬ Solvable Lambda.omega := by
  rintro ⟨args, -, u, h1, h2⟩
  have hu : u = Lambda.I := (Lambda.reduces_normal_eq is_normal_I h2).symm
  have hOm : OmegaApp u := omegaApp_of_reduces (omegaApp_appList _ OmegaApp.base args) h1
  rw [hu] at hOm
  exact not_omegaApp_I hOm

/-! ## Generic reachability -/

/-- **A solvable term can be driven to any closed term.**  This is the precise sense in which a
solvable term carries computational information: closed arguments can extract an arbitrary closed
result from it. -/
theorem exists_args_conv_of_solvable {t : Lambda} (h : Solvable t) {N : Lambda}
    (hN : Lambda.IsClosed N) :
    ∃ args : List Lambda, (∀ a ∈ args, Lambda.IsClosed a) ∧ Conv (appList t args) N := by
  obtain ⟨args, hargs, hconv⟩ := h
  refine ⟨args ++ [N], ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hargs a ha
    · rw [List.mem_singleton.1 ha]
      exact hN
  · rw [appList_concat]
    exact (conv_app_left hconv N).trans (conv_of_reduces (reduces_I N))

/-! ## Undecidability of solvability -/

/-- **No closed lambda term decides solvability.** -/
theorem not_decides_solvable {F : Lambda} (hF : Lambda.IsClosed F) : ¬ Decides F Solvable :=
  scott_theorem convInvariant_solvable Lambda.I_closed omega_closed solvable_I
    not_solvable_omega hF

/-- **Solvability is undecidable**: the set of codes of solvable terms is not computable. -/
theorem not_computablePred_codeSet_solvable : ¬ ComputablePred (CodeSet Solvable) :=
  not_computablePred_codeSet convInvariant_solvable Lambda.I_closed omega_closed solvable_I
    not_solvable_omega

end Lambda
