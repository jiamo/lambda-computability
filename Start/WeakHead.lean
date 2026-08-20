/-
Weak head reduction (call-by-name evaluation) for the untyped lambda calculus.

This file introduces the deterministic *weak head* strategy: contract the
leftmost-outermost redex, never going under a `lam` and never reducing an
argument.  A term is a *weak head normal form* when it has no such redex; for a
closed term this means exactly that it is an abstraction.

The main result proved here is `Lambda.whnIn_of_step`: performing an arbitrary
beta step can never *increase* the number of weak head steps that are needed to
reach a weak head normal form.  Together with the standardization theorem of
`Start/Standardization.lean` (which says that a term with a weak head normal
form is evaluated to one by the weak head strategy) this gives the tools needed
to prove that a term has *no* normal form.
-/

import Start.GrossKnuth

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Substitution congruences for multi-step reduction
------------------------------------------------------------------------

/-- Multi-step reduction is a congruence for substitution in both arguments. -/
theorem reduces_subst {s s' t t' : Lambda} (hs : Lambda.reduces s s')
    (ht : Lambda.reduces t t') (x : ℕ) :
    Lambda.reduces (Lambda.subst s x t) (Lambda.subst s' x t') := by
  have hstep : ∀ {a b : Lambda}, Lambda.reduces a b →
      Lambda.reduces (Lambda.subst a x t) (Lambda.subst b x t) := by
    intro a b hab
    induction hab with
    | refl _ => exact Lambda.reduces.refl _
    | step a1 a2 a3 h1 _ ih =>
        refine Lambda.reduces_trans ?_ ih
        exact Lambda.step_p_imp_reduces
          (Lambda.step_p_subst (Lambda.step_p_refl t) (Lambda.step_imp_step_p h1) x)
  have htgt : ∀ {a b : Lambda}, Lambda.reduces a b →
      Lambda.reduces (Lambda.subst s' x a) (Lambda.subst s' x b) := by
    intro a b hab
    induction hab with
    | refl _ => exact Lambda.reduces.refl _
    | step a1 a2 a3 h1 _ ih =>
        refine Lambda.reduces_trans ?_ ih
        exact Lambda.step_p_imp_reduces
          (Lambda.step_p_subst (Lambda.step_imp_step_p h1) (Lambda.step_p_refl s') x)
  exact Lambda.reduces_trans (hstep hs) (htgt ht)

------------------------------------------------------------------------
-- Weak head reduction
------------------------------------------------------------------------

/-- One step of weak head (call-by-name) reduction. -/
inductive wstep : Lambda → Lambda → Prop
  | beta (P Q : Lambda) : wstep (Lambda.app (Lambda.lam P) Q) (Lambda.subst Q 0 P)
  | app {M M' : Lambda} (N : Lambda) : wstep M M' → wstep (Lambda.app M N) (Lambda.app M' N)

/-- A weak head normal form is a term with no weak head redex. -/
def IsWhnf (t : Lambda) : Prop := ∀ t', ¬ wstep t t'

/-- Weak head steps are beta steps. -/
theorem wstep_imp_step {t t' : Lambda} (h : wstep t t') : Lambda.step t t' := by
  induction h with
  | beta P Q => exact Lambda.step.beta P Q
  | app N _ ih => exact Lambda.step.app_left _ _ _ ih

/-- Weak head reduction is deterministic. -/
theorem wstep_deterministic {t t₁ t₂ : Lambda} (h₁ : wstep t t₁) (h₂ : wstep t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | beta P Q =>
      cases h₂ with
      | beta _ _ => rfl
      | app _ h => cases h
  | app N h ih =>
      cases h₂ with
      | beta _ _ => cases h
      | app _ h' => rw [ih h']

/-- Abstractions are weak head normal forms. -/
theorem isWhnf_lam (P : Lambda) : IsWhnf (Lambda.lam P) := by
  intro t' h
  cases h

/-- Variables are weak head normal forms. -/
theorem isWhnf_var (n : ℕ) : IsWhnf (Lambda.var n) := by
  intro t' h
  cases h

/-- Church numerals are weak head normal forms. -/
theorem isWhnf_church (n : ℕ) : IsWhnf (Lambda.church n) := by
  simpa [Lambda.church] using isWhnf_lam _

/-- An application is a weak head normal form exactly when its function part is a
weak head normal form which is not an abstraction. -/
theorem isWhnf_app_iff {M N : Lambda} :
    IsWhnf (Lambda.app M N) ↔ (IsWhnf M ∧ ∀ P, M ≠ Lambda.lam P) := by
  constructor
  · intro h
    refine ⟨fun M' hM' => h _ (wstep.app N hM'), ?_⟩
    rintro P rfl
    exact h _ (wstep.beta P N)
  · rintro ⟨h1, h2⟩ t' hstep
    cases hstep with
    | beta P Q => exact h2 P rfl
    | app _ h => exact h1 _ h

/-- A weak head normal form which is not an abstraction stays one under a beta step. -/
theorem not_lam_of_step_of_isWhnf {M M' : Lambda} (hw : IsWhnf M) (hnl : ∀ P, M ≠ Lambda.lam P)
    (hs : Lambda.step M M') : ∀ P, M' ≠ Lambda.lam P := by
  cases hs with
  | beta P Q => exact absurd (wstep.beta P Q) (hw _)
  | app_left a b c _ => intro P h; exact Lambda.noConfusion h
  | app_right a b c _ => intro P h; exact Lambda.noConfusion h
  | lam t t' _ => exact absurd rfl (hnl t)

/-- Weak head normal forms are preserved by arbitrary beta steps. -/
theorem isWhnf_of_step {t t' : Lambda} (h : IsWhnf t) (hs : Lambda.step t t') : IsWhnf t' := by
  induction hs with
  | beta P Q => exact absurd (wstep.beta P Q) (h _)
  | app_left t₁ t₁' t₂ hstep ih =>
      rw [isWhnf_app_iff] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨ih h1, not_lam_of_step_of_isWhnf h1 h2 hstep⟩
  | app_right t₁ t₂ t₂' _ _ =>
      rw [isWhnf_app_iff] at h ⊢
      exact h
  | lam t t' _ _ => exact isWhnf_lam _

/-- Weak head normal forms are preserved by reduction. -/
theorem isWhnf_of_reduces {t t' : Lambda} (h : IsWhnf t) (hr : Lambda.reduces t t') :
    IsWhnf t' := by
  induction hr with
  | refl _ => exact h
  | step a b c hs _ ih => exact ih (isWhnf_of_step h hs)

------------------------------------------------------------------------
-- Internal steps
------------------------------------------------------------------------

/-- A beta step which is not the weak head step: it happens under a `lam`, inside an
argument, or (recursively) internally in the function part of an application. -/
inductive wistep : Lambda → Lambda → Prop
  | lam {P P' : Lambda} : Lambda.step P P' → wistep (Lambda.lam P) (Lambda.lam P')
  | appL {M M' N : Lambda} : wistep M M' → wistep (Lambda.app M N) (Lambda.app M' N)
  | appR {M N N' : Lambda} : Lambda.step N N' → wistep (Lambda.app M N) (Lambda.app M N')

/-- Internal steps are beta steps. -/
theorem wistep_imp_step {t t' : Lambda} (h : wistep t t') : Lambda.step t t' := by
  induction h with
  | lam h => exact Lambda.step.lam _ _ h
  | appL _ ih => exact Lambda.step.app_left _ _ _ ih
  | appR h => exact Lambda.step.app_right _ _ _ h

/-- Every beta step is either the weak head step or an internal step. -/
theorem step_dichotomy {t t' : Lambda} (h : Lambda.step t t') : wstep t t' ∨ wistep t t' := by
  induction h with
  | beta P Q => exact Or.inl (wstep.beta P Q)
  | app_left t₁ t₁' t₂ _ ih =>
      rcases ih with h | h
      · exact Or.inl (wstep.app t₂ h)
      · exact Or.inr (wistep.appL h)
  | app_right t₁ t₂ t₂' h _ => exact Or.inr (wistep.appR h)
  | lam t t' h _ => exact Or.inr (wistep.lam h)

/-- An internal step cannot remove the weak head redex. -/
theorem wstep_of_wistep {M N M' : Lambda} (hi : wistep M N) (hw : wstep M M') :
    ∃ N', wstep N N' ∧ Lambda.reduces M' N' := by
  induction hi generalizing M' with
  | lam h => cases hw
  | @appL A A' B hAi ih =>
      cases hw with
      | beta P Q =>
          cases hAi with
          | lam hP =>
              refine ⟨Lambda.subst B 0 _, wstep.beta _ B, ?_⟩
              exact reduces_subst (Lambda.reduces.refl B)
                (Lambda.reduces.step _ _ _ hP (Lambda.reduces.refl _)) 0
      | app _ hA =>
          obtain ⟨A'', hA'', hred⟩ := ih hA
          exact ⟨Lambda.app A'' B, wstep.app B hA'', Lambda.reduces_app_left hred⟩
  | @appR A B B' hB =>
      cases hw with
      | beta P Q =>
          refine ⟨Lambda.subst B' 0 P, wstep.beta P B', ?_⟩
          exact reduces_subst (Lambda.reduces.step _ _ _ hB (Lambda.reduces.refl _))
            (Lambda.reduces.refl P) 0
      | app _ hA =>
          exact ⟨Lambda.app _ B', wstep.app B' hA, Lambda.reduces_app_right
            (Lambda.reduces.step _ _ _ hB (Lambda.reduces.refl _))⟩

------------------------------------------------------------------------
-- Bounded weak head evaluation
------------------------------------------------------------------------

/-- `WHNIn n t` says that at most `n` weak head steps take `t` to a weak head
normal form. -/
def WHNIn : ℕ → Lambda → Prop
  | 0, t => IsWhnf t
  | (n + 1), t => IsWhnf t ∨ ∃ t', wstep t t' ∧ WHNIn n t'

/-- `HasWhnfEval t` says that the weak head strategy terminates on `t`. -/
def HasWhnfEval (t : Lambda) : Prop := ∃ n, WHNIn n t

theorem whnIn_mono {n m : ℕ} (hnm : n ≤ m) {t : Lambda} (h : WHNIn n t) : WHNIn m t := by
  induction m generalizing n t with
  | zero =>
      obtain rfl : n = 0 := Nat.le_zero.mp hnm
      exact h
  | succ m ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Or.inl h
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rcases h with h | ⟨t', hstep, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨t', hstep, ih (by omega) h'⟩

theorem whnIn_succ_of_wstep {n : ℕ} {t t' : Lambda} (hstep : wstep t t') (h : WHNIn n t') :
    WHNIn (n + 1) t := Or.inr ⟨t', hstep, h⟩

theorem hasWhnfEval_of_wstep {t t' : Lambda} (hstep : wstep t t') (h : HasWhnfEval t') :
    HasWhnfEval t := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, whnIn_succ_of_wstep hstep hn⟩

theorem hasWhnfEval_of_isWhnf {t : Lambda} (h : IsWhnf t) : HasWhnfEval t := ⟨0, h⟩

/-- If a term is not a weak head normal form it makes a weak head step. -/
theorem exists_wstep_of_not_isWhnf {t : Lambda} (h : ¬ IsWhnf t) : ∃ t', wstep t t' := by
  by_contra hc
  exact h fun t' hst => hc ⟨t', hst⟩

/-- **Weak head evaluation is optimal**: an arbitrary beta step never increases the
number of weak head steps needed to reach a weak head normal form. -/
theorem whnIn_of_step {n : ℕ} {M N : Lambda} (hs : Lambda.step M N) (h : WHNIn n M) :
    WHNIn n N := by
  induction n using Nat.strong_induction_on generalizing M N with
  | _ n ih =>
      -- multi-step version at strictly smaller bounds
      have ihmulti : ∀ m, m < n → ∀ {A B : Lambda}, Lambda.reduces A B → WHNIn m A → WHNIn m B := by
        intro m hm A B hred hA
        induction hred with
        | refl _ => exact hA
        | step a b c hst _ ihr => exact ihr (ih m hm hst hA)
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact isWhnf_of_step h hs
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rcases h with hw | ⟨M', hMM', hM'⟩
      · exact whnIn_mono (Nat.zero_le _) (isWhnf_of_step hw hs)
      · rcases step_dichotomy hs with hhead | hint
        · -- the step is the weak head step
          have hNM' : N = M' := wstep_deterministic hhead hMM'
          exact whnIn_mono (Nat.le_succ k) (hNM' ▸ hM')
        · -- internal step
          obtain ⟨N', hN', hred⟩ := wstep_of_wistep hint hMM'
          exact Or.inr ⟨N', hN', ihmulti k (by omega) hred hM'⟩

/-- A terminating weak head evaluation exhibits a weak head normal form reduct. -/
theorem exists_whnf_of_whnIn : ∀ (n : ℕ) {t : Lambda}, WHNIn n t →
    ∃ u, Lambda.reduces t u ∧ IsWhnf u := by
  intro n
  induction n with
  | zero => intro t h; exact ⟨t, Lambda.reduces.refl t, h⟩
  | succ n ih =>
      intro t h
      rcases h with hw | ⟨t', hstep, h'⟩
      · exact ⟨t, Lambda.reduces.refl t, hw⟩
      · obtain ⟨u, hu1, hu2⟩ := ih h'
        exact ⟨u, Lambda.reduces.step _ _ _ (wstep_imp_step hstep) hu1, hu2⟩

/-- A term with a terminating weak head evaluation reduces to a weak head normal form. -/
theorem exists_whnf_of_hasWhnfEval {t : Lambda} (h : HasWhnfEval t) :
    ∃ u, Lambda.reduces t u ∧ IsWhnf u := by
  obtain ⟨n, hn⟩ := h
  exact exists_whnf_of_whnIn n hn

/-- Weak head evaluation of an application evaluates its function part. -/
theorem hasWhnfEval_app_left : ∀ (n : ℕ) {M N : Lambda}, WHNIn n (Lambda.app M N) →
    HasWhnfEval M := by
  intro n
  induction n with
  | zero =>
      intro M N h
      exact hasWhnfEval_of_isWhnf ((isWhnf_app_iff.1 h).1)
  | succ n ih =>
      intro M N h
      rcases h with hw | ⟨z, hstep, hz⟩
      · exact hasWhnfEval_of_isWhnf ((isWhnf_app_iff.1 hw).1)
      · cases hstep with
        | beta P Q => exact hasWhnfEval_of_isWhnf (isWhnf_lam P)
        | app _ hM => exact hasWhnfEval_of_wstep hM (ih hz)

/-- If the weak head strategy terminates on an application it terminates on its
function part. -/
theorem hasWhnfEval_of_app {M N : Lambda} (h : HasWhnfEval (Lambda.app M N)) :
    HasWhnfEval M := by
  obtain ⟨n, hn⟩ := h
  exact hasWhnfEval_app_left n hn

/-- Multi-step version of `Lambda.whnIn_of_step`. -/
theorem whnIn_of_reduces {n : ℕ} {M N : Lambda} (hr : Lambda.reduces M N) (h : WHNIn n M) :
    WHNIn n N := by
  induction hr with
  | refl _ => exact h
  | step a b c hs _ ih => exact ih (whnIn_of_step hs h)

end Lambda

end
