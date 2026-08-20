/-
Normalization of the leftmost-outermost (normal order) strategy.

`Start/EvalSound.lean` defines the term-level normal order step `Lambda.step_normal`
and shows that the code-level step `Lambda.code_step'` computes it.  Iterating it is
the leftmost evaluator `Lambda.eval'`, whose completeness half was left as the
hypothesis `Lambda.EvalNormalization`.

This file discharges that hypothesis.  The argument is the classical one, organised
around the weak head machinery of `Start/WeakHead.lean` and
`Start/Standardization.lean`: while a term is not a weak head normal form, the normal
order step *is* the weak head step, so the weak head strategy (which is normalizing,
by `Lambda.hasWhnfEval_of_reduces_whnf`) is an initial segment of the normal order
reduction.  Once a weak head normal form is reached it is either an abstraction, whose
body is normalised recursively, or a *neutral* term `x M₁ … Mₙ`, whose arguments are
normalised recursively from left to right.  The recursion is on the structure of the
normal form.
-/

import Start.Standardization
import Start.EvalCorrect

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Neutral terms
------------------------------------------------------------------------

/-- A *neutral* term is a variable applied to a (possibly empty) list of arguments.
Neutral terms are exactly the weak head normal forms that are not abstractions. -/
inductive Neutral : Lambda → Prop
  | var (n : ℕ) : Neutral (Lambda.var n)
  | app {M : Lambda} (N : Lambda) : Neutral M → Neutral (Lambda.app M N)

theorem Neutral.ne_lam {M : Lambda} (h : Neutral M) : ∀ P, M ≠ Lambda.lam P := by
  cases h <;> intro P hP <;> exact Lambda.noConfusion hP

theorem neutral_of_isWhnf {M : Lambda} (hw : IsWhnf M) (hnl : ∀ P, M ≠ Lambda.lam P) :
    Neutral M := by
  induction M with
  | var n => exact Neutral.var n
  | lam P _ => exact absurd rfl (hnl P)
  | app A B ihA _ =>
      obtain ⟨hA, hAnl⟩ := isWhnf_app_iff.1 hw
      exact Neutral.app B (ihA hA hAnl)

theorem Neutral.step {M M' : Lambda} (h : Neutral M) (hs : Lambda.step M M') : Neutral M' := by
  induction hs with
  | beta t₁ t₂ =>
      cases h with
      | app N hA => exact absurd rfl (hA.ne_lam t₁)
  | app_left t₁ t₁' t₂ hst ih =>
      cases h with
      | app N hA => exact Neutral.app t₂ (ih hA)
  | app_right t₁ t₂ t₂' _ _ =>
      cases h with
      | app N hA => exact Neutral.app t₂' hA
  | lam t t' _ _ => cases h

theorem Neutral.reduces {M M' : Lambda} (h : Neutral M) (hr : Lambda.reduces M M') :
    Neutral M' := by
  induction hr with
  | refl _ => exact h
  | step a b c hs _ ih => exact ih (h.step hs)

------------------------------------------------------------------------
-- Shapes of reducts
------------------------------------------------------------------------

theorem reduces_lam_shape_aux : ∀ {t u : Lambda}, Lambda.reduces t u → ∀ M, t = Lambda.lam M →
    ∃ N, u = Lambda.lam N ∧ Lambda.reduces M N := by
  intro t u h
  induction h with
  | refl s => intro M hM; exact ⟨M, hM, Lambda.reduces.refl M⟩
  | step a b c hs _ ih =>
      intro M hM
      subst hM
      cases hs with
      | lam t t' hst =>
          obtain ⟨N, hN1, hN2⟩ := ih t' rfl
          exact ⟨N, hN1, Lambda.reduces.step _ _ _ hst hN2⟩

theorem reduces_lam_shape {M u : Lambda} (h : Lambda.reduces (Lambda.lam M) u) :
    ∃ N, u = Lambda.lam N ∧ Lambda.reduces M N :=
  reduces_lam_shape_aux h M rfl

theorem reduces_neutral_app_aux : ∀ {t u : Lambda}, Lambda.reduces t u → ∀ M N, t = Lambda.app M N →
    Neutral M → ∃ M' N', u = Lambda.app M' N' ∧ Lambda.reduces M M' ∧ Lambda.reduces N N' := by
  intro t u h
  induction h with
  | refl s =>
      intro M N hMN _
      exact ⟨M, N, hMN, Lambda.reduces.refl M, Lambda.reduces.refl N⟩
  | step a b c hs _ ih =>
      intro M N hMN hM
      subst hMN
      cases hs with
      | beta t₁ t₂ => exact absurd rfl (hM.ne_lam t₁)
      | app_left _ t₁' _ hst =>
          obtain ⟨M', N', h1, h2, h3⟩ := ih t₁' N rfl (hM.step hst)
          exact ⟨M', N', h1, Lambda.reduces.step _ _ _ hst h2, h3⟩
      | app_right _ _ t₂' hst =>
          obtain ⟨M', N', h1, h2, h3⟩ := ih M t₂' rfl hM
          exact ⟨M', N', h1, h2, Lambda.reduces.step _ _ _ hst h3⟩

theorem reduces_neutral_app {M N u : Lambda} (hM : Neutral M)
    (h : Lambda.reduces (Lambda.app M N) u) :
    ∃ M' N', u = Lambda.app M' N' ∧ Lambda.reduces M M' ∧ Lambda.reduces N N' :=
  reduces_neutral_app_aux h M N rfl hM

theorem reduces_var_shape {n : ℕ} {u : Lambda} (h : Lambda.reduces (Lambda.var n) u) :
    u = Lambda.var n :=
  (Lambda.reduces_normal_eq (Lambda.var_normal n) h).symm

------------------------------------------------------------------------
-- Normal forms of subterms
------------------------------------------------------------------------

theorem is_normal_of_lam {M : Lambda} (h : Lambda.is_normal (Lambda.lam M)) :
    Lambda.is_normal M := fun _ hs => h _ (Lambda.step.lam _ _ hs)

theorem is_normal_of_app_left {M N : Lambda} (h : Lambda.is_normal (Lambda.app M N)) :
    Lambda.is_normal M := fun _ hs => h _ (Lambda.step.app_left _ _ _ hs)

theorem is_normal_of_app_right {M N : Lambda} (h : Lambda.is_normal (Lambda.app M N)) :
    Lambda.is_normal N := fun _ hs => h _ (Lambda.step.app_right _ _ _ hs)

theorem isWhnf_of_is_normal {t : Lambda} (h : Lambda.is_normal t) : IsWhnf t :=
  fun t' hw => h t' (wstep_imp_step hw)

------------------------------------------------------------------------
-- The normal order step
------------------------------------------------------------------------

theorem step_normal_lam (M : Lambda) :
    Lambda.step_normal (Lambda.lam M) = (Lambda.step_normal M).map Lambda.lam := rfl

theorem step_normal_beta (P Q : Lambda) :
    Lambda.step_normal (Lambda.app (Lambda.lam P) Q) = some (Lambda.subst Q 0 P) := rfl

theorem step_normal_app_of_ne_lam {A B : Lambda} (hA : ∀ P, A ≠ Lambda.lam P) :
    Lambda.step_normal (Lambda.app A B) =
      match Lambda.step_normal A with
      | some A' => some (Lambda.app A' B)
      | none => (Lambda.step_normal B).map (Lambda.app A) := by
  cases A with
  | var n =>
      change (match Lambda.step_normal (Lambda.var n) with
        | some A' => some (Lambda.app A' B)
        | none => match Lambda.step_normal B with
          | some B' => some (Lambda.app (Lambda.var n) B')
          | none => none) = _
      cases Lambda.step_normal B <;> rfl
  | lam P => exact absurd rfl (hA P)
  | app C D =>
      change (match Lambda.step_normal (Lambda.app C D) with
        | some A' => some (Lambda.app A' B)
        | none => match Lambda.step_normal B with
          | some B' => some (Lambda.app (Lambda.app C D) B')
          | none => none) = _
      cases Lambda.step_normal (Lambda.app C D) <;> cases Lambda.step_normal B <;> rfl

/-- A normal order step is a beta step. -/
theorem step_of_step_normal : ∀ {t t' : Lambda}, Lambda.step_normal t = some t' →
    Lambda.step t t' := by
  intro t
  induction t with
  | var n => intro t' h; exact absurd h (by simp [Lambda.step_normal])
  | lam M ih =>
      intro t' h
      rw [step_normal_lam] at h
      rcases hM : Lambda.step_normal M with _ | M'
      · rw [hM] at h; exact absurd h (by simp)
      · rw [hM] at h
        have : t' = Lambda.lam M' := by simpa using h.symm
        subst this
        exact Lambda.step.lam _ _ (ih hM)
  | app A B ihA ihB =>
      intro t' h
      by_cases hA : ∃ P, A = Lambda.lam P
      · obtain ⟨P, rfl⟩ := hA
        rw [step_normal_beta] at h
        have : t' = Lambda.subst B 0 P := by simpa using h.symm
        subst this
        exact Lambda.step.beta P B
      · have hnl : ∀ P, A ≠ Lambda.lam P := fun P hP => hA ⟨P, hP⟩
        rw [step_normal_app_of_ne_lam hnl] at h
        rcases hAs : Lambda.step_normal A with _ | A'
        · rw [hAs] at h
          simp only at h
          rcases hBs : Lambda.step_normal B with _ | B'
          · rw [hBs] at h; exact absurd h (by simp)
          · rw [hBs] at h
            have : t' = Lambda.app A B' := by simpa using h.symm
            subst this
            exact Lambda.step.app_right _ _ _ (ihB hBs)
        · rw [hAs] at h
          have : t' = Lambda.app A' B := by simpa using h.symm
          subst this
          exact Lambda.step.app_left _ _ _ (ihA hAs)

theorem step_normal_eq_none_of_is_normal {t : Lambda} (h : Lambda.is_normal t) :
    Lambda.step_normal t = none := by
  rcases ht : Lambda.step_normal t with _ | t'
  · rfl
  · exact absurd (step_of_step_normal ht) (h t')

/-- While a term is not a weak head normal form, the normal order step *is* the weak head
step. -/
theorem step_normal_of_wstep : ∀ {t t' : Lambda}, wstep t t' → Lambda.step_normal t = some t' := by
  intro t t' h
  induction h with
  | beta P Q => exact step_normal_beta P Q
  | @app M M' N hstep ih =>
      have hnl : ∀ P, M ≠ Lambda.lam P := by
        rintro P rfl
        exact isWhnf_lam P _ hstep
      rw [step_normal_app_of_ne_lam hnl, ih]

------------------------------------------------------------------------
-- Reachability by normal order steps
------------------------------------------------------------------------

/-- Reachability by iterated normal order steps. -/
def NRed : Lambda → Lambda → Prop :=
  Relation.ReflTransGen fun a b => Lambda.step_normal a = some b

theorem NRed.refl (t : Lambda) : NRed t t := Relation.ReflTransGen.refl

theorem NRed.single {t t' : Lambda} (h : Lambda.step_normal t = some t') : NRed t t' :=
  Relation.ReflTransGen.single h

theorem NRed.trans {a b c : Lambda} (h1 : NRed a b) (h2 : NRed b c) : NRed a c :=
  Relation.ReflTransGen.trans h1 h2

theorem NRed.tail {a b c : Lambda} (h1 : NRed a b) (h2 : Lambda.step_normal b = some c) :
    NRed a c := Relation.ReflTransGen.tail h1 h2

theorem NRed.reduces {a b : Lambda} (h : NRed a b) : Lambda.reduces a b := by
  induction h with
  | refl => exact Lambda.reduces.refl a
  | tail _ hstep ih =>
      exact Lambda.reduces_trans ih
        (Lambda.reduces.step _ _ _ (step_of_step_normal hstep) (Lambda.reduces.refl _))

theorem NRed.lam {M N : Lambda} (h : NRed M N) : NRed (Lambda.lam M) (Lambda.lam N) := by
  induction h with
  | refl => exact NRed.refl _
  | tail _ hstep ih =>
      refine ih.tail ?_
      rw [step_normal_lam, hstep]
      rfl

theorem NRed.appL {M M' : Lambda} (N : Lambda) (hM : Neutral M) (h : NRed M M') :
    NRed (Lambda.app M N) (Lambda.app M' N) := by
  induction h with
  | refl => exact NRed.refl _
  | @tail b c hab hstep ih =>
      refine ih.tail ?_
      have hb : Neutral b := hM.reduces (NRed.reduces hab)
      rw [step_normal_app_of_ne_lam hb.ne_lam, hstep]

theorem NRed.appR {M N N' : Lambda} (hM : Neutral M) (hMn : Lambda.is_normal M) (h : NRed N N') :
    NRed (Lambda.app M N) (Lambda.app M N') := by
  induction h with
  | refl => exact NRed.refl _
  | tail _ hstep ih =>
      refine ih.tail ?_
      rw [step_normal_app_of_ne_lam hM.ne_lam, step_normal_eq_none_of_is_normal hMn, hstep]
      rfl

/-- The weak head strategy is an initial segment of the normal order reduction. -/
theorem nred_of_wred {t w : Lambda} (h : Relation.ReflTransGen wstep t w) : NRed t w := by
  induction h with
  | refl => exact NRed.refl _
  | tail _ hstep ih => exact ih.tail (step_normal_of_wstep hstep)

------------------------------------------------------------------------
-- Reaching a weak head normal form by normal order steps
------------------------------------------------------------------------

theorem exists_nred_whnf_aux : ∀ (n : ℕ) {t : Lambda}, WHNIn n t →
    ∃ w, NRed t w ∧ IsWhnf w := by
  intro n
  induction n with
  | zero => intro t h; exact ⟨t, NRed.refl t, h⟩
  | succ n ih =>
      intro t h
      rcases h with hw | ⟨t', hstep, h'⟩
      · exact ⟨t, NRed.refl t, hw⟩
      · obtain ⟨w, hw1, hw2⟩ := ih h'
        exact ⟨w, (NRed.single (step_normal_of_wstep hstep)).trans hw1, hw2⟩

theorem exists_nred_whnf {t : Lambda} (h : HasWhnfEval t) : ∃ w, NRed t w ∧ IsWhnf w := by
  obtain ⟨n, hn⟩ := h
  exact exists_nred_whnf_aux n hn

/-- If `t` reduces to a normal form `u`, then the normal order strategy first reaches a
weak head normal form of `t`, which still reduces to `u`. -/
theorem nred_whnf_of_reduces_normal {t u : Lambda} (hu : Lambda.is_normal u)
    (ht : Lambda.reduces t u) : ∃ w, NRed t w ∧ IsWhnf w ∧ Lambda.reduces w u := by
  obtain ⟨w, hw1, hw2⟩ :=
    exists_nred_whnf (hasWhnfEval_of_reduces_whnf ht (isWhnf_of_is_normal hu))
  obtain ⟨v, hv1, hv2⟩ := Lambda.confluence_theorem (NRed.reduces hw1) ht
  exact ⟨w, hw1, hw2, (Lambda.reduces_normal_eq hu hv2) ▸ hv1⟩

------------------------------------------------------------------------
-- Leftmost-outermost reduction is normalizing
------------------------------------------------------------------------

/-- **The leftmost-outermost strategy is normalizing.**  If `t` beta-reduces to a normal
form `u`, then the normal order strategy reaches `u` from `t`. -/
theorem nred_of_reduces_normal : ∀ (u : Lambda), Lambda.is_normal u →
    ∀ (t : Lambda), Lambda.reduces t u → NRed t u := by
  intro u
  induction u with
  | var n =>
      intro _ t ht
      obtain ⟨w, hw1, hw2, hw3⟩ := nred_whnf_of_reduces_normal (Lambda.var_normal n) ht
      cases w with
      | var m => cases reduces_var_shape hw3; exact hw1
      | lam P => obtain ⟨N, hN, -⟩ := reduces_lam_shape hw3; exact absurd hN (by simp)
      | app A B =>
          have hA : Neutral A := by
            have := (isWhnf_app_iff.1 hw2)
            exact neutral_of_isWhnf this.1 this.2
          obtain ⟨A', B', hAB, -, -⟩ := reduces_neutral_app hA hw3
          exact absurd hAB (by simp)
  | lam M ih =>
      intro hu t ht
      obtain ⟨w, hw1, hw2, hw3⟩ := nred_whnf_of_reduces_normal hu ht
      cases w with
      | var n => exact absurd (reduces_var_shape hw3) (by simp)
      | lam P =>
          obtain ⟨N, hN, hPN⟩ := reduces_lam_shape hw3
          have : N = M := by injection hN with h1; exact h1.symm
          subst this
          exact hw1.trans (NRed.lam (ih (is_normal_of_lam hu) P hPN))
      | app A B =>
          have hA : Neutral A := by
            have := (isWhnf_app_iff.1 hw2)
            exact neutral_of_isWhnf this.1 this.2
          obtain ⟨A', B', hAB, -, -⟩ := reduces_neutral_app hA hw3
          exact absurd hAB (by simp)
  | app M N ihM ihN =>
      intro hu t ht
      obtain ⟨w, hw1, hw2, hw3⟩ := nred_whnf_of_reduces_normal hu ht
      cases w with
      | var n => exact absurd (reduces_var_shape hw3) (by simp)
      | lam P => obtain ⟨K, hK, -⟩ := reduces_lam_shape hw3; exact absurd hK (by simp)
      | app A B =>
          have hA : Neutral A := by
            have := (isWhnf_app_iff.1 hw2)
            exact neutral_of_isWhnf this.1 this.2
          obtain ⟨A', B', hAB, hA', hB'⟩ := reduces_neutral_app hA hw3
          obtain ⟨rfl, rfl⟩ : M = A' ∧ N = B' := by
            injection hAB with h1 h2
            exact ⟨h1, h2⟩
          have hMn : Lambda.is_normal M := is_normal_of_app_left hu
          have hNn : Lambda.is_normal N := is_normal_of_app_right hu
          have hAM : NRed A M := ihM hMn A hA'
          have hBN : NRed B N := ihN hNn B hB'
          refine hw1.trans ((NRed.appL B hA hAM).trans ?_)
          exact NRed.appR (hA.reduces (NRed.reduces hAM)) hMn hBN

------------------------------------------------------------------------
-- The leftmost evaluator is normalizing
------------------------------------------------------------------------

theorem eval'_stop {c : ℕ} (h : Lambda.code_step' c = none) : Lambda.eval' c = Part.some c := by
  refine Part.eq_some_iff.mpr (PFun.fix_stop ?_)
  simp [Lambda.step_iter', h]

theorem eval'_forward {c c' : ℕ} (h : Lambda.code_step' c = some c') :
    Lambda.eval' c = Lambda.eval' c' := by
  refine PFun.fix_fwd_eq ?_
  simp [Lambda.step_iter', h]

/-- The leftmost evaluator computes the normal form reached by the normal order
strategy. -/
theorem eval'_of_nred {t u : Lambda} (h : NRed t u) (hu : Lambda.is_normal u) :
    Lambda.eval' (Lambda.encode t) = Part.some (Lambda.encode u) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine eval'_stop ?_
      rw [Lambda.code_step'_eq_step_normal, step_normal_eq_none_of_is_normal hu]
      rfl
  | head hstep _ ih =>
      refine Eq.trans (eval'_forward ?_) ih
      rw [Lambda.code_step'_eq_step_normal, hstep]
      rfl

/-- **The leftmost evaluator is normalizing.**  If a term has a normal form, the
leftmost-outermost evaluator finds it. -/
theorem eval'_complete {t u : Lambda} (h : Lambda.reduces t u) (hu : Lambda.is_normal u) :
    Lambda.eval' (Lambda.encode t) = Part.some (Lambda.encode u) :=
  eval'_of_nred (nred_of_reduces_normal u hu t h) hu

/-- **`Lambda.EvalNormalization` holds.**  The hypothesis isolated in
`Start/EvalCorrect.lean` is a theorem: leftmost-outermost evaluation finds the Church
numeral normal form whenever one exists. -/
theorem evalNormalization : Lambda.EvalNormalization := by
  intro t n hred
  have := eval'_complete hred (Lambda.church_normal n)
  rwa [Lambda.encode_church_eq_church_code] at this

/-- The corrected correctness statement for `Lambda.eval'` is now unconditional. -/
theorem evalCorrectness' : Lambda.EvalCorrectness' :=
  Lambda.evalCorrectness'_of_normalization evalNormalization

/-- Lambda-computable functions are partial recursive, unconditionally. -/
theorem partrec_of_lambdaComputable {f : ℕ →. ℕ} (hf : LambdaComputable f) : Partrec f :=
  LambdaComputable_imp_Partrec_of_normalization evalNormalization hf

end Lambda

end
