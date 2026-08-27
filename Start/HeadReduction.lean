/-
Head reduction and the head normalization theorem.

`Start/HeadNormal.lean` defines head normal forms and head normalizability (`Lambda.HasHnf`)
through *arbitrary* reductions.  This file introduces the **head reduction strategy** — the weak
head steps of `Start/WeakHead.lean`, allowed also underneath a leading abstraction — and proves
that it is normalizing for head normal forms: a term has a head normal form if and only if the
head strategy terminates on it (`Lambda.hasHnf_iff_hasHeadEval`).  The argument reuses the
standardization theorem for weak head reduction (`Lambda.hasWhnfEval_of_reduces_whnf`) and
confluence, peeling off one leading abstraction at a time.

The strategy is deterministic and commutes with substitution, which yields the two structural
facts about head normalizability that arbitrary reductions do not give directly:

* `Lambda.hasHnf_of_hasHnf_subst` — if a substitution instance `t[s/x]` has a head normal form
  then so does `t` (equivalently: head divergence is preserved by substitution);
* `Lambda.HasHnf.app_left`        — if an application `M N` has a head normal form then so does
  its function part `M`.

Main definitions and results:

* `Lambda.hstep`                  — one head reduction step;
* `Lambda.isHnf_iff_no_hstep`     — head normal forms are exactly the terms with no head redex;
* `Lambda.hstep_deterministic`    — the strategy is deterministic;
* `Lambda.HNIn`, `Lambda.HasHeadEval` — termination of the strategy within `n` steps, and at all;
* `Lambda.hasHnf_iff_hasHeadEval` — **head normalization**;
* `Lambda.hasHnf_lam_iff`, `Lambda.hasHnf_of_hasHnf_subst`, `Lambda.HasHnf.app_left`.
-/

import Start.HeadNormal

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Head reduction
------------------------------------------------------------------------

/-- One step of *head* reduction: a weak head step, or a head step underneath a leading
abstraction. -/
inductive hstep : Lambda → Lambda → Prop
  | weak {M N : Lambda} : wstep M N → hstep M N
  | lam {P P' : Lambda} : hstep P P' → hstep (Lambda.lam P) (Lambda.lam P')

/-- Head steps are beta steps. -/
theorem hstep_imp_step {t t' : Lambda} (h : hstep t t') : Lambda.step t t' := by
  induction h with
  | weak hw => exact wstep_imp_step hw
  | lam _ ih => exact Lambda.step.lam _ _ ih

theorem hstep_reduces {t t' : Lambda} (h : hstep t t') : Lambda.reduces t t' :=
  Lambda.reduces.step _ _ _ (hstep_imp_step h) (Lambda.reduces.refl _)

/-- A head step out of a term that is not an abstraction is a weak head step. -/
theorem wstep_of_hstep_of_ne_lam {M M' : Lambda} (h : hstep M M')
    (hnl : ∀ P, M ≠ Lambda.lam P) : wstep M M' := by
  cases h with
  | weak hw => exact hw
  | @lam P P' _ => exact absurd rfl (hnl P)

/-- Head reduction is deterministic. -/
theorem hstep_deterministic {t t₁ t₂ : Lambda} (h₁ : hstep t t₁) (h₂ : hstep t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | weak hw =>
      cases h₂ with
      | weak hw' => exact wstep_deterministic hw hw'
      | lam _ => cases hw
  | @lam P P' _ ih =>
      cases h₂ with
      | weak hw => cases hw
      | lam h' => rw [ih h']

------------------------------------------------------------------------
-- Head normal forms are the head-irreducible terms
------------------------------------------------------------------------

/-- The body of an abstraction which is a head normal form is one. -/
theorem IsHnf.of_lam {P : Lambda} (h : IsHnf (Lambda.lam P)) : IsHnf P := by
  cases h with
  | neutral hn => exact absurd rfl (hn.ne_lam P)
  | lam h => exact h

/-- A neutral term is a weak head normal form. -/
theorem isWhnf_of_neutral {t : Lambda} (h : Neutral t) : IsWhnf t := by
  induction h with
  | var n => exact isWhnf_var n
  | app N hM ih => exact isWhnf_app_iff.2 ⟨ih, hM.ne_lam⟩

/-- A head normal form is a weak head normal form. -/
theorem IsWhnf.of_isHnf {t : Lambda} (h : IsHnf t) : IsWhnf t := by
  cases h with
  | neutral hn => exact isWhnf_of_neutral hn
  | lam _ => exact isWhnf_lam _

/-- Neutral terms have no head redex. -/
theorem not_hstep_of_neutral {t : Lambda} (h : Neutral t) : ∀ t', ¬ hstep t t' := by
  induction h with
  | var n =>
      intro t' hs
      cases hs with
      | weak hw => cases hw
  | @app M N hM ih =>
      intro t' hs
      have hw : wstep (Lambda.app M N) t' :=
        wstep_of_hstep_of_ne_lam hs (fun P h => Lambda.noConfusion h)
      cases hw with
      | beta P Q => exact absurd rfl (hM.ne_lam P)
      | app _ hM' => exact ih _ (hstep.weak hM')

/-- Head normal forms have no head redex. -/
theorem not_hstep_of_isHnf {t : Lambda} (h : IsHnf t) : ∀ t', ¬ hstep t t' := by
  induction h with
  | neutral hn => exact not_hstep_of_neutral hn
  | @lam P _ ih =>
      intro t' hs
      cases hs with
      | weak hw => cases hw
      | lam h' => exact ih _ h'

/-- A term with no head redex is a head normal form. -/
theorem exists_hstep_of_not_isHnf : ∀ {t : Lambda}, ¬ IsHnf t → ∃ t', hstep t t' := by
  intro t
  induction t with
  | var n => intro h; exact absurd (IsHnf.neutral (Neutral.var n)) h
  | lam P ih =>
      intro h
      obtain ⟨P', hP'⟩ := ih (fun hP => h (IsHnf.lam hP))
      exact ⟨Lambda.lam P', hstep.lam hP'⟩
  | app M N ihM _ =>
      intro h
      cases M with
      | lam P => exact ⟨Lambda.subst N 0 P, hstep.weak (wstep.beta P N)⟩
      | var n =>
          exact absurd (IsHnf.neutral (Neutral.app N (Neutral.var n))) h
      | app A B =>
          have hM : ¬ IsHnf (Lambda.app A B) := by
            intro hM
            cases hM with
            | neutral hn => exact h (IsHnf.neutral (Neutral.app N hn))
          obtain ⟨M', hM'⟩ := ihM hM
          have hw : wstep (Lambda.app A B) M' :=
            wstep_of_hstep_of_ne_lam hM' (fun P hP => Lambda.noConfusion hP)
          exact ⟨Lambda.app M' N, hstep.weak (wstep.app N hw)⟩

/-- **Head normal forms are exactly the terms with no head redex.** -/
theorem isHnf_iff_no_hstep {t : Lambda} : IsHnf t ↔ ∀ t', ¬ hstep t t' := by
  constructor
  · exact not_hstep_of_isHnf
  · intro h
    by_contra hc
    obtain ⟨t', ht'⟩ := exists_hstep_of_not_isHnf hc
    exact h t' ht'

------------------------------------------------------------------------
-- Termination of the head strategy
------------------------------------------------------------------------

/-- `HNIn n t` says that at most `n` head steps take `t` to a head normal form. -/
def HNIn : ℕ → Lambda → Prop
  | 0, t => IsHnf t
  | (n + 1), t => IsHnf t ∨ ∃ t', hstep t t' ∧ HNIn n t'

/-- `HasHeadEval t` says that the head strategy terminates on `t`. -/
def HasHeadEval (t : Lambda) : Prop := ∃ n, HNIn n t

theorem hnIn_mono {n m : ℕ} (hnm : n ≤ m) {t : Lambda} (h : HNIn n t) : HNIn m t := by
  induction m generalizing n t with
  | zero =>
      obtain rfl : n = 0 := Nat.le_zero.mp hnm
      exact h
  | succ m ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Or.inl h
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rcases h with h | ⟨t', hs, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨t', hs, ih (by omega) h'⟩

theorem hasHeadEval_of_isHnf {t : Lambda} (h : IsHnf t) : HasHeadEval t := ⟨0, h⟩

theorem hasHeadEval_of_hstep {t t' : Lambda} (hs : hstep t t') (h : HasHeadEval t') :
    HasHeadEval t := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, Or.inr ⟨t', hs, hn⟩⟩

theorem hnIn_lam {n : ℕ} {P : Lambda} (h : HNIn n P) : HNIn n (Lambda.lam P) := by
  induction n generalizing P with
  | zero => exact IsHnf.lam h
  | succ n ih =>
      rcases h with h | ⟨P', hs, h'⟩
      · exact Or.inl (IsHnf.lam h)
      · exact Or.inr ⟨Lambda.lam P', hstep.lam hs, ih h'⟩

theorem hasHeadEval_lam {P : Lambda} (h : HasHeadEval P) : HasHeadEval (Lambda.lam P) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hnIn_lam hn⟩

/-- A terminating head evaluation exhibits a head normal form reduct. -/
theorem exists_hnf_of_hnIn : ∀ (n : ℕ) {t : Lambda}, HNIn n t →
    ∃ u, Lambda.reduces t u ∧ IsHnf u := by
  intro n
  induction n with
  | zero => intro t h; exact ⟨t, Lambda.reduces.refl t, h⟩
  | succ n ih =>
      intro t h
      rcases h with h | ⟨t', hs, h'⟩
      · exact ⟨t, Lambda.reduces.refl t, h⟩
      · obtain ⟨u, hu1, hu2⟩ := ih h'
        exact ⟨u, Lambda.reduces.step _ _ _ (hstep_imp_step hs) hu1, hu2⟩

theorem hasHnf_of_hasHeadEval {t : Lambda} (h : HasHeadEval t) : HasHnf t := by
  obtain ⟨n, hn⟩ := h
  exact exists_hnf_of_hnIn n hn

------------------------------------------------------------------------
-- Head normalization
------------------------------------------------------------------------

/-- The number of leading abstractions of a term. -/
def lamCount : Lambda → ℕ
  | Lambda.lam P => lamCount P + 1
  | _ => 0

@[simp] theorem lamCount_lam (P : Lambda) : lamCount (Lambda.lam P) = lamCount P + 1 := rfl

theorem lamCount_of_neutral {t : Lambda} (h : Neutral t) : lamCount t = 0 := by
  cases h with
  | var n => rfl
  | app N _ => rfl

/-- A head normal form which is not an abstraction is neutral. -/
theorem neutral_of_isHnf_of_lamCount_zero {t : Lambda} (h : IsHnf t) (h0 : lamCount t = 0) :
    Neutral t := by
  cases h with
  | neutral hn => exact hn
  | @lam P _ => simp at h0

/-- Head normal forms are stable under reduction, and keep their abstraction prefix. -/
theorem IsHnf.reduces_shape {u : Lambda} (h : IsHnf u) : ∀ {v : Lambda}, Lambda.reduces u v →
    IsHnf v ∧ lamCount v = lamCount u := by
  induction h with
  | @neutral t hn =>
      intro v hr
      have hv : Neutral v := hn.reduces hr
      exact ⟨IsHnf.neutral hv, by rw [lamCount_of_neutral hv, lamCount_of_neutral hn]⟩
  | @lam P _ ih =>
      intro v hr
      obtain ⟨Q, rfl, hPQ⟩ := reduces_lam_shape hr
      obtain ⟨h1, h2⟩ := ih hPQ
      exact ⟨IsHnf.lam h1, by simp [h2]⟩

/-- If the weak head strategy terminates and every weak head normal form reduct of the term is
head-evaluable, then the head strategy terminates. -/
theorem hasHeadEval_of_whnIn : ∀ (n : ℕ) {t : Lambda}, WHNIn n t →
    (∀ w, IsWhnf w → Lambda.reduces t w → HasHeadEval w) → HasHeadEval t := by
  intro n
  induction n with
  | zero => intro t h hw; exact hw t h (Lambda.reduces.refl t)
  | succ n ih =>
      intro t h hwh
      rcases h with h | ⟨t', hs, h'⟩
      · exact hwh t h (Lambda.reduces.refl t)
      · refine hasHeadEval_of_hstep (hstep.weak hs) (ih h' ?_)
        intro w hw hr
        exact hwh w hw (Lambda.reduces_trans (hstep_reduces (hstep.weak hs)) hr)

/-- The inductive step of head normalization: the weak head strategy takes the term to a weak
head normal form, which is either neutral — and then already a head normal form — or an
abstraction, whose body is handled by the induction hypothesis with one abstraction fewer. -/
theorem hasHeadEval_peel {n : ℕ} {t u : Lambda} (hr : Lambda.reduces t u) (hu : IsHnf u)
    (hle : lamCount u ≤ n)
    (ih : ∀ (P v : Lambda), Lambda.reduces P v → IsHnf v → lamCount v + 1 ≤ n →
      HasHeadEval P) : HasHeadEval t := by
  obtain ⟨k, hk⟩ := hasWhnfEval_of_reduces_whnf hr (IsWhnf.of_isHnf hu)
  refine hasHeadEval_of_whnIn k hk ?_
  intro w hw hrw
  obtain ⟨v, hwv, huv⟩ := Lambda.confluence_theorem hrw hr
  obtain ⟨hv, hcv⟩ := hu.reduces_shape huv
  cases w with
  | var m => exact hasHeadEval_of_isHnf (IsHnf.neutral (Neutral.var m))
  | app A B =>
      have hA : IsWhnf A ∧ ∀ P, A ≠ Lambda.lam P := isWhnf_app_iff.1 hw
      exact hasHeadEval_of_isHnf
        (IsHnf.neutral (Neutral.app B (neutral_of_isWhnf hA.1 hA.2)))
  | lam P =>
      obtain ⟨v₀, rfl, hPv₀⟩ := reduces_lam_shape hwv
      have hv₀ : IsHnf v₀ := hv.of_lam
      have hcount : lamCount v₀ + 1 ≤ n := by
        have hcu : lamCount v₀ + 1 = lamCount u := by simpa using hcv
        omega
      exact hasHeadEval_lam (ih P v₀ hPv₀ hv₀ hcount)

/-- **The head strategy is normalizing**: a term that reduces to a head normal form is evaluated
to one by head reduction. -/
theorem hasHeadEval_of_reduces_isHnf : ∀ (n : ℕ) {t u : Lambda}, Lambda.reduces t u → IsHnf u →
    lamCount u ≤ n → HasHeadEval t := by
  intro n
  induction n with
  | zero =>
      intro t u hr hu hle
      exact hasHeadEval_peel hr hu hle (fun _ _ _ _ hlt => absurd hlt (by omega))
  | succ n ih =>
      intro t u hr hu hle
      exact hasHeadEval_peel hr hu hle (fun P v hPv hv hlt => ih hPv hv (by omega))

theorem hasHeadEval_of_hasHnf {t : Lambda} (h : HasHnf t) : HasHeadEval t := by
  obtain ⟨u, hr, hu⟩ := h
  exact hasHeadEval_of_reduces_isHnf (lamCount u) hr hu le_rfl

/-- **Head normalization.**  A term has a head normal form exactly when the head reduction
strategy terminates on it. -/
theorem hasHnf_iff_hasHeadEval {t : Lambda} : HasHnf t ↔ HasHeadEval t :=
  ⟨hasHeadEval_of_hasHnf, hasHnf_of_hasHeadEval⟩

------------------------------------------------------------------------
-- Structural consequences
------------------------------------------------------------------------

/-- Head steps are preserved by substitution. -/
theorem hstep_subst {M M' : Lambda} (h : hstep M M') :
    ∀ (Q : Lambda) (x : ℕ), hstep (Lambda.subst Q x M) (Lambda.subst Q x M') := by
  induction h with
  | weak hw => exact fun Q x => hstep.weak (wstep_subst hw Q x)
  | lam _ ih => exact fun Q x => hstep.lam (ih (Lambda.lift 1 0 Q) (x + 1))

/-- Head divergence is preserved by substitution: if a substitution instance of `P` is
head-evaluable then so is `P`. -/
theorem hasHeadEval_of_subst : ∀ (n : ℕ) {P Q : Lambda} {x : ℕ},
    HNIn n (Lambda.subst Q x P) → HasHeadEval P := by
  intro n
  induction n with
  | zero =>
      intro P Q x h
      by_contra hc
      obtain ⟨P', hP'⟩ := exists_hstep_of_not_isHnf (fun hP => hc (hasHeadEval_of_isHnf hP))
      exact not_hstep_of_isHnf h _ (hstep_subst hP' Q x)
  | succ n ih =>
      intro P Q x h
      by_cases hP : IsHnf P
      · exact hasHeadEval_of_isHnf hP
      obtain ⟨P', hP'⟩ := exists_hstep_of_not_isHnf hP
      rcases h with h | ⟨w, hs, hw⟩
      · exact absurd (hstep_subst hP' Q x) (not_hstep_of_isHnf h _)
      · have hwe : w = Lambda.subst Q x P' := hstep_deterministic hs (hstep_subst hP' Q x)
        subst hwe
        exact hasHeadEval_of_hstep hP' (ih hw)

/-- If a substitution instance of `P` has a head normal form then so does `P`. -/
theorem hasHnf_of_hasHnf_subst {P Q : Lambda} {x : ℕ} (h : HasHnf (Lambda.subst Q x P)) :
    HasHnf P := by
  obtain ⟨n, hn⟩ := hasHeadEval_of_hasHnf h
  exact hasHnf_of_hasHeadEval (hasHeadEval_of_subst n hn)

/-- Head evaluation of an application evaluates its function part. -/
theorem hasHeadEval_app_left : ∀ (n : ℕ) {M N : Lambda}, HNIn n (Lambda.app M N) →
    HasHeadEval M := by
  intro n
  induction n with
  | zero =>
      intro M N h
      cases h with
      | neutral hn =>
          cases hn with
          | app _ hM => exact hasHeadEval_of_isHnf (IsHnf.neutral hM)
  | succ n ih =>
      intro M N h
      rcases h with h | ⟨w, hs, hw⟩
      · cases h with
        | neutral hn =>
            cases hn with
            | app _ hM => exact hasHeadEval_of_isHnf (IsHnf.neutral hM)
      · have hwstep : wstep (Lambda.app M N) w :=
          wstep_of_hstep_of_ne_lam hs (fun P hP => Lambda.noConfusion hP)
        cases hwstep with
        | beta P Q => exact hasHeadEval_lam (hasHeadEval_of_subst n hw)
        | app _ hM => exact hasHeadEval_of_hstep (hstep.weak hM) (ih hw)

/-- **If an application has a head normal form then so does its function part.** -/
theorem HasHnf.app_left {M N : Lambda} (h : HasHnf (Lambda.app M N)) : HasHnf M := by
  obtain ⟨n, hn⟩ := hasHeadEval_of_hasHnf h
  exact hasHnf_of_hasHeadEval (hasHeadEval_app_left n hn)

/-- An abstraction has a head normal form exactly when its body does. -/
theorem hasHnf_lam_iff {P : Lambda} : HasHnf (Lambda.lam P) ↔ HasHnf P := by
  refine ⟨fun h => ?_, hasHnf_lam⟩
  obtain ⟨u, hr, hu⟩ := h
  obtain ⟨Q, rfl, hPQ⟩ := reduces_lam_shape hr
  exact ⟨Q, hPQ, hu.of_lam⟩

end Lambda

end
