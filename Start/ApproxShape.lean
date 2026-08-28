/-
# The shape of a direct approximant

`Start/GraphApprox.lean` defines the approximation order `Lambda.Approx` and the direct
approximant `Lambda.direct`, which erases to `Ω` everything under a head redex.  An approximant
of a direct approximant is therefore very constrained: either it is dominated by an unsolvable
term, or it is a *spine* `λx₁ … x_b. x_h A₁ … A_k` whose shape is copied from the term it
approximates.

* `Lambda.direct_eq_var`, `Lambda.direct_eq_lam`, `Lambda.direct_eq_app` — inverting `direct`;
* `Lambda.approx_direct_shape` — **the shape lemma**: `Approx A (direct t)` forces either that
  `A` approximates an unsolvable term, or a common spine shape for `A` and `t` whose arguments
  are again related in the same way;
* `Lambda.size_lt_appList`, `Lambda.size_lamN` — the size bookkeeping which makes a structural
  induction along that shape well founded.
-/

import Start.GraphApprox
import Start.TermSize
import Start.HeadSpine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-! ## Size along a spine -/

theorem size_le_appList : ∀ (l : List Lambda) (t : Lambda), size t ≤ size (appList t l) := by
  intro l
  induction l with
  | nil => intro t; exact le_refl _
  | cons a rest ih =>
      intro t
      rw [appList_cons]
      exact le_trans (by simp only [size_app]; omega) (ih (Lambda.app t a))

theorem size_lt_appList : ∀ (l : List Lambda) (t a : Lambda), a ∈ l →
    size a < size (appList t l) := by
  intro l
  induction l with
  | nil => intro t a ha; exact absurd ha List.not_mem_nil
  | cons c rest ih =>
      intro t a ha
      rw [appList_cons]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact lt_of_lt_of_le (by simp only [size_app]; omega) (size_le_appList rest _)
      · exact ih (Lambda.app t c) a ha

theorem size_lamN : ∀ (b : ℕ) (t : Lambda), size (lamN b t) = size t + b := by
  intro b
  induction b with
  | zero => intro t; rw [lamN_zero]; omega
  | succ b ih => intro t; rw [lamN_succ, size_lam, ih]; omega

/-- Appending a single related pair to a `Forall₂`. -/
theorem forall₂_concat {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → R a b →
      List.Forall₂ R (as ++ [a]) (bs ++ [b]) := by
  intro as bs h hab
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons hx ih

/-! ## Inverting the direct approximant -/

theorem direct_eq_var {t : Lambda} {n : ℕ} (h : direct t = Lambda.var n) : t = Lambda.var n := by
  cases t with
  | var i => rw [direct_var] at h; exact h
  | lam s => rw [direct_lam] at h; exact absurd h (by simp)
  | app s u =>
      rw [direct_app] at h
      by_cases hh : headVar s
      · rw [if_pos hh] at h; exact absurd h (by simp)
      · rw [if_neg hh] at h; exact absurd h (by simp [Lambda.omega])

theorem direct_eq_lam {t s : Lambda} (h : direct t = Lambda.lam s) :
    ∃ t', t = Lambda.lam t' ∧ direct t' = s := by
  cases t with
  | var i => rw [direct_var] at h; exact absurd h (by simp)
  | lam u => rw [direct_lam] at h; exact ⟨u, rfl, by simpa using h⟩
  | app a b =>
      rw [direct_app] at h
      by_cases hh : headVar a
      · rw [if_pos hh] at h; exact absurd h (by simp)
      · rw [if_neg hh] at h; exact absurd h (by simp [Lambda.omega])

/-- Inverting `direct` at an application.  The second alternative is real: the direct approximant
of a head redex is `Ω`, which is itself an application. -/
theorem direct_eq_app {t s u : Lambda} (h : direct t = Lambda.app s u) :
    direct t = Lambda.omega ∨
      ∃ t₁ t₂, t = Lambda.app t₁ t₂ ∧ headVar t₁ ∧ direct t₁ = s ∧ direct t₂ = u := by
  cases t with
  | var i => rw [direct_var] at h; exact absurd h (by simp)
  | lam v => rw [direct_lam] at h; exact absurd h (by simp)
  | app a b =>
      rw [direct_app] at h
      by_cases hh : headVar a
      · rw [direct_app, if_pos hh]
        refine Or.inr ⟨a, b, rfl, hh, ?_, ?_⟩
        · rw [if_pos hh] at h
          exact (Lambda.app.injEq _ _ _ _ ▸ h).1
        · rw [if_pos hh] at h
          exact (Lambda.app.injEq _ _ _ _ ▸ h).2
      · exact Or.inl (by rw [direct_app, if_neg hh])

/-! ## The shape lemma -/

/-- **The shape of an approximant of a direct approximant.**  Either the approximant is dominated
by an unsolvable term, or it is a spine whose abstraction prefix and head variable are those of
the term it approximates, and whose arguments approximate the arguments of that term in the same
way. -/
theorem approx_direct_shape : ∀ (A u : Lambda), Approx A u → ∀ t, direct t = u →
    (∃ C, Approx A C ∧ ¬ HasHnf C) ∨ ∃ (b h : ℕ) (as bs : List Lambda),
      A = lamN b (appList (Lambda.var h) as) ∧ t = lamN b (appList (Lambda.var h) bs) ∧
        List.Forall₂ (fun a c => Approx a (direct c)) as bs := by
  intro A
  induction A with
  | var n =>
      intro u hA t hdt
      cases hA with
      | var n =>
          exact Or.inr ⟨0, n, [], [], rfl, direct_eq_var hdt, List.Forall₂.nil⟩
  | lam a ih =>
      intro u hA t hdt
      cases hA with
      | @lam _ s hs =>
          obtain ⟨t', rfl, hdir⟩ := direct_eq_lam hdt
          rcases ih s hs t' hdir with ⟨C, hAC, hC⟩ | ⟨b, h, as, bs, rfl, rfl, hall⟩
          · exact Or.inl ⟨Lambda.lam C, Approx.lam hAC, fun hc => hC (hasHnf_lam_iff.1 hc)⟩
          · exact Or.inr ⟨b + 1, h, as, bs, by rw [lamN_succ], by rw [lamN_succ], hall⟩
  | app a b iha _ =>
      intro u hA t hdt
      cases hA with
      | omega _ =>
          exact Or.inl ⟨Lambda.omega, Approx.omega _, GraphModel.not_hasHnf_omega⟩
      | @app _ _ s w hs hw =>
          rcases direct_eq_app hdt with homega | ⟨t₁, t₂, rfl, hhv, hd₁, hd₂⟩
          · refine Or.inl ⟨Lambda.omega, ?_, GraphModel.not_hasHnf_omega⟩
            have hle : Approx (Lambda.app a b) (direct t) := hdt ▸ Approx.app hs hw
            rw [homega] at hle
            exact hle
          · rcases iha s hs t₁ hd₁ with ⟨C, hAC, hC⟩ | ⟨b', hh, as, bs, rfl, ht₁, hall⟩
            · exact Or.inl ⟨Lambda.app C b, Approx.app hAC (Approx.refl b),
                fun hc => hC (HasHnf.app_left hc)⟩
            · have hb' : b' = 0 := by
                cases b' with
                | zero => rfl
                | succ k => rw [ht₁, lamN_succ] at hhv; simp at hhv
              subst hb'
              rw [lamN_zero] at ht₁ ⊢
              refine Or.inr ⟨0, hh, as ++ [b], bs ++ [t₂], ?_, ?_, ?_⟩
              · rw [lamN_zero, appList_concat]
              · rw [lamN_zero, appList_concat, ht₁]
              · exact forall₂_concat hall (hd₂ ▸ hw)

end Lambda
