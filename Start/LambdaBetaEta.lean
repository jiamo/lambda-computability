/-
βη-reduction for the untyped λ-calculus: the Church–Rosser theorem.

`Start/Reduction.lean` proves β-reduction confluent (`Lambda.confluence_theorem`) and
`Start/LambdaEta.lean` proves η-reduction confluent (`Lambda.etaReduces_church_rosser`).
Neither fact alone gives confluence of the union: two confluent relations may have a
non-confluent union.  This module supplies the missing ingredient — β and η *commute* — and
runs the Hindley–Rosen argument to conclude that βη-reduction on untyped terms is confluent.

Contrast with `Start/LambdaPiEta.lean`, where the very same rules on the *raw* terms of `λΠ`
fail to be confluent: there the abstraction carries a domain annotation which β can rewrite but
η erases.  Untyped abstractions carry no annotation, so the obstruction disappears.

* `Lambda.step_lift_inv`, `Lambda.subst_var_lift_succ` — the two syntactic lemmas behind the
  critical pairs;
* `Lambda.etaStep_subst`, `Lambda.etaReduces_subst_arg` — η-reduction is substitutive;
* `Lambda.step_etaStep_commute` — the local commutation diagram: a β-step and an η-step out of
  the same term are joined by η-steps on one side and at most one β-step on the other;
* `Lambda.reduces_etaReduces_commute` — β-reduction and η-reduction commute;
* `Lambda.betaEtaStep`, `Lambda.betaEtaReduces` — βη-reduction;
* `Lambda.betaEta_church_rosser` — **βη-reduction is confluent**.
-/

import Start.LambdaEta
import Start.Reduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-! ### Two syntactic lemmas -/

/-- Substituting the variable `j` for itself undoes the lifting that made room for it. -/
theorem subst_var_lift_succ : ∀ (t : Lambda) (j : ℕ),
    Lambda.subst (Lambda.var j) j (Lambda.lift 1 (j + 1) t) = t := by
  intro t
  induction t with
  | var y =>
      intro j
      simp only [lift_var, Lambda.subst]
      split_ifs <;> first | rfl | (congr 1; omega)
  | app f a ihf iha => intro j; simp only [lift_app, Lambda.subst, ihf, iha]
  | lam b ihb =>
      intro j
      simp only [lift_lam, Lambda.subst, lift_var]
      norm_num
      exact ihb (j + 1)

/-- The general form of the reflection of a β-step through a lifting. -/
theorem step_lift_inv_aux : ∀ {t' w : Lambda}, Lambda.step t' w → ∀ {n k : ℕ} {t : Lambda},
    t' = Lambda.lift n k t → ∃ w₀, w = Lambda.lift n k w₀ ∧ Lambda.step t w₀ := by
  intro t' w h
  induction h with
  | beta b a =>
      intro n k t ht
      cases t with
      | app f₁ a₁ =>
          simp only [lift_app] at ht
          obtain ⟨hf, ha⟩ := Lambda.app.injEq _ _ _ _ ▸ ht
          cases f₁ with
          | lam b₁ =>
              simp only [lift_lam, Lambda.lam.injEq] at hf
              refine ⟨Lambda.subst a₁ 0 b₁, ?_, ?_⟩
              · rw [Lambda.lift_subst_zero, ← ha, ← hf]
              · exact Lambda.step.beta b₁ a₁
          | _ => simp at hf
      | _ => simp at ht
  | app_left f f' a _ ih =>
      intro n k t ht
      cases t with
      | app f₁ a₁ =>
          simp only [lift_app, Lambda.app.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.1
          exact ⟨Lambda.app w₀ a₁, by simp [hw₁, ht.2], Lambda.step.app_left _ _ _ hw₂⟩
      | _ => simp at ht
  | app_right f a a' _ ih =>
      intro n k t ht
      cases t with
      | app f₁ a₁ =>
          simp only [lift_app, Lambda.app.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.2
          exact ⟨Lambda.app f₁ w₀, by simp [hw₁, ht.1], Lambda.step.app_right _ _ _ hw₂⟩
      | _ => simp at ht
  | lam b b' _ ih =>
      intro n k t ht
      cases t with
      | lam b₁ =>
          simp only [lift_lam, Lambda.lam.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht
          exact ⟨Lambda.lam w₀, by simp [hw₁], Lambda.step.lam _ _ hw₂⟩
      | _ => simp at ht

/-- A β-step out of a lifted term is a lifted β-step. -/
theorem step_lift_inv {n k : ℕ} {t w : Lambda} (h : Lambda.step (Lambda.lift n k t) w) :
    ∃ w₀, w = Lambda.lift n k w₀ ∧ Lambda.step t w₀ :=
  step_lift_inv_aux h rfl

/-- A lifting is an abstraction only if the term lifted is. -/
theorem lift_eq_lam {n k : ℕ} {s c : Lambda} (h : Lambda.lift n k s = Lambda.lam c) :
    ∃ s₀, s = Lambda.lam s₀ ∧ c = Lambda.lift n (k + 1) s₀ := by
  cases s with
  | var y => simp at h
  | app f a => simp at h
  | lam s₀ => exact ⟨s₀, rfl, by simpa using h.symm⟩

/-- Inversion for a β-step out of an application. -/
theorem step_app_inv {f a w : Lambda} (h : Lambda.step (Lambda.app f a) w) :
    (∃ c, f = Lambda.lam c ∧ w = Lambda.subst a 0 c) ∨
      (∃ f', Lambda.step f f' ∧ w = Lambda.app f' a) ∨
      (∃ a', Lambda.step a a' ∧ w = Lambda.app f a') := by
  cases h with
  | beta c a' => exact Or.inl ⟨c, rfl, rfl⟩
  | app_left _ f' _ hf => exact Or.inr (Or.inl ⟨f', hf, rfl⟩)
  | app_right _ _ a' ha => exact Or.inr (Or.inr ⟨a', ha, rfl⟩)

/-- No β-step out of a variable. -/
theorem step.var_inv {n : ℕ} {w : Lambda} (h : Lambda.step (Lambda.var n) w) : False := by cases h

/-! ### η-reduction is substitutive -/

/-- η-reduction is stable under substitution in the term being reduced. -/
theorem etaStep_subst {t t' : Lambda} (h : etaStep t t') (s : Lambda) (x : ℕ) :
    etaStep (Lambda.subst s x t) (Lambda.subst s x t') := by
  induction h generalizing s x with
  | eta r =>
      have hkey : Lambda.subst (Lambda.lift 1 0 s) (x + 1) (Lambda.lift 1 0 r)
          = Lambda.lift 1 0 (Lambda.subst s x r) :=
        (Lambda.lift_subst r s 1 0 x (Nat.zero_le x)).symm
      have h0 : Lambda.subst (Lambda.lift 1 0 s) (x + 1) (Lambda.var 0) = Lambda.var 0 := by
        simp [Lambda.subst]
      change etaStep (Lambda.lam (Lambda.app _ _)) _
      rw [hkey, h0]
      exact etaStep.eta _
  | app_left a _ ih => exact etaStep.app_left _ (ih s x)
  | app_right f _ ih => exact etaStep.app_right _ (ih s x)
  | lam _ ih => exact etaStep.lam (ih (Lambda.lift 1 0 s) (x + 1))

/-- η-reduction in the term being substituted propagates to every occurrence. -/
theorem etaReduces_subst_arg : ∀ (t : Lambda) {a a' : Lambda} (x : ℕ), etaStep a a' →
    etaReduces (Lambda.subst a x t) (Lambda.subst a' x t) := by
  intro t
  induction t with
  | var y =>
      intro a a' x h
      simp only [Lambda.subst]
      split_ifs
      · exact etaReduces.single h
      · exact etaReduces.refl _
      · exact etaReduces.refl _
  | app f b ihf ihb =>
      intro a a' x h
      exact etaReduces.app (ihf x h) (ihb x h)
  | lam b ihb =>
      intro a a' x h
      exact etaReduces.lam (ihb (x + 1) (etaStep_lift h 1 0))

/-! ### β and η commute -/

/-- **Local commutation**: a β-step and an η-step out of the same term can be joined by
η-reduction on the β-side and at most one β-step on the η-side. -/
theorem step_etaStep_commute {t u v : Lambda} (hb : Lambda.step t u) (he : etaStep t v) :
    ∃ w, etaReduces u w ∧ (v = w ∨ Lambda.step v w) := by
  induction hb generalizing v with
  | beta b a =>
      cases he with
      | @app_left _ f' _ hf =>
          rcases hf.lam_inv with ⟨s, hbs, hfs⟩ | ⟨b', hb', hfs⟩
          · subst hbs
            rw [hfs]
            refine ⟨Lambda.app s a, ?_, Or.inl rfl⟩
            have hu : Lambda.subst a 0 (Lambda.app (Lambda.lift 1 0 s) (Lambda.var 0))
                = Lambda.app s a := by
              simp [Lambda.subst, Lambda.subst_lift]
            rw [hu]
            exact etaReduces.refl _
          · subst hfs
            exact ⟨Lambda.subst a 0 b', etaReduces.single (etaStep_subst hb' a 0),
              Or.inr (Lambda.step.beta b' a)⟩
      | app_right _ ha =>
          exact ⟨Lambda.subst _ 0 b, etaReduces_subst_arg b 0 ha, Or.inr (Lambda.step.beta b _)⟩
  | app_left f f' a hf ih =>
      cases he with
      | app_left _ hf₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih hf₂
          refine ⟨Lambda.app w a, hw₁.app_left a, ?_⟩
          rcases hw₂ with rfl | hw₂
          exacts [Or.inl rfl, Or.inr (Lambda.step.app_left _ _ _ hw₂)]
      | app_right _ ha₂ =>
          exact ⟨Lambda.app f' _, etaReduces.app_right f' (etaReduces.single ha₂),
            Or.inr (Lambda.step.app_left _ _ _ hf)⟩
  | app_right f a a' ha ih =>
      cases he with
      | app_left _ hf₂ =>
          exact ⟨Lambda.app _ a', etaReduces.app_left a' (etaReduces.single hf₂),
            Or.inr (Lambda.step.app_right _ _ _ ha)⟩
      | app_right _ ha₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih ha₂
          refine ⟨Lambda.app f w, hw₁.app_right f, ?_⟩
          rcases hw₂ with rfl | hw₂
          exacts [Or.inl rfl, Or.inr (Lambda.step.app_right _ _ _ hw₂)]
  | lam b b' hstep ih =>
      rcases he.lam_inv with ⟨s, hs, rfl⟩ | ⟨b₂, hb₂, rfl⟩
      · subst hs
        rcases step_app_inv hstep with ⟨c, hc, hb'⟩ | ⟨f', hf, hb'⟩ | ⟨a', ha, _⟩
        · obtain ⟨s₀, rfl, rfl⟩ := lift_eq_lam hc
          subst hb'
          refine ⟨Lambda.lam s₀, ?_, Or.inl ?_⟩
          · rw [subst_var_lift_succ s₀ 0]
            exact etaReduces.refl _
          · rfl
        · obtain ⟨s₀, rfl, hs₀⟩ := step_lift_inv hf
          subst hb'
          exact ⟨s₀, etaReduces.single (etaStep.eta s₀), Or.inr hs₀⟩
        · exact absurd ha step.var_inv
      · obtain ⟨w, hw₁, hw₂⟩ := ih hb₂
        refine ⟨Lambda.lam w, hw₁.lam, ?_⟩
        rcases hw₂ with rfl | hw₂
        exacts [Or.inl rfl, Or.inr (Lambda.step.lam _ _ hw₂)]

/-- One β-step commutes with many η-steps. -/
theorem step_etaReduces_commute {t u v : Lambda} (hb : Lambda.step t u) (he : etaReduces t v) :
    ∃ w, etaReduces u w ∧ (v = w ∨ Lambda.step v w) := by
  induction he with
  | refl => exact ⟨u, etaReduces.refl u, Or.inr hb⟩
  | @tail v₀ v _ hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      rcases hw₂ with rfl | hw₂
      · exact ⟨v, hw₁.tail hs, Or.inl rfl⟩
      · obtain ⟨w, hz₁, hz₂⟩ := step_etaStep_commute hw₂ hs
        exact ⟨w, hw₁.trans hz₁, hz₂⟩

/-- **β-reduction and η-reduction commute.** -/
theorem reduces_etaReduces_commute {t u v : Lambda} (hb : Lambda.reduces t u)
    (he : etaReduces t v) : ∃ w, etaReduces u w ∧ Lambda.reduces v w := by
  induction hb generalizing v with
  | refl => exact ⟨v, he, Lambda.reduces.refl v⟩
  | step t t₁ u hs _ ih =>
      obtain ⟨w₁, hw₁, hw₂⟩ := step_etaReduces_commute hs he
      obtain ⟨w, hw, hvw⟩ := ih hw₁
      refine ⟨w, hw, ?_⟩
      rcases hw₂ with rfl | hw₂
      · exact hvw
      · exact Lambda.reduces.step _ _ _ hw₂ hvw

/-! ### βη-reduction and its confluence -/

/-- One step of βη-reduction. -/
inductive betaEtaStep : Lambda → Lambda → Prop
  | beta {t u : Lambda} : Lambda.step t u → betaEtaStep t u
  | eta {t u : Lambda} : etaStep t u → betaEtaStep t u

/-- Many-step βη-reduction. -/
inductive betaEtaReduces : Lambda → Lambda → Prop
  | refl (t : Lambda) : betaEtaReduces t t
  | tail {t u v : Lambda} : betaEtaReduces t u → betaEtaStep u v → betaEtaReduces t v

namespace betaEtaReduces

theorem single {t u : Lambda} (h : betaEtaStep t u) : betaEtaReduces t u :=
  (betaEtaReduces.refl t).tail h

theorem trans {t u v : Lambda} (h₁ : betaEtaReduces t u) (h₂ : betaEtaReduces u v) :
    betaEtaReduces t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

theorem of_reduces {t u : Lambda} (h : Lambda.reduces t u) : betaEtaReduces t u := by
  induction h with
  | refl => exact betaEtaReduces.refl _
  | step _ _ _ hs _ ih => exact (single (betaEtaStep.beta hs)).trans ih

theorem of_etaReduces {t u : Lambda} (h : etaReduces t u) : betaEtaReduces t u := by
  induction h with
  | refl => exact betaEtaReduces.refl _
  | tail _ hs ih => exact ih.tail (betaEtaStep.eta hs)

end betaEtaReduces

/-- A β-phase followed by an η-phase.  This composite relation has the diamond property, which
is the Hindley–Rosen route to confluence of the union. -/
def betaEtaT (t u : Lambda) : Prop := ∃ m, Lambda.reduces t m ∧ etaReduces m u

/-- Reflexive–transitive closure of `betaEtaT`. -/
inductive betaEtaTStar : Lambda → Lambda → Prop
  | refl (t : Lambda) : betaEtaTStar t t
  | tail {t u v : Lambda} : betaEtaTStar t u → betaEtaT u v → betaEtaTStar t v

theorem betaEtaT.refl' (t : Lambda) : betaEtaT t t :=
  ⟨t, Lambda.reduces.refl t, etaReduces.refl t⟩

/-- The composite relation has the diamond property. -/
theorem betaEtaT.diamond {t u v : Lambda} (h₁ : betaEtaT t u) (h₂ : betaEtaT t v) :
    ∃ w, betaEtaT u w ∧ betaEtaT v w := by
  obtain ⟨m₁, hm₁, he₁⟩ := h₁
  obtain ⟨m₂, hm₂, he₂⟩ := h₂
  obtain ⟨n, hn₁, hn₂⟩ := Lambda.confluence_theorem hm₁ hm₂
  obtain ⟨p₁, hp₁, hq₁⟩ := reduces_etaReduces_commute hn₁ he₁
  obtain ⟨p₂, hp₂, hq₂⟩ := reduces_etaReduces_commute hn₂ he₂
  obtain ⟨q, hqa, hqb⟩ := etaReduces_church_rosser hp₁ hp₂
  exact ⟨q, ⟨p₁, hq₁, hqa⟩, ⟨p₂, hq₂, hqb⟩⟩

/-- The strip lemma for the composite relation. -/
theorem betaEtaTStar.strip {t u v : Lambda} (h₁ : betaEtaT t u) (h₂ : betaEtaTStar t v) :
    ∃ w, betaEtaTStar u w ∧ betaEtaT v w := by
  induction h₂ with
  | refl => exact ⟨u, betaEtaTStar.refl u, h₁⟩
  | @tail v₀ v _ hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      obtain ⟨z, hz₁, hz₂⟩ := hw₂.diamond hs
      exact ⟨z, hw₁.tail hz₁, hz₂⟩

/-- The composite relation is confluent. -/
theorem betaEtaTStar.confluent {t u v : Lambda} (h₁ : betaEtaTStar t u) (h₂ : betaEtaTStar t v) :
    ∃ w, betaEtaTStar u w ∧ betaEtaTStar v w := by
  induction h₁ with
  | refl => exact ⟨v, h₂, betaEtaTStar.refl v⟩
  | @tail u₀ u _ hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      obtain ⟨z, hz₁, hz₂⟩ := betaEtaTStar.strip hs hw₁
      exact ⟨z, hz₁, hw₂.tail hz₂⟩

theorem betaEtaTStar.toBetaEtaReduces {t u : Lambda} (h : betaEtaTStar t u) :
    betaEtaReduces t u := by
  induction h with
  | refl => exact betaEtaReduces.refl _
  | tail _ hs ih =>
      obtain ⟨m, hm, he⟩ := hs
      exact (ih.trans (betaEtaReduces.of_reduces hm)).trans (betaEtaReduces.of_etaReduces he)

theorem betaEtaReduces.toTStar {t u : Lambda} (h : betaEtaReduces t u) : betaEtaTStar t u := by
  induction h with
  | refl => exact betaEtaTStar.refl _
  | @tail u v _ hs ih =>
      refine ih.tail ?_
      cases hs with
      | beta hb => exact ⟨v, Lambda.reduces.step _ _ _ hb (Lambda.reduces.refl v),
          etaReduces.refl v⟩
      | eta he => exact ⟨u, Lambda.reduces.refl u, etaReduces.single he⟩

/-- **The Church–Rosser theorem for βη-reduction on untyped terms.** -/
theorem betaEta_church_rosser {t u v : Lambda} (h₁ : betaEtaReduces t u)
    (h₂ : betaEtaReduces t v) : ∃ w, betaEtaReduces u w ∧ betaEtaReduces v w := by
  obtain ⟨w, hw₁, hw₂⟩ := betaEtaTStar.confluent h₁.toTStar h₂.toTStar
  exact ⟨w, hw₁.toBetaEtaReduces, hw₂.toBetaEtaReduces⟩

/-- A term is βη-normal when no βη-step applies to it. -/
def BetaEtaNf (t : Lambda) : Prop := ∀ u, ¬ betaEtaStep t u

/-- A βη-normal term reduces only to itself. -/
theorem betaEtaReduces.eq_of_nf {t u : Lambda} (h : betaEtaReduces t u) (hn : BetaEtaNf t) :
    t = u := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact absurd hs (ih ▸ hn _)

/-- βη-convertibility: the equivalence relation generated by βη-reduction. -/
inductive betaEtaConv : Lambda → Lambda → Prop
  | refl (t : Lambda) : betaEtaConv t t
  | step {t u v : Lambda} : betaEtaConv t u → betaEtaStep u v → betaEtaConv t v
  | symm_step {t u v : Lambda} : betaEtaConv t u → betaEtaStep v u → betaEtaConv t v

theorem betaEtaConv.trans {t u v : Lambda} (h₁ : betaEtaConv t u) (h₂ : betaEtaConv u v) :
    betaEtaConv t v := by
  induction h₂ with
  | refl => exact h₁
  | step _ hs ih => exact ih.step hs
  | symm_step _ hs ih => exact ih.symm_step hs

theorem betaEtaConv.of_reduces {t u : Lambda} (h : betaEtaReduces t u) : betaEtaConv t u := by
  induction h with
  | refl => exact betaEtaConv.refl _
  | tail _ hs ih => exact ih.step hs

/-- **Confluence in the form of the Church–Rosser property**: βη-convertible terms have a
common βη-reduct. -/
theorem betaEtaConv.common_reduct {t u : Lambda} (h : betaEtaConv t u) :
    ∃ w, betaEtaReduces t w ∧ betaEtaReduces u w := by
  induction h with
  | refl => exact ⟨t, betaEtaReduces.refl t, betaEtaReduces.refl t⟩
  | @step u v _ hs ih =>
      obtain ⟨w, hw₁, hw₂⟩ := ih
      obtain ⟨z, hz₁, hz₂⟩ :=
        betaEta_church_rosser hw₂ (betaEtaReduces.single hs)
      exact ⟨z, hw₁.trans hz₁, hz₂⟩
  | @symm_step u v _ hs ih =>
      obtain ⟨w, hw₁, hw₂⟩ := ih
      exact ⟨w, hw₁, (betaEtaReduces.single hs).trans hw₂⟩

/-- **βη-normal forms are unique**: two βη-convertible βη-normal terms are equal. -/
theorem betaEtaNf_unique {u v : Lambda} (hu : BetaEtaNf u) (hv : BetaEtaNf v)
    (h : betaEtaConv u v) : u = v := by
  obtain ⟨w, hw₁, hw₂⟩ := h.common_reduct
  rw [hw₁.eq_of_nf hu, hw₂.eq_of_nf hv]

/-- A term has at most one βη-normal form. -/
theorem betaEtaNf_eq_of_reduces {t u v : Lambda} (h₁ : betaEtaReduces t u)
    (h₂ : betaEtaReduces t v) (hu : BetaEtaNf u) (hv : BetaEtaNf v) : u = v := by
  obtain ⟨w, hw₁, hw₂⟩ := betaEta_church_rosser h₁ h₂
  rw [hw₁.eq_of_nf hu, hw₂.eq_of_nf hv]

end Lambda
