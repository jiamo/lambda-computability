import Start.TLCA4YGrammar

/-!
# TLCA open problem 4: the index of a component of `Q x` is unique
(row M20-TLCA4-Q-NOT-FIXPOINT; series V, big round, run 3, item A1)

Every member of the grammar `YG x i` (`Start/TLCA4YGrammar.lean`) βη-reduces to the normal form
`ãᵢ = λz c. xⁱ⁺¹ (z (λw d. x (z w d)) c)` of `Aᵢ[B x]` (`tAnfQ`); with Church–Rosser and the
injectivity of `i ↦ ãᵢ` the index is unique.

* `chainNf x n` — the normal form of a chain of height `n` (`q W` for `n = 0`,
  `λd. xⁿ (q W d)` otherwise, `W = λzw. x (q z w)`); `tAnfQ_eq_chainNf`;
* `ByR.to_byl3`, `ByqR.to_bym3` — the reducts of `B (B x)` and `B (B x) q` reduce to their normal
  forms;
* **`YG.reduces_tAnfQ`**, `YC.reduces_chainNf`, `YBase.reduces_chainNf` — every member reduces to
  its normal form (mutual structural induction);
* **`YG.index_unique`** — the index of a member of `YG` is unique.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)


/-- `λzw. x (q z w)` in the context of a chain (`q` = `0`, `x` = `x + 1`). -/
def wq (x : ℕ) : Lambda := bym3 (x + 1)

/-- The normal form of a chain of height `n`. -/
def chainNf (x : ℕ) : ℕ → Lambda
  | 0 => .app (.var 0) (wq x)
  | n + 1 => .lam (xPow (.var (x + 2)) (n + 1) (.app (.app (.var 1) (Lambda.lift 1 0 (wq x))) (.var 0)))

theorem tAnfQ_eq_chainNf (x i : ℕ) : tAnfQ x i = .lam (chainNf x (i + 1)) := by
  simp [tAnfQ, chainNf, wq, bym3, Lambda.lift]

theorem ByR.to_byl3 {y : ℕ} {R : Lambda} (h : ByR y R) : betaEtaReduces R (byl3 y) := by
  have h23 : betaEtaReduces (byl2 y) (byl3 y) := by
    refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
    have := betaEtaReduces_beta (.lam (.app (.var (y + 2 + 2)) (.app (.var 1) (.var 0))))
      (.app (.var 1) (.var 0))
    simpa [Lambda.subst, Lambda.lift, bxPre] using this
  have h12 : betaEtaReduces (byl1 y) (byl3 y) := by
    refine Lambda.betaEtaReduces.trans ?_ h23
    refine betaEtaReduces_lam (betaEtaReduces_lam (betaEtaReduces_app_left _ ?_))
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (.var (y + 2))
    rwa [step_lamB_var] at this
  cases h with
  | bb =>
    refine Lambda.betaEtaReduces.trans ?_ h12
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))
      (.app lamB (.var y))
    simpa [Lambda.subst, Lambda.lift, byl1, lamB, bbx] using this
  | bpre =>
    refine Lambda.betaEtaReduces.trans ?_ h23
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (bxPre y)
    simpa [Lambda.subst, Lambda.lift, byl2, bxPre, bbpre, lamB] using this
  | l1 => exact h12
  | l2 => exact h23
  | l3 => exact .refl _

theorem ByqR.to_bym3 {y : ℕ} {R : Lambda} (h : ByqR y R) : betaEtaReduces R (bym3 y) := by
  have hl3 : betaEtaReduces (.app (byl3 y) (.var 0)) (bym3 y) := by
    have := betaEtaReduces_beta
      (.lam (.lam (.app (.var (y + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) (.var 0)
    simpa [Lambda.subst, Lambda.lift, bym3, byl3] using this
  have happ : ∀ {R : Lambda}, ByR y R → betaEtaReduces (.app R (.var 0)) (bym3 y) :=
    fun hR => (betaEtaReduces_app_left _ hR.to_byl3).trans hl3
  have h23 : betaEtaReduces (bym2 y) (bym3 y) := by
    refine betaEtaReduces_lam ?_
    have := betaEtaReduces_beta (.lam (.app (.var (y + 1 + 2)) (.app (.var 1) (.var 0))))
      (.app (.var 1) (.var 0))
    simpa [Lambda.subst, Lambda.lift, bxPre] using this
  cases h with
  | bb => exact happ .bb
  | bpre => exact happ .bpre
  | l1 => exact happ .l1
  | l2 => exact happ .l2
  | l3 => exact happ .l3
  | m1 =>
    refine Lambda.betaEtaReduces.trans ?_ h23
    refine betaEtaReduces_lam (betaEtaReduces_app_left _ ?_)
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (.var (y + 1))
    rwa [step_lamB_var] at this
  | m2 => exact h23
  | m3 => exact .refl _


theorem byl3_tAnfQ (x i : ℕ) :
    betaEtaReduces (.app (byl3 x) (tAnfQ x i)) (tAnfQ x (i + 1)) :=
  reduces_nf_of_reduct (.of_reduces (Bx_tAnfQ_reduces x i)) (tAnfQ_nf x (i + 1))
    (betaEtaReduces_app_left _ (ByR.bb.to_byl3 (y := x)))

theorem chain_succ {x n : ℕ} {C : Lambda} (h : betaEtaReduces C (chainNf x n)) :
    betaEtaReduces (.lam (.app (.var (x + 2)) (.app (Lambda.lift 1 0 C) (.var 0))))
      (chainNf x (n + 1)) := by
  refine (betaEtaReduces_lam (betaEtaReduces_app_right _
    (betaEtaReduces_app_left _ (betaEtaReduces_lift h)))).trans ?_
  cases n with
  | zero =>
    have : Lambda.lift 1 0 (chainNf x 0) = .app (.var 1) (Lambda.lift 1 0 (wq x)) := by
      simp [chainNf, Lambda.lift]
    rw [this]; simp only [chainNf, xPow]; exact .refl _
  | succ n =>
    have e : Lambda.lift 1 0 (chainNf x (n + 1)) = .lam (Lambda.lift 1 1
        (xPow (.var (x + 2)) (n + 1) (.app (.app (.var 1) (Lambda.lift 1 0 (wq x))) (.var 0)))) := by
      simp [chainNf]
    rw [e]
    refine (betaEtaReduces_lam (betaEtaReduces_app_right _ (betaEtaReduces_beta _ _))).trans ?_
    rw [Lambda.subst_var_lift_succ]
    exact .refl _

theorem wq_wq (x : ℕ) : betaEtaReduces (.app (wq x) (wq x)) (chainNf x 1) := by
  have := betaEtaReduces_beta
    (.lam (.app (.var (x + 1 + 2)) (.app (.app (.var 2) (.var 1)) (.var 0)))) (wq x)
  simp only [wq, bym3] at this ⊢
  refine this.trans ?_
  simp [Lambda.subst, Lambda.lift, chainNf, wq, bym3, xPow]
  exact .refl _


theorem A0_byl3 (x : ℕ) :
    betaEtaReduces (.app (.app lamB lamM) (byl3 x)) (tAnfQ x 0) :=
  reduces_nf_of_reduct (.of_reduces (tAy0_reducesQ x)) (tAnfQ_nf x 0)
    (betaEtaReduces_app_right _ (ByR.bb.to_byl3 (y := x)))

theorem A0pre1_byl3 (x : ℕ) : betaEtaReduces (.app bmPre1 (byl3 x)) (tAnfQ x 0) := by
  refine reduces_nf_of_reduct (A0_byl3 x) (tAnfQ_nf x 0) (betaEtaReduces_app_left _ ?_)
  have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) lamM
  rwa [step_lamB_M] at this

theorem A0pre2_byl3 (x : ℕ) : betaEtaReduces (.app bmPre2 (byl3 x)) (tAnfQ x 0) := by
  refine reduces_nf_of_reduct (A0pre1_byl3 x) (tAnfQ_nf x 0) (betaEtaReduces_app_left _ ?_)
  refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
  have := betaEtaReduces_beta (.app (.var 0) (.var 0)) (.app (.var 1) (.var 0))
  simpa [Lambda.subst, lamM] using this

mutual
theorem YG.reduces_tAnfQ {x i : ℕ} {P : Lambda} (h : YG x i P) :
    betaEtaReduces P (tAnfQ x i) := by
  match h with
  | .bm hR => exact (betaEtaReduces_app_right _ hR.to_byl3).trans (A0_byl3 x)
  | .bm1 hR => exact (betaEtaReduces_app_right _ hR.to_byl3).trans (A0pre1_byl3 x)
  | .bm2 hR => exact (betaEtaReduces_app_right _ hR.to_byl3).trans (A0pre2_byl3 x)
  | .byApp hR hP =>
    exact ((betaEtaReduces_app_left _ hR.to_byl3).trans
      (betaEtaReduces_app_right _ (YG.reduces_tAnfQ hP))).trans (byl3_tAnfQ x _)
  | .lam hc =>
    rw [tAnfQ_eq_chainNf]
    exact betaEtaReduces_lam (YC.reduces_chainNf hc)
theorem YC.reduces_chainNf {x n : ℕ} {C : Lambda} (h : YC x n C) :
    betaEtaReduces C (chainNf x n) := by
  match h with
  | .base hb => exact YBase.reduces_chainNf hb
  | .bx h =>
    refine Lambda.betaEtaReduces.trans (.of_reduces (reduces_B2 _ _)) ?_
    exact chain_succ (YC.reduces_chainNf h)
  | .bx1 h =>
    refine Lambda.betaEtaReduces.trans (betaEtaReduces_beta _ _) ?_
    have e : ∀ C : Lambda, Lambda.subst C 0
        (.lam (.app (.var (x + 1 + 2)) (.app (.var 1) (.var 0)))) =
        .lam (.app (.var (x + 2)) (.app (Lambda.lift 1 0 C) (.var 0))) := by
      intro C; simp [Lambda.subst]
    rw [e]
    exact chain_succ (YC.reduces_chainNf h)
  | @YC.rq _ n n' m R h hm =>
    refine (betaEtaReduces_lam (betaEtaReduces_xPow _ (betaEtaReduces_app_left _
      (betaEtaReduces_lift (YC.reduces_chainNf h))) m)).trans ?_
    cases n' with
    | zero =>
      have e : Lambda.lift 1 0 (chainNf x 0) = .app (.var 1) (Lambda.lift 1 0 (wq x)) := by
        simp [chainNf, Lambda.lift]
      rw [e]
      cases m with
      | zero =>
        subst hm
        have : Lambda.app (.app (.var 1) (Lambda.lift 1 0 (wq x))) (.var 0) =
            .app (Lambda.lift 1 0 (chainNf x 0)) (.var 0) := by rw [e]
        simp only [xPow]
        rw [this]
        exact .single (.eta (.eta _))
      | succ m =>
        subst hm
        exact .refl _
    | succ k =>
      have e : Lambda.lift 1 0 (chainNf x (k + 1)) = .lam (Lambda.lift 1 1
          (xPow (.var (x + 2)) (k + 1) (.app (.app (.var 1) (Lambda.lift 1 0 (wq x))) (.var 0)))) := by
        simp [chainNf]
      rw [e]
      refine (betaEtaReduces_lam (betaEtaReduces_xPow _ (betaEtaReduces_beta _ _) m)).trans ?_
      rw [Lambda.subst_var_lift_succ, xPow_add]
      subst hm
      have : m + (k + 1) = (m + k) + 1 := by omega
      rw [this]
      exact .refl _
theorem YBase.reduces_chainNf {x n : ℕ} {P : Lambda} (h : YBase x n P) :
    betaEtaReduces P (chainNf x n) := by
  match h with
  | .q hR => exact betaEtaReduces_app_right _ hR.to_bym3
  | .m hR =>
    refine (betaEtaReduces_beta _ _).trans ?_
    simp only [Lambda.subst, if_pos]
    exact ((betaEtaReduces_app_left _ hR.to_bym3).trans
      (betaEtaReduces_app_right _ hR.to_bym3)).trans (wq_wq x)
  | .rr h1 h2 =>
    exact ((betaEtaReduces_app_left _ h1.to_bym3).trans
      (betaEtaReduces_app_right _ h2.to_bym3)).trans (wq_wq x)
  | @YBase.comp _ i' R hR =>
    refine (betaEtaReduces_app_left _ (betaEtaReduces_lift (YG.reduces_tAnfQ hR))).trans ?_
    rw [lift_tAnfQ]
    refine (betaEtaReduces_beta _ _).trans ?_
    simp [Lambda.subst, Lambda.lift, chainNf, wq, bym3, subst_xPow]
    exact .refl _
end

/-- **The index of a component of `Q x` is unique.** -/
theorem YG.index_unique {x i j : ℕ} {P : Lambda} (hi : YG x i P) (hj : YG x j P) : i = j := by
  obtain ⟨w, h1, h2⟩ := Lambda.betaEta_church_rosser hi.reduces_tAnfQ hj.reduces_tAnfQ
  exact tAnfQ_injective x ((h1.eq_of_nf (tAnfQ_nf x i)).trans (h2.eq_of_nf (tAnfQ_nf x j)).symm)

end TLCA4
