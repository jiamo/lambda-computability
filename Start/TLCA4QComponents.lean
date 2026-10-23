import Start.TLCA4QStages

/-!
# TLCA open problem 4: the normal forms of the components `Aₙ[B x]` of `Q x`
(row M20-TLCA4-Q-NOT-FIXPOINT; series V, big round, run 1, item A1)

The components `Aₙ[y]` of `Start/TLCA4QStages.lean`, at `y = B x`, have βη-normal forms
`ãₙ = λz c. xⁿ⁺¹ (z (λw d. x (z w d)) c)` (`tAy_Bx_reduces_tAnfQ`).  This module gives the index function for them:

* `tAnfQ x n = ãₙ`; **`tAnfQ_nf`** — every `ãₙ` is βη-normal; **`tAnfQ_injective`**;
* `lift_tAnfQ`, `tAnfQ_app2`; **`Bx_tAnfQ_reduces`** — `B (B x) ãₙ →β ãₙ₊₁`;
* `tAy0_reducesQ`, **`tAy_Bx_reduces_tAnfQ`** — `Aₙ[B x] →β ãₙ`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

theorem betaEtaNf_app_of {f a : Lambda} (hf : BetaEtaNf f) (ha : BetaEtaNf a)
    (hl : ∀ c, f ≠ .lam c) : BetaEtaNf (.app f a) := by
  intro u hu
  rcases betaEtaStep_app_cases hu with ⟨c, hc, _⟩ | ⟨f', h', _⟩ | ⟨a', h', _⟩
  · exact hl c hc
  · exact hf _ h'
  · exact ha _ h'

/-- `ãₙ = λz c. xⁿ⁺¹ (z (λw d. x (z w d)) c)`, the βη-normal form of `Aₙ[B x]`. -/
def tAnfQ (x n : ℕ) : Lambda :=
  .lam (.lam (xPow (.var (x + 2)) (n + 1)
    (.app (.app (.var 1) (.lam (.lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 1))
      (.var 0)))))) (.var 0))))

theorem tAnfQ_nf (x n : ℕ) : BetaEtaNf (tAnfQ x n) := by
  have hin : ∀ i j k l : ℕ, BetaEtaNf (.app (.var i) (.app (.app (.var j) (.var k)) (.var l))) :=
    fun i j k l => betaEtaNf_app_var (betaEtaNf_app_of (betaEtaNf_app_var (betaEtaNf_var _))
      (betaEtaNf_var _) (by intro c h; simp at h))
  have hW : BetaEtaNf (.lam (.lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 1))
      (.var 0)))) : Lambda) := by
    refine betaEtaNf_lam (betaEtaNf_lam (hin _ _ _ _) ?_) ?_ <;> intro f h <;> simp at h
  unfold tAnfQ
  refine betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_xPow _ _ (betaEtaNf_app_of
    (betaEtaNf_app_var hW) (betaEtaNf_var _) (by intro c h; simp at h))) ?_) ?_
  · intro f h
    simp only [xPow, Lambda.app.injEq] at h
    exact xPow_app_ne_var _ _ _ n 0 h.2
  · intro f h; simp at h

theorem tAnfQ_injective (x : ℕ) {n m : ℕ} (h : tAnfQ x n = tAnfQ x m) : n = m := by
  unfold tAnfQ at h
  simp only [Lambda.lam.injEq] at h
  have key : ∀ (a b : Lambda) (n m : ℕ), xPow (.var (x + 2)) n (.app (.app (.var 1) a) (.var 0)) =
      xPow (.var (x + 2)) m (.app (.app (.var 1) b) (.var 0)) → n = m := by
    intro a b n m
    induction n generalizing m with
    | zero => cases m <;> simp [xPow]
    | succ n ih =>
      cases m with
      | zero => simp [xPow]
      | succ m => simp only [xPow, Lambda.app.injEq, true_and]; intro h; rw [ih m h]
  have := key _ _ _ _ h
  omega


theorem lift_tAnfQ (x n : ℕ) : Lambda.lift 1 0 (tAnfQ x n) = tAnfQ (x + 1) n := by
  simp [tAnfQ, Lambda.lift, lift_xPow]

theorem tAnfQ_app2 (x n : ℕ) :
    Lambda.reduces (.app (.app (tAnfQ (x + 2) n) (.var 1)) (.var 0))
      (xPow (.var (x + 2)) (n + 1) (.app (.app (.var 1) (.lam (.lam (.app (.var (x + 4))
        (.app (.app (.var 3) (.var 1)) (.var 0)))))) (.var 0))) := by
  refine Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces.step _ _ _
    (Lambda.step.beta _ _) (.refl _))) ?_
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
  simp [Lambda.subst, Lambda.lift, subst_xPow]
  exact .refl _

theorem Bx_tAnfQ_reduces (x n : ℕ) :
    Lambda.reduces (.app (.app lamB (.app lamB (.var x))) (tAnfQ x n)) (tAnfQ x (n + 1)) := by
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  simp only [Lambda.lift, lift_tAnfQ]
  apply Lambda.reduces_lam
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  apply Lambda.reduces_lam
  simp only [Lambda.lift, lift_tAnfQ]
  have := Lambda.reduces_app_right (t1 := .var (x + 2)) (tAnfQ_app2 x n)
  simpa [tAnfQ, xPow] using this

theorem tAy0_reducesQ (x : ℕ) :
    Lambda.reduces (toLam (tAy (app B (var x)) 0)) (tAnfQ x 0) := by
  show Lambda.reduces (.app (.app lamB lamM) (.app lamB (.app lamB (.var x)))) _
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  have hM : Lambda.lift 1 0 lamM = lamM := rfl
  rw [hM]
  apply Lambda.reduces_lam
  have e1 : Lambda.app (Lambda.lift 1 0 (.app lamB (.app lamB (.var x)))) (.var 0) =
      .app (.app lamB (.app lamB (.var (x + 1)))) (.var 0) := by
    simp [Lambda.lift, lamB]
  rw [e1]
  have hW1 : Lambda.reduces (.app (.app lamB (.app lamB (.var (x + 1)))) (.var 0))
      (.lam (.app (.app lamB (.var (x + 2))) (.app (.var 1) (.var 0)))) := by
    have := reduces_B2 (.app lamB (.var (x + 1))) (.var 0)
    simpa [Lambda.lift, lamB] using this
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
  simp only [Lambda.subst, if_pos]
  refine Lambda.reduces_trans (Lambda.reduces_app_left hW1) ?_
  have sB : ∀ (u : Lambda) (j : ℕ), Lambda.subst u j lamB = lamB := by
    intro u j; simp [lamB, Lambda.subst]
  have lB : ∀ (n k : ℕ), Lambda.lift n k lamB = lamB := by
    intro n k; simp [lamB, Lambda.lift]
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
  simp only [Lambda.subst, sB, if_pos, lt_irrefl, if_false]
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  apply Lambda.reduces_lam
  have hW2 : Lambda.reduces (.app (.app lamB (.app lamB (.var (x + 1)))) (.var 0))
      (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) := by
    refine Lambda.reduces_trans hW1 (Lambda.reduces_lam ?_)
    have := reduces_B2 (.var (x + 2)) (.app (.var 1) (.var 0))
    simpa [Lambda.lift] using this
  have h3 := Lambda.reduces_lift hW2 1 0
  simp only [Lambda.lift, lB] at h3 ⊢
  have h4 := Lambda.reduces_app_right (t1 := .var (x + 2))
    (Lambda.reduces_app_left (t2 := .var 0) (Lambda.reduces_app_right (t1 := .var 1) h3))
  simpa [tAnfQ, xPow] using h4
/-- **Every component `Aₙ[B x]` β-reduces to `ãₙ`.** -/
theorem tAy_Bx_reduces_tAnfQ (x : ℕ) :
    ∀ n : ℕ, Lambda.reduces (toLam (tAy (app B (var x)) n)) (tAnfQ x n)
  | 0 => tAy0_reducesQ x
  | n + 1 => Lambda.reduces_trans (Lambda.reduces_app_right (tAy_Bx_reduces_tAnfQ x n))
      (Bx_tAnfQ_reduces x n)

end TLCA4
