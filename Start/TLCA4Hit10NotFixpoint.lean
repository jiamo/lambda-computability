import Start.TLCA4Hit6NotFixpoint

/-!
# TLCA open problem 4: `hit10` is not a βη fixed-point combinator
(row M20-TLCA4-BETAETA; big round 2, item A3, rebuilt in run 6 after the move to a new project)

`hit10 = M ∘ M ∘ B²M ∘ BB ∘ BM ∘ B ∘ B` is not of the `stage_gen` form, but `hit10 x = M (M s)`
syntactically with `s = B²M w`, `w = BB (BM (B (B x)))` the `w`-term of `hit5`, and `s`
βη-reduces to

  `s₁₀ = λa w. x (a U_a (w (λc. x (a U_a (w c)))))`,  `U_a = λzw. x (a z w)`,

a component of index `0` of the grammar `NG` (`Start/TLCA4NfGrammar.lean`; `U_a` is `G_a` with
the tail `w`).  So `hit10 x →βη s₁₀ s₁₀ (M s₁₀)` and `not_fixedPoint_of_nf` applies.

* `hit10_act`, `h10s_red` (`s →βη s₁₀`), `s10nf_NG`;
* **`hit10_not_fixedPoint`**.
-/

set_option autoImplicit false
namespace TLCA4
open Tm
open Lambda (betaEtaReduces betaEtaStep)

theorem hit10_act (x : ℕ) :
    actList hit10 (var x) = app M (app M (app (app B (app B M)) (h5w x))) := rfl

/-- `λc. x (a U (w c))` under the binders `a w`. -/
def xi10 (x : ℕ) : Lambda :=
  .lam (.app (.var (x + 3)) (.app (.app (.var 2) (h5U3 x)) (.app (.var 1) (.var 0))))

/-- The normal form `λa w. x (a U_a (w (λc. x (a U_a (w c)))))` of the step term of `hit10`. -/
def s10nf (x : ℕ) : Lambda :=
  .lam (.lam (.app (.var (x + 2)) (.app (.app (.var 1) (h5U x)) (.app (.var 0) (xi10 x)))))

theorem lift_h5wnf (x : ℕ) : Lambda.lift 1 0 (h5wnf x) = h5wnf (x + 1) := by
  simp [h5wnf, h5U3, Lambda.lift]

theorem h10s_red (x : ℕ) :
    betaEtaReduces (toLam (app (app B (app B M)) (h5w x))) (s10nf x) := by
  show betaEtaReduces (.app (.app lamB (.app lamB lamM)) (toLam (h5w x))) _
  refine (betaEtaReduces_app_right _ (h5w_reduces x)).trans ?_
  refine (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)).trans (betaEtaReduces_lam ?_)
  simp only [Lambda.lift, lift_lamB, lift_lamM]
  refine (bm_red _).trans (betaEtaReduces_lam ?_)
  have hΦ : betaEtaReduces (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 (h5wnf x)) (.var 0)))
      (.var 0)) (xi10 x) := by
    simp only [Lambda.lift, lift_h5wnf]
    simp only [show ¬ (0 < 0) from by omega, ite_false]
    refine (betaEtaReduces_app_left _ (betaEtaReduces_beta _ _)).trans ?_
    refine (betaEtaReduces_beta _ _).trans ?_
    simp [h5U3, xi10, Lambda.subst, Lambda.lift]
    exact .refl _
  refine ((betaEtaReduces_app_left _ hΦ).trans (betaEtaReduces_app_right _ hΦ)).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp [xi10, h5U3, h5U, Lambda.subst]
  exact .refl _

theorem s10nf_NG (x : ℕ) : NG x 0 (s10nf x) := by
  have e : s10nf x = .lam (.lam (xPow (.var (x + 2)) 1
      (.app (Lambda.lift 1 0 (.app (.var 0) (qG x (.var 0)))) (.app (.var 0) (xi10 x))))) := by
    simp [s10nf, qG, h5U, xPow, Lambda.lift]
  rw [e]
  exact .lam (.rq (m := 1) (.base .q) rfl) (by norm_num)

/-- **`hit10` is not a βη fixed-point combinator.** -/
theorem hit10_not_fixedPoint (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit10 (var x)))
      (.app (.var x) (toLam (actList hit10 (var x)))) := by
  refine not_fixedPoint_of_nf (ρ := .app lamM (s10nf x)) (s10nf_NG x) ?_
  rw [hit10_act]
  exact (betaEtaReduces_app_right _ (betaEtaReduces_app_right _ (h10s_red x))).trans
    (mm_red _)

end TLCA4
