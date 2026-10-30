import Start.TLCA4NfCores
import Start.TLCA4HitClasses
import Start.TLCA4StageGen

/-!
# TLCA open problem 4: `hit6`, `hit7`, `hit8`, `hit9` are not βη fixed-point combinators
(row M20-TLCA4-BETAETA; big round 2, item A2, rebuilt in run 6 after the move to a new project)

`hit6 x = M (M s)` and `hit8 x = M (M s')` with `s = B M g` (`Start/TLCA4StageGen.lean`).  The tail
`F = B (BB (B x))` βη-reduces to `fnf x = λpqbc. x (p q (b c))` (`f6_red`), so

* for `hit6`, `g a →βη G_a = λz w'. x (a z (Ψ w'))`-like terms (`h6g_qG`:
  `B M (F a) → λz. Ψ Ψ → λz c. x (a z (Ψ c))`), and for `hit8`, `g' a →βη λz w. x (a z (w Ψ))`
  (`h8g_qG`);
* `sComp_of_qG`: if `g a →βη G_a`, then `B M g` reduces to `nfStage x T₁ T`, a component of index
  `0` of the grammar `NG`;
* **`hit6_not_fixedPoint`**, **`hit8_not_fixedPoint`** (by `not_fixedPoint_of_nf`), and through
  `hit6_conv_hit7`, `hit8_conv_hit9`, **`hit7_not_fixedPoint`**, **`hit9_not_fixedPoint`**.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

theorem lift_lamM (k : ℕ) : Lambda.lift 1 k lamM = lamM := by
  simp [lamM, Lambda.lift]

theorem lift_fnf (x : ℕ) : Lambda.lift 1 0 (fnf x) = fnf (x + 1) := by
  simp [fnf, Lambda.lift]

theorem lamM_app_red (t : Lambda) : betaEtaReduces (.app lamM t) (.app t t) := by
  have := betaEtaReduces_beta (.app (.var 0) (.var 0)) t
  simp only [Lambda.subst, ite_eq_left] at this
  exact this

/-- `M (M S) →βη S S (M S)`. -/
theorem mm_red (S : Lambda) :
    betaEtaReduces (.app lamM (.app lamM S)) (.app (.app S S) (.app lamM S)) :=
  (lamM_app_red _).trans (betaEtaReduces_app_left _ (lamM_app_red S))

/-- If `g a →βη G_a`, then `B M g` βη-reduces to a component of index `0`
(`λa. g a (g a) →βη λa. G_a G_a →β λa w. x (a G_a T₁)`). -/
theorem sComp_of_qG {x : ℕ} {g : Tm} {T : Lambda}
    (hT : betaEtaReduces (.app (Lambda.lift 1 0 (toLam g)) (.var 0)) (qG x T)) :
    ∃ S, betaEtaReduces (toLam (app (app B M) g)) S ∧ NG x 0 S := by
  refine ⟨nfStage x (Lambda.subst (Lambda.lift 1 0 (qG x T)) 1 T) T, ?_, nfStage_NG x _ _⟩
  show betaEtaReduces (.app (.app lamB lamM) (toLam g)) _
  refine (bm_red _).trans (betaEtaReduces_lam ?_)
  refine ((betaEtaReduces_app_left _ hT).trans (betaEtaReduces_app_right _ hT)).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp [qG, Lambda.subst, Lambda.lift]
  exact .refl _

/-- `fnf y a z →β λbc. y (a z (b c))` under the binders `a z`. -/
theorem fnf_app2 (x : ℕ) : betaEtaReduces (.app (.app (fnf (x + 2)) (.var 1)) (.var 0))
    (.lam (.lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 2)) (.app (.var 1) (.var 0)))))) := by
  refine (betaEtaReduces_app_left _ (betaEtaReduces_beta _ _)).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp [Lambda.subst, Lambda.lift]
  exact .refl _

/-- `λbc. x (a z (b c))` under the binders `a z` (`x` at index `x + 2` outside). -/
def psi6 (x : ℕ) : Lambda :=
  .lam (.lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 2)) (.app (.var 1) (.var 0)))))

/-- If `F` reduces to `fnf x`, then `B M (F a)` reduces to `G_a` with tail `Ψ c`. -/
theorem bmF_qG {x : ℕ} {F : Lambda} (hF : betaEtaReduces F (fnf x)) :
    betaEtaReduces (.app (.app lamB lamM) (.app (Lambda.lift 1 0 F) (.var 0)))
      (qG x (.app (Lambda.lift 1 0 (psi6 x)) (.var 0))) := by
  have hF2 : betaEtaReduces (Lambda.lift 1 0 (Lambda.lift 1 0 F)) (fnf (x + 2)) := by
    have := betaEtaReduces_lift (betaEtaReduces_lift hF)
    rwa [lift_fnf, lift_fnf] at this
  have hΦ : betaEtaReduces (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 F) (.var 0))) (.var 0))
      (psi6 x) := by
    simp only [Lambda.lift]
    simp only [show ¬ (0 < 0) from by omega, ite_false]
    refine (betaEtaReduces_app_left _ (betaEtaReduces_app_left _ hF2)).trans ?_
    exact fnf_app2 x
  refine (bm_red _).trans (betaEtaReduces_lam ?_)
  refine ((betaEtaReduces_app_left _ hΦ).trans (betaEtaReduces_app_right _ hΦ)).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp [psi6, Lambda.subst, Lambda.lift]
  exact .refl _

/-- `g a →βη G_a` for `hit6`. -/
theorem h6g_qG (x : ℕ) : ∃ T, betaEtaReduces (.app (Lambda.lift 1 0 (toLam (h6g x))) (.var 0))
    (qG x T) := by
  refine ⟨.app (Lambda.lift 1 0 (psi6 x)) (.var 0), ?_⟩
  show betaEtaReduces (.app (Lambda.lift 1 0 (.app (.app lamB (.app lamB lamM)) (toLam (h6F x))))
    (.var 0)) _
  simp only [Lambda.lift, lift_lamB, lift_lamM]
  refine (betaEtaReduces_app_left _ (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _))).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp only [Lambda.subst, Lambda.lift, lift_lamB, lift_lamM, Lambda.subst_lift, subst_lamB,
    subst_lamM, ite_true]
  exact bmF_qG (f6_red x)

/-- **`hit6` is not a βη fixed-point combinator**: `hit6 x` is not βη-convertible to
`x (hit6 x)`. -/
theorem hit6_not_fixedPoint (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit6 (var x)))
      (.app (.var x) (toLam (actList hit6 (var x)))) := by
  obtain ⟨T, hT⟩ := h6g_qG x
  obtain ⟨S, hS, hNG⟩ := sComp_of_qG hT
  refine not_fixedPoint_of_nf (ρ := .app lamM S) hNG ?_
  rw [hit6_act]
  exact (betaEtaReduces_app_right _ (betaEtaReduces_app_right _ hS)).trans (mm_red S)

/-- `λc. x (a z (w c))` under the binders `a z w` (`x` at index `x + 3` outside). -/
def psi8 (x : ℕ) : Lambda :=
  .lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 2)) (.app (.var 1) (.var 0))))

theorem fnf_app3 (x : ℕ) :
    betaEtaReduces (.app (.app (.app (fnf (x + 3)) (.var 2)) (.var 1)) (.var 0)) (psi8 x) := by
  refine (betaEtaReduces_app_left _ (betaEtaReduces_app_left _ (betaEtaReduces_beta _ _))).trans ?_
  refine (betaEtaReduces_app_left _ (betaEtaReduces_beta _ _)).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp [psi8, Lambda.subst, Lambda.lift]
  exact .refl _

/-- `g' a →βη G_a` for `hit8`. -/
theorem h8g_qG (x : ℕ) : ∃ T, betaEtaReduces (.app (Lambda.lift 1 0 (toLam (h8g x))) (.var 0))
    (qG x T) := by
  have hF3 : betaEtaReduces (Lambda.lift 1 0 (Lambda.lift 1 0 (Lambda.lift 1 0 (toLam (h6F x)))))
      (fnf (x + 3)) := by
    have := betaEtaReduces_lift (betaEtaReduces_lift (betaEtaReduces_lift (f6_red x)))
    rwa [lift_fnf, lift_fnf, lift_fnf] at this
  refine ⟨.app (.var 0) (psi8 x), ?_⟩
  show betaEtaReduces (.app (Lambda.lift 1 0
    (.app (.app lamB (.app lamB (.app lamB lamM))) (toLam (h6F x)))) (.var 0)) _
  simp only [Lambda.lift, lift_lamB, lift_lamM]
  refine (betaEtaReduces_app_left _ (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _))).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp only [Lambda.subst, Lambda.lift, lift_lamB, lift_lamM, Lambda.subst_lift, subst_lamB,
    subst_lamM, ite_true]
  refine (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)).trans (betaEtaReduces_lam ?_)
  simp only [Lambda.lift, lift_lamB, lift_lamM]
  refine (bm_red _).trans (betaEtaReduces_lam ?_)
  have hΦ : betaEtaReduces (.app (Lambda.lift 1 0 (.app (.app (Lambda.lift 1 0 (Lambda.lift 1 0
      (toLam (h6F x)))) (.var 1)) (.var 0))) (.var 0)) (psi8 x) := by
    simp only [Lambda.lift]
    simp only [show ¬ (0 < 0) from by omega, show ¬ (1 < 0) from by omega, ite_false]
    exact (betaEtaReduces_app_left _ (betaEtaReduces_app_left _
      (betaEtaReduces_app_left _ hF3))).trans (fnf_app3 x)
  refine ((betaEtaReduces_app_left _ hΦ).trans (betaEtaReduces_app_right _ hΦ)).trans ?_
  refine (betaEtaReduces_beta _ _).trans ?_
  simp [psi8, Lambda.subst]
  exact .refl _

/-- **`hit8` is not a βη fixed-point combinator.** -/
theorem hit8_not_fixedPoint (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit8 (var x)))
      (.app (.var x) (toLam (actList hit8 (var x)))) := by
  obtain ⟨T, hT⟩ := h8g_qG x
  obtain ⟨S, hS, hNG⟩ := sComp_of_qG hT
  refine not_fixedPoint_of_nf (ρ := .app lamM S) hNG ?_
  rw [hit8_act]
  exact (betaEtaReduces_app_right _ (betaEtaReduces_app_right _ hS)).trans (mm_red S)

/-- Non-fixedness transfers along βη-conversion. -/
theorem not_fixedPoint_of_conv {x : ℕ} {L L' : Lambda} (h : Lambda.betaEtaConv L L')
    (h' : ¬ Lambda.betaEtaConv L' (.app (.var x) L')) :
    ¬ Lambda.betaEtaConv L (.app (.var x) L) := fun hL =>
  h' ((betaEtaConv_symm h).trans (hL.trans (betaEtaConv_app_right _ h)))

theorem polyOf_conv_actList (L : List Mono) (hL : L ≠ []) (x : ℕ) :
    Lambda.betaEtaConv (toLam (app (polyOf L) (var x))) (toLam (actList L (var x))) :=
  toLam_weq (hit_unfold L hL (var x))

/-- **`hit7` is not a βη fixed-point combinator** (`hit7 x =βη hit6 x`). -/
theorem hit7_not_fixedPoint (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit7 (var x)))
      (.app (.var x) (toLam (actList hit7 (var x)))) := by
  refine not_fixedPoint_of_conv ?_ (hit6_not_fixedPoint x)
  exact ((betaEtaConv_symm (polyOf_conv_actList hit7 (by simp [hit7]) x)).trans
    (betaEtaConv_symm (hit6_conv_hit7 x))).trans (polyOf_conv_actList hit6 (by simp [hit6]) x)

/-- **`hit9` is not a βη fixed-point combinator** (`hit9 x =βη hit8 x`). -/
theorem hit9_not_fixedPoint (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit9 (var x)))
      (.app (.var x) (toLam (actList hit9 (var x)))) := by
  refine not_fixedPoint_of_conv ?_ (hit8_not_fixedPoint x)
  exact ((betaEtaConv_symm (polyOf_conv_actList hit9 (by simp [hit9]) x)).trans
    (betaEtaConv_symm (hit8_conv_hit9 x))).trans (polyOf_conv_actList hit8 (by simp [hit8]) x)

end TLCA4
