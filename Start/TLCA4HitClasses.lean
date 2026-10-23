import Start.TLCA4Hit5Components

/-!
# TLCA open problem 4: hit6 = hit7 and hit8 = hit9 up to βη
(row M20-TLCA4-BETAETA; series V, big round, run 8, item A3, plan 4.4 step 1)

Of the six length-7 spine hits without a factor `T` (`Start/TLCA4Candidates.lean`), `hit6`, `hit7`
end in `B²M ∘ F`, and `hit8`, `hit9` in `B³M ∘ F`, with two different tails `F`:
`F₆ = B ∘ BB ∘ B` (hit6, hit8) and `F₇ = B²B ∘ B ∘ B` (hit7, hit9).  Both tails, applied to `x`,
βη-reduce to the same normal form `λpqbc. x (p q (b c))` (`f6_red`, `f7_red`), so

* **`hit6_conv_hit7`** — `hit6 x =βη hit7 x`;
* **`hit8_conv_hit9`** — `hit8 x =βη hit9 x`.

Hence `hit7` is a βη fixed-point combinator iff `hit6` is, and likewise `hit9` and `hit8`: the six
hits without a factor `T` fall into at most four βη-classes, `hit5`, `hit6 ≡ hit7`, `hit8 ≡ hit9`,
`hit10`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- `λpqbc. x (p q (b c))`, the common normal form of `F₆ x` and `F₇ x`. -/
def fnf (x : ℕ) : Lambda :=
  .lam (.lam (.lam (.lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 2)) (.app (.var 1) (.var 0)))))))

/-- `λabc. x (a (b c))`, the normal form of `B B (B x)`. -/
def bbyn (x : ℕ) : Lambda :=
  .lam (.lam (.lam (.app (.var (x + 3)) (.app (.var 2) (.app (.var 1) (.var 0))))))

/-- `λgz. x (g z)`, the normal form of `B x`. -/
def byx (x : ℕ) : Lambda := .lam (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0))))

theorem bx_red (x : ℕ) : betaEtaReduces (toLam (app B (var x))) (byx x) := by
  have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (.var x)
  have e2 : x + 1 + 1 = x + 2 := by omega
  simpa [Lambda.subst, Lambda.lift, byx, toLam, lamB, e2] using this

theorem bby_red (x : ℕ) : betaEtaReduces (toLam (app (app B B) (app B (var x)))) (bbyn x) := by
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ (bx_red x)) ?_
  refine Lambda.betaEtaReduces.trans (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)) ?_
  refine betaEtaReduces_lam ?_
  have h1 : betaEtaReduces (.app (Lambda.lift 1 0 (byx x)) (.var 0))
      (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0)))) := by
    have := betaEtaReduces_beta (.lam (.app (.var (x + 1 + 2)) (.app (.var 1) (.var 0)))) (.var 0)
    simpa [byx, Lambda.lift, Lambda.subst] using this
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ h1) ?_
  have e : Lambda.lift 1 0 (toLam B) =
      .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) := rfl
  rw [e]
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_beta _ _) ?_
  simp [Lambda.subst, Lambda.lift]
  refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
  have h3 := betaEtaReduces_beta (.app (.var (x + 4)) (.app (.var 3) (.var 0))) (.app (.var 1) (.var 0))
  simp [Lambda.subst] at h3 ⊢
  rw [show x + 2 + 1 + 1 = x + 4 by omega]
  exact h3

theorem f6_red (x : ℕ) :
    betaEtaReduces (toLam (actList [mB, mBB, mB] (var x))) (fnf x) := by
  show betaEtaReduces (.app lamB (toLam (app (app B B) (app B (var x))))) _
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ (bby_red x)) ?_
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_beta _ _) ?_
  simp [Lambda.subst, Lambda.lift, bbyn, fnf]
  refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
  have h3 := betaEtaReduces_beta (.lam (.lam (.app (.var (x + 5)) (.app (.var 2)
    (.app (.var 1) (.var 0)))))) (.app (.var 1) (.var 0))
  have a1 : ¬ x + 3 + 1 < 3 := by omega
  simp only [a1, if_false, show x + 3 + 1 + 1 = x + 5 by omega]
  exact h3

theorem f7_red (x : ℕ) :
    betaEtaReduces (toLam (actList [mB2B, mB, mB] (var x))) (fnf x) := by
  have hu : betaEtaReduces (toLam (h5u x)) (byl3 x) := ByR.to_byl3 (ByR.of_toLam x)
  show betaEtaReduces (.app (.app lamB (.app lamB lamB)) (toLam (h5u x))) _
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ hu) ?_
  refine Lambda.betaEtaReduces.trans (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)) ?_
  refine betaEtaReduces_lam ?_
  have h1 : betaEtaReduces (.app (Lambda.lift 1 0 (byl3 x)) (.var 0))
      (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) := by
    have := betaEtaReduces_beta
      (.lam (.lam (.app (.var (x + 1 + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) (.var 0)
    simpa [byl3, Lambda.lift, Lambda.subst] using this
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ h1) ?_
  have e : Lambda.lift 1 0 (Lambda.app lamB lamB) = .app lamB lamB := rfl
  rw [e]
  refine Lambda.betaEtaReduces.trans (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)) ?_
  refine betaEtaReduces_lam ?_
  have h2 : betaEtaReduces (.app (Lambda.lift 1 0
      (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0)))))) (.var 0))
      (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0)))) := by
    have := betaEtaReduces_beta
      (.lam (.app (.var (x + 1 + 3)) (.app (.app (.var 3) (.var 1)) (.var 0)))) (.var 0)
    simp [Lambda.lift, Lambda.subst] at this ⊢
    rw [show x + 3 + 1 = x + 1 + 3 by omega]
    exact this
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ h2) ?_
  have e' : Lambda.lift 1 0 lamB = .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) := rfl
  rw [e']
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_beta _ _) ?_
  simp [Lambda.subst, Lambda.lift]
  refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
  have h3 := betaEtaReduces_beta (.app (.var (x + 5)) (.app (.app (.var 4) (.var 3)) (.var 0)))
    (.app (.var 1) (.var 0))
  simp [Lambda.subst] at h3 ⊢
  rw [show x + 3 + 1 + 1 = x + 5 by omega]
  exact h3

/-- The λ-context of a monomial list around a λ-term. -/
def lamAct : List Mono → Lambda → Lambda
  | [], N => N
  | m :: C, N => .app (toLam m.tm) (lamAct C N)

theorem actList_reduces_lamAct (t : Tm) (N : Lambda) (h : betaEtaReduces (toLam t) N) :
    ∀ C : List Mono, betaEtaReduces (toLam (actList C t)) (lamAct C N)
  | [] => h
  | _ :: C => betaEtaReduces_app_right _ (actList_reduces_lamAct t N h C)

/-- Two polynomials `C ∘ F` and `C ∘ F'` whose tails reduce to a common term are βη-equal. -/
theorem polyOf_conv_of_tails (C F F' : List Mono) (hC : C ≠ []) (x : ℕ) (N : Lambda)
    (hF : betaEtaReduces (toLam (actList F (var x))) N)
    (hF' : betaEtaReduces (toLam (actList F' (var x))) N) :
    Lambda.betaEtaConv (toLam (app (polyOf (C ++ F)) (var x)))
      (toLam (app (polyOf (C ++ F')) (var x))) := by
  have c1 := toLam_weq (hit_unfold (C ++ F) (by simp [hC]) (var x))
  have c2 := toLam_weq (hit_unfold (C ++ F') (by simp [hC]) (var x))
  rw [actList_append] at c1 c2
  have r1 := Lambda.betaEtaConv.of_reduces (actList_reduces_lamAct _ N hF C)
  have r2 := Lambda.betaEtaConv.of_reduces (actList_reduces_lamAct _ N hF' C)
  exact ((c1.trans r1).trans (betaEtaConv_symm r2)).trans (betaEtaConv_symm c2)

/-- **`hit6 x =βη hit7 x`.** -/
theorem hit6_conv_hit7 (x : ℕ) :
    Lambda.betaEtaConv (toLam (app (polyOf hit6) (var x))) (toLam (app (polyOf hit7) (var x))) :=
  polyOf_conv_of_tails [mM, mM, mBM, mB2M] [mB, mBB, mB] [mB2B, mB, mB] (by simp) x (fnf x)
    (f6_red x) (f7_red x)

/-- **`hit8 x =βη hit9 x`.** -/
theorem hit8_conv_hit9 (x : ℕ) :
    Lambda.betaEtaConv (toLam (app (polyOf hit8) (var x))) (toLam (app (polyOf hit9) (var x))) :=
  polyOf_conv_of_tails [mM, mM, mBM, mB3M] [mB, mBB, mB] [mB2B, mB, mB] (by simp) x (fnf x)
    (f6_red x) (f7_red x)

end TLCA4
