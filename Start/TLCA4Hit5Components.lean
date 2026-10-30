import Start.TLCA4Hit5Stages
import Start.TLCA4QComponents
import Start.TLCA4YIndex

/-!
# TLCA open problem 4: the normal forms of the components of `hit5 x`
(row M20-TLCA4-BETAETA; series V, big round, run 8, item A3, plan 4.4 step 1)

The stages of `hit5 x` (`Start/TLCA4Hit5Stages.lean`) are `x^{tri n} (s (uⁿ s) Wₙ)` with
`u = B (B x)`.  The components `uⁿ s` have the βη-normal forms

  `bₙ = λa c. xⁿ⁺¹ (a U (λd. x (a U (c d))))`,  `U = λzw. x (a z w)`

(de Bruijn, `x` free).  This module proves this and gives the index function, as `tAnfQ`
did for `Q`:

* `h5Body`, `h5nf x n = bₙ`; **`h5nf_nf`** — every `bₙ` is βη-normal; **`h5nf_injective`**;
* `lift_h5nf`, `h5nf_app2`; **`Bx_h5nf_reduces`** — `B (B x) bₙ →β bₙ₊₁`;
* `bm_red`, `h5v_reduces`, `h5w_reduces`, **`h5s_reduces`** — `s →βη b₀`, through the normal
  forms `λaw. x (a U w)` of `v` and `λabc. x (a U (b c))` of `w`;
* **`h5A_reduces`** — every component `uⁿ s` βη-reduces to `bₙ`;
* **`h5A_index_unique`** — `uⁿ s =βη uᵐ s → n = m`.

Not proved here: a grammar for the reducts of `hit5 x` closed under βη (the analogue of `QShape`)
and `hit5_not_fixedPoint`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- `U = λzw. x (a z w)` under the binders `a c` (with `x` at `x + 2` there). -/
def h5U (x : ℕ) : Lambda :=
  .lam (.lam (.app (.var (x + 4)) (.app (.app (.var 3) (.var 1)) (.var 0))))

/-- `U` under three binders `a _ _` (with `x` at `x + 3` there). -/
def h5U3 (x : ℕ) : Lambda :=
  .lam (.lam (.app (.var (x + 5)) (.app (.app (.var 4) (.var 1)) (.var 0))))

/-- `λd. x (a U (c d))` under the binders `a c`. -/
def h5V (x : ℕ) : Lambda :=
  .lam (.app (.var (x + 3)) (.app (.app (.var 2) (h5U3 x)) (.app (.var 1) (.var 0))))

/-- The core `a U (λd. x (a U (c d)))` under the binders `a c`. -/
def h5Body (x : ℕ) : Lambda := .app (.app (.var 1) (h5U x)) (h5V x)

/-- `bₙ = λa c. xⁿ⁺¹ (a U (λd. x (a U (c d))))`. -/
def h5nf (x n : ℕ) : Lambda := .lam (.lam (xPow (.var (x + 2)) (n + 1) (h5Body x)))

theorem h5U_nf (x : ℕ) : BetaEtaNf (h5U x) := by
  have hin : ∀ i j k l : ℕ, BetaEtaNf (.app (.var i) (.app (.app (.var j) (.var k)) (.var l))) :=
    fun i j k l => betaEtaNf_app_var (betaEtaNf_app_of (betaEtaNf_app_var (betaEtaNf_var _))
      (betaEtaNf_var _) (by intro c h; simp at h))
  unfold h5U
  refine betaEtaNf_lam (betaEtaNf_lam (hin _ _ _ _) ?_) ?_ <;> intro f h <;> simp at h

theorem h5V_nf (x : ℕ) : BetaEtaNf (h5V x) := by
  unfold h5V h5U3
  refine betaEtaNf_lam (betaEtaNf_app_var (betaEtaNf_app_of (betaEtaNf_app_of
    (betaEtaNf_var _) (betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_app_var (betaEtaNf_app_of (betaEtaNf_app_var (betaEtaNf_var _)) (betaEtaNf_var _) (by intro c h; simp at h))) (by intro f h; simp at h)) (by intro f h; simp at h)) (by intro c h; simp at h))
    (betaEtaNf_app_var (betaEtaNf_var _)) (by intro c h; simp at h))) ?_
  intro f h; simp at h

theorem h5Body_nf (x : ℕ) : BetaEtaNf (h5Body x) :=
  betaEtaNf_app_of (betaEtaNf_app_of (betaEtaNf_var _) (h5U_nf x) (by intro c h; simp at h))
    (h5V_nf x) (by intro c h; simp at h)

theorem h5nf_nf (x n : ℕ) : BetaEtaNf (h5nf x n) := by
  unfold h5nf
  refine betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_xPow _ _ (h5Body_nf x)) ?_) ?_
  · intro f h
    simp only [xPow, Lambda.app.injEq] at h
    exact xPow_app_ne_var _ _ _ n 0 h.2
  · intro f h; simp at h

theorem h5nf_injective (x : ℕ) {n m : ℕ} (h : h5nf x n = h5nf x m) : n = m := by
  unfold h5nf at h
  simp only [Lambda.lam.injEq] at h
  have key : ∀ (n m : ℕ), xPow (.var (x + 2)) n (h5Body x) =
      xPow (.var (x + 2)) m (h5Body x) → n = m := by
    intro n m
    induction n generalizing m with
    | zero => cases m <;> simp [xPow, h5Body]
    | succ n ih =>
      cases m with
      | zero => simp [xPow, h5Body]
      | succ m => simp only [xPow, Lambda.app.injEq, true_and]; intro h; rw [ih m h]
  have := key _ _ h
  omega

theorem lift_h5nf (x n : ℕ) : Lambda.lift 1 0 (h5nf x n) = h5nf (x + 1) n := by
  have h1 : ¬ (x + 1 + 4 < 5) := by omega
  simp [h5nf, h5Body, h5U, h5U3, h5V, Lambda.lift, lift_xPow, h1, Nat.add_assoc, Nat.add_comm 1]

theorem h5nf_app2 (x n : ℕ) :
    Lambda.reduces (.app (.app (h5nf (x + 2) n) (.var 1)) (.var 0))
      (xPow (.var (x + 2)) (n + 1) (h5Body x)) := by
  refine Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces.step _ _ _
    (Lambda.step.beta _ _) (.refl _))) ?_
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
  simp [Lambda.subst, Lambda.lift, subst_xPow, h5Body, h5U, h5V]
  exact .refl _

/-- **`B (B x) bₙ →β bₙ₊₁`.** -/
theorem Bx_h5nf_reduces (x n : ℕ) :
    Lambda.reduces (.app (.app lamB (.app lamB (.var x))) (h5nf x n)) (h5nf x (n + 1)) := by
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  simp only [Lambda.lift, lift_h5nf]
  apply Lambda.reduces_lam
  refine Lambda.reduces_trans (reduces_B2 _ _) ?_
  apply Lambda.reduces_lam
  simp only [Lambda.lift, lift_h5nf]
  have := Lambda.reduces_app_right (t1 := .var (x + 2)) (h5nf_app2 x n)
  simpa [h5nf, xPow] using this

/-! ### `s →βη b₀` -/

/-- `B M F →βη λa. F a (F a)`. -/
theorem bm_red (F : Lambda) : betaEtaReduces (.app (.app lamB lamM) F)
    (.lam (.app (.app (Lambda.lift 1 0 F) (.var 0)) (.app (Lambda.lift 1 0 F) (.var 0)))) := by
  refine Lambda.betaEtaReduces.trans (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)) ?_
  refine betaEtaReduces_lam ?_
  have := betaEtaReduces_beta (.app (.var 0) (.var 0)) (.app (Lambda.lift 1 0 F) (.var 0))
  simpa [lamM, Lambda.lift, Lambda.subst] using this

/-- The normal form `λaw. x (a U w)` of `v = B M u`. -/
def h5vnf (x : ℕ) : Lambda :=
  .lam (.lam (.app (.var (x + 2)) (.app (.app (.var 1) (h5U x)) (.var 0))))

/-- The normal form `λabc. x (a U (b c))` of `w = B B v`. -/
def h5wnf (x : ℕ) : Lambda :=
  .lam (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (h5U3 x)) (.app (.var 1) (.var 0))))))

/-- `λbc. x (a U (b c))` under the binder `a`. -/
def h5wa (x : ℕ) : Lambda :=
  .lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (h5U3 x)) (.app (.var 1) (.var 0)))))

theorem h5v_reduces (x : ℕ) : betaEtaReduces (toLam (h5v x)) (h5vnf x) := by
  have hu : betaEtaReduces (toLam (h5u x)) (byl3 x) := ByR.to_byl3 (ByR.of_toLam x)
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ hu) ?_
  refine Lambda.betaEtaReduces.trans (bm_red _) ?_
  have h1 : betaEtaReduces (.app (Lambda.lift 1 0 (byl3 x)) (.var 0))
      (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) := by
    have := betaEtaReduces_beta
      (.lam (.lam (.app (.var (x + 1 + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) (.var 0)
    simpa [byl3, Lambda.lift, Lambda.subst] using this
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_lam (Lambda.betaEtaReduces.trans
    (betaEtaReduces_app_left _ h1) (betaEtaReduces_app_right _ h1))) ?_
  refine betaEtaReduces_lam ?_
  have := betaEtaReduces_beta (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))
    (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0)))))
  simpa [h5vnf, h5U, Lambda.lift, Lambda.subst] using this

theorem h5w_reduces (x : ℕ) : betaEtaReduces (toLam (h5w x)) (h5wnf x) := by
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ (h5v_reduces x)) ?_
  refine Lambda.betaEtaReduces.trans (Lambda.betaEtaReduces.of_reduces (reduces_B2 _ _)) ?_
  refine betaEtaReduces_lam ?_
  have h1 : betaEtaReduces (.app (Lambda.lift 1 0 (h5vnf x)) (.var 0))
      (.lam (.app (.var (x + 2)) (.app (.app (.var 1) (.lam (.lam (.app (.var (x + 4))
        (.app (.app (.var 3) (.var 1)) (.var 0)))))) (.var 0)))) := by
    have := betaEtaReduces_beta (.lam (.app (.var (x + 1 + 2)) (.app (.app (.var 1)
      (.lam (.lam (.app (.var (x + 1 + 4)) (.app (.app (.var 3) (.var 1)) (.var 0)))))) (.var 0))))
      (.var 0)
    simpa [h5vnf, h5U, Lambda.lift, Lambda.subst] using this
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ h1) ?_
  have h2 := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))
    (.lam (.app (.var (x + 2)) (.app (.app (.var 1) (.lam (.lam (.app (.var (x + 4))
      (.app (.app (.var 3) (.var 1)) (.var 0)))))) (.var 0))))
  have e : Lambda.lift 1 0 (toLam B) =
      .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) := rfl
  rw [e]
  refine Lambda.betaEtaReduces.trans h2 ?_
  simp [Lambda.subst, Lambda.lift, h5U3]
  refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
  have h3 := betaEtaReduces_beta (.app (.var (x + 4)) (.app (.app (.var 3) (.lam (.lam
    (.app (.var (x + 6)) (.app (.app (.var 5) (.var 1)) (.var 0)))))) (.var 0)))
    (.app (.var 1) (.var 0))
  have a1 : ¬ x + 4 < 3 := by omega
  have a2 : ¬ x + 4 + 1 < 3 := by omega
  simp [Lambda.subst, a1, a2] at h3 ⊢
  convert h3 using 4

/-- **`s →βη b₀`.** -/
theorem h5s_reduces (x : ℕ) : betaEtaReduces (toLam (h5s x)) (h5nf x 0) := by
  show betaEtaReduces _ (.lam (.lam (.app (.var (x + 2)) (.app (.app (.var 1) (h5U x)) (h5V x)))))
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ (h5w_reduces x)) ?_
  refine Lambda.betaEtaReduces.trans (bm_red _) ?_
  have h1 : betaEtaReduces (.app (Lambda.lift 1 0 (h5wnf x)) (.var 0)) (h5wa x) := by
    have := betaEtaReduces_beta (.lam (.lam (.app (.var (x + 1 + 3)) (.app (.app (.var 2) (.lam (.lam (.app (.var (x + 1 + 5)) (.app (.app (.var 4) (.var 1)) (.var 0)))))) (.app (.var 1) (.var 0)))))) (.var 0)
    simpa [h5wnf, h5wa, h5U3, Lambda.lift, Lambda.subst] using this
  refine Lambda.betaEtaReduces.trans (betaEtaReduces_lam (Lambda.betaEtaReduces.trans (betaEtaReduces_app_left _ h1) (betaEtaReduces_app_right _ h1))) ?_
  refine betaEtaReduces_lam ?_
  have h2 := betaEtaReduces_beta (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.lam (.lam (.app (.var (x + 5)) (.app (.app (.var 4) (.var 1)) (.var 0)))))) (.app (.var 1) (.var 0))))) (h5wa x)
  refine Lambda.betaEtaReduces.trans h2 ?_
  simp [Lambda.subst, h5wa, h5U3]
  refine betaEtaReduces_lam ?_
  have a1 : ¬ x + 5 < 4 := by omega
  simp only [a1, ite_false]
  refine betaEtaReduces_app_right _ (betaEtaReduces_app_right _ ?_)
  have h3 := betaEtaReduces_beta (.lam (.app (.var (x + 3 + 1)) (.app (.app (.var 3)
    (.lam (.lam (.app (.var (x + 5 + 1)) (.app (.app (.var 5) (.var 1)) (.var 0))))))
    (.app (.var 1) (.var 0))))) (.var 0)
  simp [Lambda.subst] at h3
  refine h3.trans ?_
  simp only [h5V]
  rw [show x + 1 + 4 = x + 5 by omega]
  exact .refl _

/-- **Every component `uⁿ s` βη-reduces to `bₙ`.** -/
theorem h5A_reduces (x : ℕ) : ∀ n : ℕ, betaEtaReduces (toLam (h5A x n)) (h5nf x n)
  | 0 => h5s_reduces x
  | n + 1 => Lambda.betaEtaReduces.trans (betaEtaReduces_app_right _ (h5A_reduces x n))
      (Lambda.betaEtaReduces.of_reduces (Bx_h5nf_reduces x n))

/-- **The index of a component is unique**: `uⁿ s =βη uᵐ s → n = m`. -/
theorem h5A_index_unique (x : ℕ) {n m : ℕ}
    (h : Lambda.betaEtaConv (toLam (h5A x n)) (toLam (h5A x m))) : n = m := by
  have hn := Lambda.betaEtaConv.of_reduces (h5A_reduces x n)
  have hm := Lambda.betaEtaConv.of_reduces (h5A_reduces x m)
  exact h5nf_injective x (Lambda.betaEtaNf_unique (h5nf_nf x n) (h5nf_nf x m)
    (((betaEtaConv_symm hn).trans h).trans hm))

end TLCA4
