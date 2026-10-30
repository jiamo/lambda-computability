import Start.TLCA4Hit5W

/-!
# TLCA open problem 4: the `s`-layer of `hit5`
(row M20-TLCA4-BETAETA; series V, big round, run 10, item A3, plan 4.4 step 2)

The next layer after `Start/TLCA4Hit5W.lean`: the reducts of `s = B M W` with `W` a reduct of
`w`.

* **`TC.subst_liftB`** — substituting any term for the extra binder of a lifted chain gives a
  chain over the original base (this is how `(λb. C) Y` fires);
* `WqF x` — the reducts of `W q` (`W ∈ WR x`, `q` = variable `0`): `W q` itself and the bodies
  `WqR x`;
* `SqR x` — the bodies under `q` of the `s`-reducts: `M Wq`, `Wq Y` (`Wq ∈ WqF x`, `Y`
  arbitrary) and chains of height `1` over the cores of `Q`;
* `SR x` — `B M W`, `(λab. M (a b)) W`, `(λab. a b (a b)) W` (`W ∈ WR x`), `λq. S`
  (`S ∈ SqR x`), and the η-contracta (components `V ∈ YG x 0`, and `f` with `f q ∈ WqF x`);
* **`WqF.step`**, **`SqR.step`**, **`SR.step`**, `SR.reduces` — closure under βη;
* **`SR.of_h5s`**, `SR.of_reduces` — `s` and all its βη-reducts are in the grammar.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

theorem subst_lamB (s : Lambda) (k : ℕ) : Lambda.subst s k lamB = lamB := by
  simp [lamB, Lambda.subst]

theorem subst_bxPre (s : Lambda) (y : ℕ) : Lambda.subst s 0 (bxPre (y + 1)) = bxPre y := by
  simp [bxPre, Lambda.subst]

/-- **Firing a lifted chain**: substituting for the extra binder gives a chain over the base. -/
theorem TC.subst_liftB {base : ℤ → Lambda → Prop} {x : ℕ} {i : ℤ} {C : Lambda} (Y : Lambda)
    (h : TC (LiftB base) (x + 1) i C) : TC base x i (Lambda.subst Y 0 C) := by
  generalize ex : x + 1 = x' at h
  induction h with
  | base hb =>
    obtain ⟨P0, hb, rfl⟩ := hb
    rw [Lambda.subst_lift]; exact .base hb
  | @bx i P _ ih =>
    subst ex
    have e : Lambda.subst Y 0 (.app (.app lamB (.var (x + 1))) P) =
        .app (.app lamB (.var x)) (Lambda.subst Y 0 P) := by
      simp [Lambda.subst, subst_lamB]
    rw [e]; exact .bx ih
  | @bx1 i P _ ih =>
    subst ex
    have e : Lambda.subst Y 0 (.app (bxPre (x + 1)) P) = .app (bxPre x) (Lambda.subst Y 0 P) := by
      simp only [Lambda.subst, subst_bxPre]
    rw [e]; exact .bx1 ih
  | @rq i i' m R T _ hm ih =>
    subst ex
    have e : Lambda.subst Y 0 (.lam (xPow (.var (x + 1 + 1)) m (.app (Lambda.lift 1 0 R) T))) =
        .lam (xPow (.var (x + 1)) m
          (.app (Lambda.lift 1 0 (Lambda.subst Y 0 R)) (Lambda.subst (Lambda.lift 1 0 Y) 1 T))) := by
      simp only [Lambda.subst, subst_xPow]
      rw [Lambda.lift_subst R Y 1 0 0 (le_refl 0)]
      simp
    rw [e]; exact .rq ih hm

theorem subst_var_lift_succ : ∀ (W : Lambda) (k : ℕ),
    Lambda.subst (.var k) k (Lambda.lift 1 (k + 1) W) = W
  | .var n, k => by
    simp only [Lambda.lift]
    split_ifs with h1
    · simp only [Lambda.subst]; split_ifs <;> first | rfl | (congr 1; omega)
    · simp only [Lambda.subst]; split_ifs <;> first | rfl | (congr 1; omega)
  | .app a b, k => by
    simp only [Lambda.lift, Lambda.subst, subst_var_lift_succ a k, subst_var_lift_succ b k]
  | .lam b, k => by
    simp only [Lambda.lift, Lambda.subst, ite_eq_right (Nat.not_lt_zero k)]
    rw [subst_var_lift_succ b (k + 1)]

/-- The reducts of `W q` with `W ∈ WR x` (`q` = variable `0`, `x` at `x + 1`). -/
inductive WqF (x : ℕ) : Lambda → Prop
  | ap {W : Lambda} : WR x W → WqF x (.app (Lambda.lift 1 0 W) (.var 0))
  | body {W : Lambda} : WqR x W → WqF x W

theorem WqF.step {x : ℕ} {P P' : Lambda} (h : WqF x P) (hs : betaEtaStep P P') : WqF x P' := by
  cases h with
  | @ap W hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · obtain ⟨W0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
      rw [subst_var_lift_succ W0 0]
      cases hW with
      | wlam hq => exact .body hq
    · obtain ⟨W', rfl, hW'⟩ := betaEtaStep_lift_inv hf
      exact .ap (hW.step hW')
    · exact (betaEtaStep_var ha).elim
  | body hW => exact .body (hW.step hs)

theorem WqF.reduces {x : ℕ} {P Q : Lambda} (h : WqF x P) (hr : betaEtaReduces P Q) : WqF x Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem betaEtaStep_lift_reduces {t t' : Lambda} (h : betaEtaStep t t') :
    betaEtaReduces (Lambda.lift 1 0 t) (Lambda.lift 1 0 t') := by
  rcases h with h | h
  · exact betaEtaReduces.of_reduces (Lambda.reduces_lift (Lambda.reduces.step _ _ _ h
      (Lambda.reduces.refl _)) 1 0)
  · exact betaEtaReduces.single (.eta (Lambda.etaStep_lift h 1 0))

theorem WqF.ne_var {x : ℕ} {P : Lambda} {n : ℕ} (h : WqF x P) : P ≠ .var n := by
  cases h with
  | ap _ => simp
  | body hW => cases hW <;> simp

/-- The bodies under `q` of the `s`-reducts. -/
inductive SqR (x : ℕ) : Lambda → Prop
  | mw {W : Lambda} : WqF x W → SqR x (.app lamM W)
  | ww {W Y : Lambda} : WqF x W → SqR x (.app W Y)
  | core {P : Lambda} : TC (YB x) (x + 1) 1 P → SqR x P

theorem SqR.step {x : ℕ} {P P' : Lambda} (h : SqR x P) (hs : betaEtaStep P P') : SqR x P' := by
  cases h with
  | mw hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, ite_eq_left]
      exact .ww hW
    · exact (nf_lamM _ hf).elim
    · exact .mw (hW.step ha)
  | ww hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · subst hc
      cases hW with
      | body hq =>
        cases hq with
        | wL hC => exact .core (hC.subst_liftB (x := x + 1) _)
    · exact .ww (hW.step hf)
    · exact .ww hW
  | core hP => exact .core (hP.step_YB hs)

/-- The reducts of `s = B M W` (`W ∈ WR x`), `x` at index `x`. -/
inductive SR (x : ℕ) : Lambda → Prop
  | sbm {W : Lambda} : WR x W → SR x (.app (.app lamB lamM) W)
  | sbm1 {W : Lambda} : WR x W → SR x (.app bmPre1 W)
  | sbm2 {W : Lambda} : WR x W → SR x (.app bmPre2 W)
  | slam {S : Lambda} : SqR x S → SR x (.lam S)
  | sv {V : Lambda} : YG x 0 V → SR x V
  | seta {f : Lambda} : WqF x (Lambda.lift 1 0 f) → SR x f

theorem SR.step {x : ℕ} {P P' : Lambda} (h : SR x P) (hs : betaEtaStep P P') : SR x P' := by
  cases h with
  | sbm hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_M]; exact .sbm1 hW
      · exact (nf_lamB _ hf').elim
      · exact (nf_lamM _ ha).elim
    · exact .sbm (hW.step ha)
  | @sbm1 W hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre1, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst W 0 (.lam (.app lamM (.app (.var 1) (.var 0)))) =
          .lam (.app lamM (.app (Lambda.lift 1 0 W) (.var 0))) := by
        simp [Lambda.subst, lamM]
      rw [e]; exact .slam (.mw (.ap hW))
    · rw [step_bmPre1 hf]; exact .sbm2 hW
    · exact .sbm1 (hW.step ha)
  | @sbm2 W hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre2, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst W 0
          (.lam (.app (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0)))) =
          .lam (.app (.app (Lambda.lift 1 0 W) (.var 0)) (.app (Lambda.lift 1 0 W) (.var 0))) := by
        simp [Lambda.subst]
      rw [e]; exact .slam (.ww (.ap hW))
    · exact (nf_bmPre2 _ hf).elim
    · exact .sbm2 (hW.step ha)
  | slam hS =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .slam (hS.step hb)
    · cases hS with
      | mw hW =>
        simp only [Lambda.app.injEq] at hf
        exact (hW.ne_var hf.2).elim
      | ww hW =>
        simp only [Lambda.app.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact .seta hW
      | core hP =>
        generalize hone : (1 : ℤ) = one at hP
        cases hP with
        | base hb =>
          obtain ⟨n, rfl, hb⟩ := hb
          cases hb with
          | q hR => simp only [Lambda.app.injEq] at hf; cases hR <;> simp [bym1, bym2, bym3] at hf
          | m hR => simp only [Lambda.app.injEq] at hf; cases hR <;> simp [bym1, bym2, bym3] at hf
          | rr _ hR => simp only [Lambda.app.injEq] at hf; cases hR <;> simp [bym1, bym2, bym3] at hf
          | @comp i' R hR =>
            simp only [Lambda.app.injEq] at hf
            obtain rfl := Lambda.lift_one_injective 0 hf.1
            have : i' = 0 := by omega
            subst this
            exact .sv hR
        | bx hP =>
          simp only [Lambda.app.injEq] at hf
          exact (hP.ne_var_of YB.ne_var 0 hf.2).elim
        | bx1 hP =>
          simp only [Lambda.app.injEq] at hf
          exact (hP.ne_var_of YB.ne_var 0 hf.2).elim
        | rq _ _ => simp at hf
  | sv hV => exact .sv (hV.step hs)
  | seta hW => exact .seta (hW.reduces (betaEtaStep_lift_reduces hs))

theorem SR.reduces {x : ℕ} {P Q : Lambda} (h : SR x P) (hr : betaEtaReduces P Q) : SR x Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **`s = B M w` is in the grammar.** -/
theorem SR.of_h5s (x : ℕ) : SR x (toLam (h5s x)) :=
  .sbm (WR.of_h5w x)

/-- Every βη-reduct of `s` is in the grammar. -/
theorem SR.of_reduces {x : ℕ} {P : Lambda} (hr : betaEtaReduces (toLam (h5s x)) P) : SR x P :=
  (SR.of_h5s x).reduces hr

end TLCA4
