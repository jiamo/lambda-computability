import Start.TLCA4TailShape
import Start.TLCA4Hit5Stages

/-!
# TLCA open problem 4: the `w`-layer of `hit5`
(row M20-TLCA4-BETAETA; series V, big round, run 10, item A3, plan 4.4 step 2)

`hit5 x` unfolds through the terms `u = B (B x)`, `v = B M u`, `w = B B v`, `s = B M w`
(`Start/TLCA4Hit5Stages.lean`).  The reducts of `v` (and of the components `uⁿ v`) are described
by the grammar `YG` of `Start/TLCA4YGrammar.lean`.  This module gives a βη-closed grammar for
the next layer, the reducts of `w = B B V` with `V` a reduct of `v`:

* `YB x` — the cores `YBase x` with integer heights; `LiftB base` — a base family lifted under
  one more binder; **`TC.lift`** — chains with arbitrary tails are stable under lifting, and
  `TC.step_liftB` — the lifted chains are closed under βη when the base is;
* `WqR x` — the bodies under the binder `q`: `B Vq` with `Vq` a chain of height `1` over
  `YB x`, and `λb. C` with `C` a lifted chain of height `1` (the arbitrary tail absorbs
  `b c` and its descendants);
* `WR x` — `B B V`, `(λbc. B (b c)) V`, `(λbcyz. b c (y z)) V` with `V` in `YG x 0`, and
  `λq. W` with `W ∈ WqR x`;
* **`WqR.step`**, **`WR.step`**, `WR.reduces` — the grammar is closed under βη;
* **`WR.of_h5w`**, `WR.of_reduces` — `w` itself, hence every βη-reduct of `w`, is in it.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- The cores `YBase x` with integer heights. -/
def YB (x : ℕ) : ℤ → Lambda → Prop := fun i P => ∃ n : ℕ, (n : ℤ) = i ∧ YBase x n P

/-- A base family lifted under one more binder. -/
def LiftB (base : ℤ → Lambda → Prop) : ℤ → Lambda → Prop :=
  fun i P => ∃ P0, base i P0 ∧ P = Lambda.lift 1 0 P0

theorem lift_lamB (k : ℕ) : Lambda.lift 1 k lamB = lamB := by
  simp [lamB, Lambda.lift]

theorem lift_bxPre (y : ℕ) : Lambda.lift 1 0 (bxPre y) = bxPre (y + 1) := by
  simp [bxPre, Lambda.lift]

/-- **Chains with arbitrary tails are stable under lifting.** -/
theorem TC.lift {base : ℤ → Lambda → Prop} {x : ℕ} {i : ℤ} {P : Lambda}
    (h : TC base x i P) : TC (LiftB base) (x + 1) i (Lambda.lift 1 0 P) := by
  induction h with
  | base hb => exact .base ⟨_, hb, rfl⟩
  | @bx i P _ ih =>
    have e : Lambda.lift 1 0 (.app (.app lamB (.var x)) P) =
        .app (.app lamB (.var (x + 1))) (Lambda.lift 1 0 P) := by
      simp only [Lambda.lift, lift_lamB]; simp
    rw [e]; exact .bx ih
  | @bx1 i P _ ih =>
    have e : Lambda.lift 1 0 (.app (bxPre x) P) = .app (bxPre (x + 1)) (Lambda.lift 1 0 P) := by
      simp only [Lambda.lift, lift_bxPre]
    rw [e]; exact .bx1 ih
  | @rq i i' m R T _ hm ih =>
    have e : Lambda.lift 1 0 (.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) T))) =
        .lam (xPow (.var (x + 1 + 1)) m
          (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) (Lambda.lift 1 1 T))) := by
      simp only [Lambda.lift, lift_xPow, lift_lift_zero_one]
      simp
    rw [e]; exact .rq ih hm

theorem TC.ne_var_of {base : ℤ → Lambda → Prop} {x : ℕ}
    (hv : ∀ {i : ℤ} {P : Lambda} {n : ℕ}, base i P → P ≠ .var n) {i : ℤ} {P : Lambda}
    (h : TC base x i P) (n : ℕ) : P ≠ .var n := by
  cases h with
  | base hb => exact hv hb
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

theorem LiftB.ne_var {base : ℤ → Lambda → Prop}
    (hv : ∀ {i : ℤ} {P : Lambda} {n : ℕ}, base i P → P ≠ .var n) {i : ℤ} {P : Lambda} {n : ℕ}
    (h : LiftB base i P) : P ≠ .var n := by
  obtain ⟨P0, hb, rfl⟩ := h
  intro e
  cases P0 with
  | var k => exact hv hb rfl
  | app _ _ => simp [Lambda.lift] at e
  | lam _ => simp [Lambda.lift] at e

theorem TC.ne_app_var0 {base : ℤ → Lambda → Prop} {x : ℕ}
    (hv : ∀ {i : ℤ} {P : Lambda} {n : ℕ}, base i P → P ≠ .var n)
    (hb : ∀ {i : ℤ} {P : Lambda} (F : Lambda), base i P → P ≠ .app F (.var 0)) {i : ℤ}
    {P : Lambda} (h : TC base x i P) (F : Lambda) : P ≠ .app F (.var 0) := by
  cases h with
  | base hb' => exact hb F hb'
  | bx h' =>
    intro e; simp only [Lambda.app.injEq] at e; exact h'.ne_var_of hv 0 e.2
  | bx1 h' =>
    intro e; simp only [Lambda.app.injEq] at e; exact h'.ne_var_of hv 0 e.2
  | rq _ _ => simp

theorem LiftB.ne_app_var0 {base : ℤ → Lambda → Prop} {i : ℤ} {P : Lambda} (F : Lambda)
    (h : LiftB base i P) : P ≠ .app F (.var 0) := by
  obtain ⟨P0, -, rfl⟩ := h
  intro e
  cases P0 with
  | var _ => simp [Lambda.lift] at e
  | lam _ => simp [Lambda.lift] at e
  | app a b =>
    simp only [Lambda.lift, Lambda.app.injEq] at e
    cases b <;> simp [Lambda.lift] at e

/-- Lifted chains are closed under βη when the base is. -/
theorem TC.step_liftB {base : ℤ → Lambda → Prop} {x : ℕ}
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ} {P P' : Lambda}
    (h : TC (LiftB base) (x + 1) i P) (hs : betaEtaStep P P') :
    TC (LiftB base) (x + 1) i P' := by
  refine h.step ?_ ?_ hs
  · rintro i P P' ⟨P0, hb, rfl⟩ hs'
    obtain ⟨P0', rfl, hs''⟩ := betaEtaStep_lift_inv hs'
    exact (hs0 hb hs'').lift
  · rintro i c ⟨P0, hb, e⟩
    obtain ⟨c0, rfl, -⟩ := Lambda.lift_eq_lam e.symm
    exact hl hb

theorem YC.toTC {x n : ℕ} {P : Lambda} (h : YC x n P) : TC (YB x) (x + 1) n P :=
  match h with
  | .base hb => .base ⟨_, rfl, hb⟩
  | .bx h' => by push_cast; exact .bx (YC.toTC h')
  | .bx1 h' => by push_cast; exact .bx1 (YC.toTC h')
  | .rq h' hm => .rq (YC.toTC h') (by rw [← hm]; push_cast; rfl)

theorem YB.step {x : ℕ} {i : ℤ} {P P' : Lambda} (h : YB x i P) (hs : betaEtaStep P P') :
    TC (YB x) (x + 1) i P' := by
  obtain ⟨n, rfl, hb⟩ := h
  exact (YBase.step hb hs).toTC

theorem YB.not_lam {x : ℕ} {i : ℤ} {c : Lambda} (h : YB x i (.lam c)) : False := by
  obtain ⟨n, -, hb⟩ := h
  cases hb

theorem YB.ne_var {x : ℕ} {i : ℤ} {P : Lambda} {n : ℕ} (h : YB x i P) : P ≠ .var n := by
  obtain ⟨k, -, hb⟩ := h
  cases hb <;> simp

/-- `λbcyz. b c (y z)`, the normal form of `B B`. -/
def bbPre2 : Lambda :=
  .lam (.lam (.lam (.lam (.app (.app (.var 3) (.var 2)) (.app (.var 1) (.var 0))))))

/-- `λbc. B (b c)`, the first reduct of `B B`. -/
def bbPre : Lambda := .lam (.lam (.app lamB (.app (.var 1) (.var 0))))

theorem nf_bbPre2 : BetaEtaNf bbPre2 := by
  unfold bbPre2
  refine betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_lam ?_ ?_) ?_) ?_) ?_
  · intro u hu
    rcases betaEtaStep_app_cases hu with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
    · cases hc
    · exact nf_app_var_var _ hf
    · exact nf_app_var_var _ ha
  all_goals intro f h; simp at h

theorem step_bbPre {u : Lambda} (h : betaEtaStep bbPre u) : u = bbPre2 := by
  unfold bbPre at h
  rcases betaEtaStep_lam_cases h with ⟨b', hb, rfl⟩ | ⟨f, hf, _⟩
  · rcases betaEtaStep_lam_cases hb with ⟨b'', hb', rfl⟩ | ⟨f, hf, _⟩
    · rcases betaEtaStep_app_cases hb' with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        simp [Lambda.subst, Lambda.lift, bbPre2]
      · exact (nf_lamB _ hf).elim
      · exact (nf_app_var_var _ ha).elim
    · simp only [Lambda.app.injEq] at hf
      obtain ⟨-, h2⟩ := hf
      cases f <;> simp at h2
  · simp at hf

/-- The bodies of the `w`-reducts under the binder `q` (`x` at index `x + 1`). -/
inductive WqR (x : ℕ) : Lambda → Prop
  | wB {Vq : Lambda} : TC (YB x) (x + 1) 1 Vq → WqR x (.app lamB Vq)
  | wL {C : Lambda} : TC (LiftB (YB x)) (x + 2) 1 C → WqR x (.lam C)

/-- The reducts of `w = B B V` (`V` a reduct of `v`), `x` at index `x`. -/
inductive WR (x : ℕ) : Lambda → Prop
  | wbb {V : Lambda} : YG x 0 V → WR x (.app (.app lamB lamB) V)
  | wpre {V : Lambda} : YG x 0 V → WR x (.app bbPre V)
  | wpre2 {V : Lambda} : YG x 0 V → WR x (.app bbPre2 V)
  | wlam {W : Lambda} : WqR x W → WR x (.lam W)

theorem TC.step_YB {x : ℕ} {i : ℤ} {P P' : Lambda} (h : TC (YB x) (x + 1) i P)
    (hs : betaEtaStep P P') : TC (YB x) (x + 1) i P' :=
  h.step YB.step YB.not_lam hs

theorem TC.step_LYB {x : ℕ} {i : ℤ} {P P' : Lambda} (h : TC (LiftB (YB x)) (x + 2) i P)
    (hs : betaEtaStep P P') : TC (LiftB (YB x)) (x + 2) i P' :=
  TC.step_liftB (x := x + 1) YB.step YB.not_lam h hs

/-- The chain body of `λb.λc. (lift lift Vq) (b c)` (the β-reduct of `B Vq`). -/
theorem wL_of_wB {x : ℕ} {Vq : Lambda} (h : TC (YB x) (x + 1) 1 Vq) :
    TC (LiftB (YB x)) (x + 2) 1
      (.lam (.app (Lambda.lift 1 0 (Lambda.lift 1 0 Vq)) (.app (.var 1) (.var 0)))) := by
  have := TC.rq (x := x + 2) (i := 1) (m := 0) (T := .app (.var 1) (.var 0)) h.lift (by simp)
  simpa [xPow] using this

/-- **The bodies are closed under one βη-step.** -/
theorem WqR.step {x : ℕ} {P P' : Lambda} (h : WqR x P) (hs : betaEtaStep P P') : WqR x P' := by
  cases h with
  | @wB Vq hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamB, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst Vq 0 (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) =
          .lam (.lam (.app (Lambda.lift 1 0 (Lambda.lift 1 0 Vq)) (.app (.var 1) (.var 0)))) := by
        simp [Lambda.subst, lift_lift_zero_one]
      rw [e]; exact .wL (wL_of_wB hV)
    · exact (nf_lamB _ hf).elim
    · exact .wB (hV.step_YB ha)
  | wL hC =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .wL (hC.step_LYB hb)
    · exact (hC.ne_app_var0 (LiftB.ne_var YB.ne_var) LiftB.ne_app_var0 _ hf).elim

/-- **The reducts of `w` are closed under one βη-step.** -/
theorem WR.step {x : ℕ} {P P' : Lambda} (h : WR x P) (hs : betaEtaStep P P') : WR x P' := by
  cases h with
  | wbb hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        have e : Lambda.subst lamB 0 (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) =
            bbPre := by
          simp [Lambda.subst, Lambda.lift, bbPre, lamB]
        rw [e]; exact .wpre hV
      · exact (nf_lamB _ hf').elim
      · exact (nf_lamB _ ha).elim
    · exact .wbb (hV.step ha)
  | @wpre V hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bbPre, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst V 0 (.lam (.app lamB (.app (.var 1) (.var 0)))) =
          .lam (.app lamB (.app (Lambda.lift 1 0 V) (.var 0))) := by
        simp [Lambda.subst, lamB]
      rw [e]; exact .wlam (.wB (.base ⟨1, rfl, .comp hV⟩))
    · rw [step_bbPre hf]; exact .wpre2 hV
    · exact .wpre (hV.step ha)
  | wpre2 hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bbPre2, Lambda.lam.injEq] at hc
      subst hc
      refine .wlam (.wL ?_)
      have := wL_of_wB (x := x) (Vq := .app (Lambda.lift 1 0 _) (.var 0)) (.base ⟨1, rfl, .comp hV⟩)
      convert this using 2
      simp [Lambda.subst, Lambda.lift, lift_lift_zero_one]
    · exact (nf_bbPre2 _ hf).elim
    · exact .wpre2 (hV.step ha)
  | wlam hW =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .wlam (hW.step hb)
    · exfalso
      cases hW with
      | wB hV =>
        simp only [Lambda.app.injEq] at hf
        exact hV.ne_var_of YB.ne_var 0 hf.2
      | wL _ => simp at hf

theorem WR.reduces {x : ℕ} {P Q : Lambda} (h : WR x P) (hr : betaEtaReduces P Q) : WR x Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **`w = B B v` is in the grammar.** -/
theorem WR.of_h5w (x : ℕ) : WR x (toLam (h5w x)) :=
  .wbb (.bm .bb)

/-- Every βη-reduct of `w` is in the grammar. -/
theorem WR.of_reduces {x : ℕ} {P : Lambda} (hr : betaEtaReduces (toLam (h5w x)) P) : WR x P :=
  (WR.of_h5w x).reduces hr

end TLCA4
