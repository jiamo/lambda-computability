import Start.TLCA4QNotFixpoint

/-!
# TLCA open problem 4: a generic shape argument with arbitrary tails
(row M20-TLCA4-BETAETA; series V, big round, run 9, item A3, plan 4.4 step 3)

The proofs of `T_not_fixedPoint` and `Q_not_fixedPoint` follow one pattern: the reducts of `p x`
keep a *shape* `xᵏ (H ρ)`, with `H` an `x`-chain of integer height `h` over a family of *cores*
and a conserved quantity `K = k + h` that the chain determines; a term and its `x`-prefix cannot
both have the shape.  For `Q` the tail `ρ` was a reduct of a fixed term and the chains passed
their bound variable unchanged to the next chain.  The candidates `hit5`, `hit6`, `hit8` update
their tail at every stage (`Wₙ₊₁ = w (uⁿ s) Wₙ`, `Start/TLCA4Hit5Stages.lean`), so this module
abstracts the pattern with **arbitrary tails**:

* `TC base x` — integer-height chains `B x C`, `(λab. x (a b)) C` and
  `λc. xᵐ (C T)` with an *arbitrary* term `T` (the tail transformer) over a base family;
* `TailCores base x` — the hypotheses on a `K`-indexed core family: closure under one βη-step
  (a firing core becomes a chain), no core is an abstraction, a variable or a chain head, and the
  core determines `K − n`;
* **`TC.step`**, `TC.reduces` — chains are closed under βη;
* `AShape`, **`AShape.step`**, `AShape.reduces` — the shape `xᵏ (H ρ)` (any `ρ`) is closed under
  βη;
* **`TC.unique`**, **`AShape.not_xPrefix`** — `K − h` is determined, so a term and its
  `x`-prefix cannot both have the shape;
* **`not_fixedPoint_of_ashape`** — if `L` βη-reduces to a term of the shape, then
  `¬ L =βη x L`.

What remains for each candidate is a core family with `TailCores` that contains a reduct of
`p x`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- `x`-chains with integer heights and **arbitrary tails** over an indexed base family. -/
inductive TC (base : ℤ → Lambda → Prop) (x : ℕ) : ℤ → Lambda → Prop
  | base {i : ℤ} {P : Lambda} : base i P → TC base x i P
  | bx {i : ℤ} {P : Lambda} : TC base x i P → TC base x (i + 1) (.app (.app lamB (.var x)) P)
  | bx1 {i : ℤ} {P : Lambda} : TC base x i P → TC base x (i + 1) (.app (bxPre x) P)
  | rq {i i' : ℤ} {m : ℕ} {R T : Lambda} : TC base x i' R → (m : ℤ) + i' = i →
      TC base x i (.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) T)))

/-- The hypotheses on a `K`-indexed family of cores. -/
structure TailCores (base : ℤ → ℤ → Lambda → Prop) (x : ℕ) : Prop where
  step : ∀ {K i : ℤ} {P P' : Lambda}, base K i P → betaEtaStep P P' → TC (base K) x i P'
  not_lam : ∀ {K i : ℤ} {c : Lambda}, base K i (.lam c) → False
  ne_var : ∀ {K i : ℤ} {P : Lambda} {n : ℕ}, base K i P → P ≠ .var n
  ne_bx : ∀ {K i : ℤ} {P Q : Lambda}, base K i P → P ≠ .app (.app lamB (.var x)) Q
  ne_bx1 : ∀ {K i : ℤ} {P Q : Lambda}, base K i P → P ≠ .app (bxPre x) Q
  unique : ∀ {K i K' i' : ℤ} {P : Lambda}, base K i P → base K' i' P → K - i = K' - i'

theorem subst_lift_lift_one (T X : Lambda) :
    Lambda.subst T 0 (Lambda.lift 1 1 (Lambda.lift 1 0 X)) = Lambda.lift 1 0 X := by
  rw [lift_lift_zero_one X |>.symm, Lambda.subst_lift]

/-- A chain that is an abstraction, applied to a tail, gives a chain under the same binder. -/
theorem TC.beta_lift {base : ℤ → Lambda → Prop} {x : ℕ}
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i' : ℤ} {R c0 T : Lambda}
    (hR : TC base x i' R) (e : R = .lam c0) (m : ℕ) :
    TC base x ((m : ℤ) + i')
      (.lam (xPow (.var (x + 1)) m (Lambda.subst T 0 (Lambda.lift 1 1 c0)))) := by
  cases hR with
  | base hb => subst e; exact (hl hb).elim
  | bx _ => cases e
  | bx1 _ => cases e
  | @rq _ i'' m' R' T' hR' hm =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [lift_xPow, subst_xPow]
    simp only [Lambda.lift, Lambda.subst, subst_lift_lift_one]
    have hx : Lambda.subst T 0 (.var (x + 1 + 1)) = .var (x + 1) := by
      simp [Lambda.subst]
    rw [if_neg (by omega), hx, xPow_add]
    exact .rq hR' (by push_cast; omega)

/-- **Chains with arbitrary tails are closed under one βη-step**, given closure of the base. -/
theorem TC.step {base : ℤ → Lambda → Prop} {x : ℕ}
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ}
    {P P' : Lambda} (h : TC base x i P) (hs : betaEtaStep P P') : TC base x i P' := by
  induction h generalizing P' with
  | base hP => exact hs0 hP hs
  | bx h ih =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bx1 h
      · exact (nf_lamB _ hf').elim
      · exact (betaEtaStep_var ha).elim
    · exact .bx (ih ha)
  | bx1 h ih =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bxPre, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ P : Lambda, Lambda.subst P 0 (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0)))) =
          .lam (xPow (.var (x + 1)) 1 (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst, xPow]
      rw [e]; exact TC.rq (m := 1) h (by push_cast; omega)
    · exact (nf_bxPre x _ hf).elim
    · exact .bx1 (ih ha)
  | @rq i₀ i' m R T h hm ih =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        have := TC.beta_lift (T := T) hl h rfl m
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (ih hR') hm
      · exact .rq h hm
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by push_cast at hm; omega
      subst e
      exact h

theorem TC.reduces {base : ℤ → Lambda → Prop} {x : ℕ}
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ}
    {P Q : Lambda} (h : TC base x i P) (hr : betaEtaReduces P Q) : TC base x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs0 hl hs

/-- **The shape with arbitrary tails**: `xᵏ (H ρ)` with `H` a chain of height `h` over the cores
with conserved quantity `k + h`; the tail `ρ` is arbitrary. -/
def AShape (base : ℤ → ℤ → Lambda → Prop) (x : ℕ) (N : Lambda) : Prop :=
  ∃ (k : ℕ) (h : ℤ) (H ρ : Lambda), N = xPow (.var x) k (.app H ρ) ∧
    TC (base ((k : ℤ) + h)) x h H

/-- **The shape is closed under one βη-step.** -/
theorem AShape.step {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailCores base x)
    {N N' : Lambda} (h : AShape base x N) (hs : betaEtaStep N N') : AShape base x N' := by
  obtain ⟨k, hh, H, ρ, rfl, hH⟩ := h
  obtain ⟨T', hT, rfl⟩ := betaEtaStep_xPow hs
  rcases betaEtaStep_app_cases hT with ⟨c, rfl, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
  · generalize e : Lambda.lam c = t at hH
    cases hH with
    | base hb => subst e; exact (hc.not_lam hb).elim
    | bx _ => cases e
    | bx1 _ => cases e
    | @rq _ i' m R T hR hm =>
      simp only [Lambda.lam.injEq] at e
      subst e
      rw [subst_xPow_var]
      simp only [Lambda.subst, Lambda.subst_lift]
      rw [xPow_add]
      refine ⟨k + m, i', R, _, rfl, ?_⟩
      have : ((k + m : ℕ) : ℤ) + i' = (k : ℤ) + hh := by push_cast; omega
      rw [this]; exact hR
  · exact ⟨k, hh, f', ρ, rfl, hH.step hc.step hc.not_lam hf⟩
  · exact ⟨k, hh, H, a', rfl, hH⟩

theorem AShape.reduces {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailCores base x)
    {N N' : Lambda} (h : AShape base x N) (hr : betaEtaReduces N N') : AShape base x N' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hc hs

theorem TC.ne_var {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailCores base x) {K h : ℤ}
    {H : Lambda} (hH : TC (base K) x h H) (n : ℕ) : H ≠ .var n := by
  cases hH with
  | base hb => exact hc.ne_var hb
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

/-- **The conserved quantity `K − h` is determined by the chain.** -/
theorem TC.unique {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailCores base x) {K h : ℤ}
    {H : Lambda} (hH : TC (base K) x h H) :
    ∀ {K' h' : ℤ}, TC (base K') x h' H → K - h = K' - h' := by
  induction hH with
  | base hb =>
    intro K' h' hH'
    cases hH' with
    | base hb' => exact hc.unique hb hb'
    | bx _ => exact (hc.ne_bx hb rfl).elim
    | bx1 _ => exact (hc.ne_bx1 hb rfl).elim
    | rq _ _ => exact (hc.not_lam hb).elim
  | bx hP ih =>
    intro K' h' hH'
    generalize e : Lambda.app (.app lamB (.var x)) _ = t at hH'
    cases hH' with
    | base hb' => subst e; exact (hc.ne_bx hb' rfl).elim
    | bx hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := ih hP'
      omega
    | bx1 _ => simp [lamB, bxPre] at e
    | rq _ _ => simp at e
  | bx1 hP ih =>
    intro K' h' hH'
    generalize e : Lambda.app (bxPre x) _ = t at hH'
    cases hH' with
    | base hb' => subst e; exact (hc.ne_bx1 hb' rfl).elim
    | bx _ => simp [lamB, bxPre] at e
    | bx1 hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := ih hP'
      omega
    | rq _ _ => simp at e
  | @rq i₀ i' m R T hR hm ih =>
    intro K' h' hH'
    generalize e : Lambda.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) T)) = t at hH'
    cases hH' with
    | base hb' => subst e; exact (hc.not_lam hb').elim
    | bx _ => simp at e
    | bx1 _ => simp at e
    | @rq _ i'' m' R' T' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      have hA : Lambda.lift 1 0 R ≠ .var (x + 1) := by
        intro e'; cases R <;> simp [Lambda.lift] at e'; exact hR.ne_var hc x (by rw [e'])
      have hA' : Lambda.lift 1 0 R' ≠ .var (x + 1) := by
        intro e'; cases R' <;> simp [Lambda.lift] at e'; exact hR'.ne_var hc x (by rw [e'])
      obtain ⟨rfl, e1, -⟩ := xPow_app_unique hA hA' e
      obtain rfl := Lambda.lift_one_injective 0 e1
      have := ih hR'
      omega

/-- **A term and its `x`-prefix cannot both have the shape.** -/
theorem AShape.not_xPrefix {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailCores base x)
    {N : Lambda} (h : AShape base x N) (h' : AShape base x (.app (.var x) N)) : False := by
  obtain ⟨k, hh, H, ρ, rfl, hH⟩ := h
  obtain ⟨k', hh', H', ρ', e, hH'⟩ := h'
  have e' : xPow (.var x) (k + 1) (.app H ρ) = xPow (.var x) k' (.app H' ρ') := e
  obtain ⟨rfl, rfl, rfl⟩ := xPow_app_unique (hH.ne_var hc x) (hH'.ne_var hc x) e'
  have := hH.unique hc hH'
  push_cast at this
  omega

/-- **The generic non-fixed-point theorem**: if `L` βη-reduces to a term of the shape, then `L` is
not βη-convertible to `x L`. -/
theorem not_fixedPoint_of_ashape {base : ℤ → ℤ → Lambda → Prop} {x : ℕ}
    (hc : TailCores base x) {L N₀ : Lambda} (hL : betaEtaReduces L N₀) (hS : AShape base x N₀) :
    ¬ Lambda.betaEtaConv L (.app (.var x) L) := by
  intro hconv
  obtain ⟨w, hw₁, hw₂⟩ := hconv.common_reduct
  obtain ⟨w', rfl, hw'⟩ := betaEtaReduces_app_var' hw₂
  obtain ⟨D, hD₁, hD₂⟩ := Lambda.betaEta_church_rosser hL hw'
  obtain ⟨E, hE₁, hE₂⟩ := Lambda.betaEta_church_rosser hL
    (hw₁.trans (betaEtaReduces_app_right (.var x) hD₂))
  obtain ⟨D', rfl, hD'⟩ := betaEtaReduces_app_var' hE₂
  exact (hS.reduces hc (hD₁.trans hD')).not_xPrefix hc (hS.reduces hc hE₁)

/-! ### Instance: the cores of `Q` -/

theorem ZC.toTC {base : ℤ → Lambda → Prop} {x : ℕ} {i : ℤ} {P : Lambda} (h : ZC base x i P) :
    TC base x i P := by
  induction h with
  | base hb => exact .base hb
  | bx _ ih => exact .bx ih
  | bx1 _ ih => exact .bx1 ih
  | rq _ hm ih => exact .rq ih hm

/-- The cores of `Q` (`QBase`) satisfy the hypotheses of the generic argument. -/
theorem QBase.tailCores (x : ℕ) : TailCores (QBase x) x where
  step hb hs := ((QBase.zcBase x _).step hb hs).toTC
  not_lam := by
    rintro K i c ⟨i', j', hc, -⟩
    exact hc.ne_lam rfl
  ne_var := by
    rintro K i P n ⟨i', j', hc, -⟩
    cases hc <;> simp
  ne_bx := by
    rintro K i P Q ⟨i', j', hc, -⟩
    exact hc.ne_bx
  ne_bx1 := by
    rintro K i P Q ⟨i', j', hc, -⟩
    exact hc.ne_bx1
  unique := by
    rintro K i K' i' P ⟨a, b, hc, hK⟩ ⟨a', b', hc', hK'⟩
    obtain ⟨rfl, rfl⟩ := hc.unique hc'
    omega

/-- `Q_not_fixedPoint` again, from the generic argument (a check that its hypotheses are met). -/
theorem Q_not_fixedPoint_of_ashape :
    ¬ Lambda.betaEtaConv (toLam (app tQ (var 0))) (toLam (app (var 0) (app tQ (var 0)))) :=
  not_fixedPoint_of_ashape (QBase.tailCores 0) (.of_reduces (Q_stage_betaEta 0 0))
    ⟨0, 0, _, _, rfl, .base ⟨1, 1, .mq (YG.of_tAy 0 1), by simp [tri]⟩⟩

end TLCA4
