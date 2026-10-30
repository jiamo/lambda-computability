import Start.TLCA4TGrammar

/-!
# Series V, round 4, run 1, parts A3–A4: `T` is not a βη fixed-point combinator
(row M20-TLCA4-T-NOT-FIXPOINT)

With `tri j = j (j + 1) / 2` (`TLCA4.tri`), the *shape* `TShape x N` of a term is

* `N = xᵏ (P Q)` with `P`, `Q` in the component grammar at indices `i`, `j` and `k + i = tri j`, or
* `N = xᵏ (M Q)` with `Q` in the component grammar at index `j` and `k + j = tri j`.

* **`TShape.step`**, `TShape.reduces` — the shape is closed under βη-reduction;
* **`TGram.reduces_tAnf`**, `TGram.index_unique` — the index of a grammar member is unique;
* **`T_not_fixedPoint`** — `¬ T x =βη x (T x)`.

The argument: `T x →β M A₀ =: N₀`, which has shape `(k, j) = (0, 0)`.  If `T x =βη x (T x)` then
`N₀ =βη x N₀`, so by Church–Rosser `N₀ →βη C'` and `N₀ →βη x C'` for some `C'`.  Both have shape;
the `x`-prefix decomposition is unique (no component is a variable), and the indices are unique, so
`k + 1 + i = k + i` (or `k + 1 + j = k + j`), a contradiction.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep etaStep betaEta_church_rosser)

/-- Triangular numbers, `tri j = j (j + 1) / 2`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | j + 1 => tri j + j + 1

theorem two_mul_tri (j : ℕ) : 2 * tri j = j * (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [tri]; linear_combination ih

/-! ### Substitution into the four bodies -/

theorem subst_xPow_var (Q : Lambda) (x m : ℕ) (H : Lambda) :
    Lambda.subst Q 0 (xPow (.var (x + 1)) m H) = xPow (.var x) m (Lambda.subst Q 0 H) := by
  rw [subst_xPow]; simp [Lambda.subst]

theorem BxqR.subst {x j : ℕ} {R Q : Lambda} (hR : BxqR (x + 1) R) (hQ : TGram x j Q) :
    TGram x (j + 1) (Lambda.subst Q 0 R) := by
  cases hR with
  | b =>
    have : Lambda.subst Q 0 (.app (.app lamB (.var (x + 1))) (.var 0)) =
        .app (.app lamB (.var x)) Q := by simp [Lambda.subst, lamB]
    rw [this]; exact .bx hQ
  | pre =>
    have : Lambda.subst Q 0 (.app (bxPre (x + 1)) (.var 0)) = .app (bxPre x) Q := by
      simp [Lambda.subst, bxPre]
    rw [this]; exact .bx1 hQ
  | lam =>
    have : Lambda.subst Q 0 (lamXq (x + 1)) =
        .lam (xPow (.var (x + 1)) 1 (.app (Lambda.lift 1 0 Q) (.var 0))) := by
      simp [Lambda.subst, lamXq, xPow]
    rw [this]; exact TGram.rq (m := 1) hQ (by omega)

/-! ### The shape and its closure -/

/-- **The shape of the reducts of `M A₀`.** -/
inductive TShape (x : ℕ) : Lambda → Prop
  | mstage {k j : ℕ} {Q : Lambda} : TGram x j Q → k + j = tri j →
      TShape x (xPow (.var x) k (.app lamM Q))
  | pair {k i j : ℕ} {P Q : Lambda} : TGram x i P → TGram x j Q → k + i = tri j →
      TShape x (xPow (.var x) k (.app P Q))

/-- **The shape is closed under one βη-step.** -/
theorem TShape.step {x : ℕ} {N N' : Lambda} (h : TShape x N) (hs : betaEtaStep N N') :
    TShape x N' := by
  cases h with
  | @mstage k j Q hQ hk =>
    obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hs
    rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, ite_eq_left]
      exact .pair hQ hQ hk
    · exact (nf_lamM _ hf).elim
    · exact .mstage (hQ.step ha) hk
  | @pair k i j P Q hP hQ hk =>
    obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hs
    rcases betaEtaStep_app_cases hH with ⟨c, rfl, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hP.lam_inv with
      | @rq i' m R hR hm =>
        rw [subst_xPow_var]
        simp only [Lambda.subst, Lambda.subst_lift, ite_eq_left]
        rw [xPow_add]
        exact .pair hR hQ (by omega)
      | @qr m R hR hm =>
        rw [subst_xPow_var]
        simp only [Lambda.subst, ite_eq_left]
        rw [xPow_add]
        exact .pair hQ (hR.subst hQ) (by simp only [tri]; omega)
      | @mr m R hR hm =>
        rw [subst_xPow_var]
        have e : Lambda.subst Q 0 lamM = lamM := by simp [Lambda.subst, lamM]
        simp only [Lambda.subst, e]
        rw [xPow_add]
        exact .mstage (hR.subst hQ) (by simp only [tri]; omega)
      | @rr m R₁ R₂ h₁ h₂ hm =>
        rw [subst_xPow_var]
        simp only [Lambda.subst]
        rw [xPow_add]
        exact .pair (h₁.subst hQ) (h₂.subst hQ) (by simp only [tri]; omega)
    · exact .pair (hP.step hf) hQ hk
    · exact .pair hP (hQ.step ha) hk

theorem TShape.reduces {x : ℕ} {N N' : Lambda} (h : TShape x N) (hr : betaEtaReduces N N') :
    TShape x N' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-! ### βη-reduction congruences -/

theorem betaEtaReduces_lam {b b' : Lambda} (h : betaEtaReduces b b') :
    betaEtaReduces (.lam b) (.lam b') := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine ih.tail ?_
    cases hs with
    | beta hb => exact .beta (.lam _ _ hb)
    | eta he => exact .eta (.lam he)

theorem betaEtaReduces_app_left {f f' : Lambda} (a : Lambda) (h : betaEtaReduces f f') :
    betaEtaReduces (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine ih.tail ?_
    cases hs with
    | beta hb => exact .beta (.app_left _ _ _ hb)
    | eta he => exact .eta (.app_left _ he)

theorem betaEtaReduces_lift {R R' : Lambda} (h : betaEtaReduces R R') :
    betaEtaReduces (Lambda.lift 1 0 R) (Lambda.lift 1 0 R') := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine ih.trans ?_
    cases hs with
    | beta hb =>
      exact .of_reduces (Lambda.reduces_lift (Lambda.reduces.step _ _ _ hb (.refl _)) 1 0)
    | eta he => exact .single (.eta (Lambda.etaStep_lift he 1 0))

theorem betaEtaReduces_xPow (y : ℕ) {H H' : Lambda} (h : betaEtaReduces H H') :
    ∀ m : ℕ, betaEtaReduces (xPow (.var y) m H) (xPow (.var y) m H')
  | 0 => h
  | m + 1 => betaEtaReduces_app_right _ (betaEtaReduces_xPow y h m)

theorem betaEtaReduces_beta (c a : Lambda) :
    betaEtaReduces (.app (.lam c) a) (Lambda.subst a 0 c) :=
  .single (.beta (.beta _ _))

/-- A reduct of a term that reduces to a normal form reduces to it as well. -/
theorem reduces_nf_of_reduct {P P' a : Lambda} (h : betaEtaReduces P a) (ha : BetaEtaNf a)
    (h' : betaEtaReduces P P') : betaEtaReduces P' a := by
  obtain ⟨w, h1, h2⟩ := betaEta_church_rosser h h'
  rw [← h1.eq_of_nf ha] at h2
  exact h2

/-! ### Every grammar member reduces to `aᵢ` -/

theorem lamXq_app (y : ℕ) (R : Lambda) :
    betaEtaReduces (.app (lamXq y) R) (.app (.var y) (.app (.var 0) R)) := by
  have := betaEtaReduces_beta (.app (.var (y + 1)) (.app (.var 1) (.var 0))) R
  simpa [Lambda.subst, lamXq] using this

theorem BxqR.reduces_lamXq {y : ℕ} {R : Lambda} (h : BxqR y R) : betaEtaReduces R (lamXq y) := by
  have hpre : betaEtaReduces (.app (bxPre y) (.var 0)) (lamXq y) := by
    have := betaEtaReduces_beta (.lam (.app (.var (y + 2)) (.app (.var 1) (.var 0)))) (.var 0)
    simpa [Lambda.subst, bxPre, lamXq] using this
  cases h with
  | b =>
    refine (betaEtaReduces_app_left _ ?_).trans hpre
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (.var y)
    rw [step_lamB_var] at this
    exact this
  | pre => exact hpre
  | lam => exact .refl _

theorem tAnf_eq_xPow (x i : ℕ) :
    tAnf x i = .lam (xPow (.var (x + 1)) (i + 1) (.app (.var 0) (lamXq (x + 1)))) := rfl

/-- **Every grammar member of index `i` βη-reduces to `aᵢ`.** -/
theorem TGram.reduces_tAnf {x i : ℕ} {P : Lambda} (h : TGram x i P) :
    betaEtaReduces P (tAnf x i) := by
  have hbm : ∀ {R : Lambda}, BxR x R →
      betaEtaReduces (.app (.app lamB lamM) R) (tAnf x 0) := by
    intro R hR
    have h0 : betaEtaReduces (.app (.app lamB lamM) (.app lamB (.var x))) (tAnf x 0) :=
      .of_reduces (tA0_reduces x)
    cases hR with
    | b => exact h0
    | pre =>
      refine reduces_nf_of_reduct h0 (tAnf_nf x 0) (betaEtaReduces_app_right _ ?_)
      have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (.var x)
      rwa [step_lamB_var] at this
  have hbm1 : ∀ {R : Lambda}, BxR x R → betaEtaReduces (.app bmPre1 R) (tAnf x 0) := by
    intro R hR
    refine reduces_nf_of_reduct (hbm hR) (tAnf_nf x 0) (betaEtaReduces_app_left _ ?_)
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) lamM
    rwa [step_lamB_M] at this
  induction h with
  | bm hR => exact hbm hR
  | bm1 hR => exact hbm1 hR
  | bm2 hR =>
    refine reduces_nf_of_reduct (hbm1 hR) (tAnf_nf x 0) (betaEtaReduces_app_left _ ?_)
    refine betaEtaReduces_lam (betaEtaReduces_lam ?_)
    have := betaEtaReduces_beta (.app (.var 0) (.var 0)) (.app (.var 1) (.var 0))
    simpa [Lambda.subst, lamM] using this
  | bx _ ih =>
    exact (betaEtaReduces_app_right _ ih).trans (.of_reduces (Bx_tAnf_reduces x _))
  | @bx1 i P _ ih =>
    refine reduces_nf_of_reduct ((betaEtaReduces_app_right _ ih).trans
      (.of_reduces (Bx_tAnf_reduces x _))) (tAnf_nf x _) (betaEtaReduces_app_left _ ?_)
    have := betaEtaReduces_beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (.var x)
    rwa [step_lamB_var] at this
  | @rq i i' m R _ hm ih =>
    refine (betaEtaReduces_lam (betaEtaReduces_xPow _ (betaEtaReduces_app_left _
      (betaEtaReduces_lift ih)) m)).trans ?_
    rw [lift_tAnf]
    refine (betaEtaReduces_lam (betaEtaReduces_xPow _
      (.single (.beta (tAnf_app_var0 x i'))) m)).trans ?_
    rw [xPow_add, ← hm]
    exact .refl _
  | @qr i m R hR hm =>
    subst hm
    exact betaEtaReduces_lam (betaEtaReduces_xPow _
      (betaEtaReduces_app_right _ hR.reduces_lamXq) _)
  | @mr i m R hR hm =>
    subst hm
    have h1 : betaEtaReduces (.app lamM R) (.app (.var (x + 1)) (.app (.var 0) (lamXq (x + 1)))) := by
      have h0 : betaEtaReduces (.app lamM R) (.app R R) := by
        have := betaEtaReduces_beta (.app (.var 0) (.var 0)) R
        simpa [Lambda.subst, lamM] using this
      exact h0.trans ((betaEtaReduces_app_left _ hR.reduces_lamXq).trans
        ((betaEtaReduces_app_right _ hR.reduces_lamXq).trans (lamXq_app _ _)))
    have := betaEtaReduces_lam (betaEtaReduces_xPow (x + 1) h1 m)
    rw [xPow_app_self] at this
    exact this
  | @rr i m R₁ R₂ h₁ h₂ hm =>
    subst hm
    have h1 : betaEtaReduces (.app R₁ R₂) (.app (.var (x + 1)) (.app (.var 0) (lamXq (x + 1)))) :=
      (betaEtaReduces_app_left _ h₁.reduces_lamXq).trans
        ((betaEtaReduces_app_right _ h₂.reduces_lamXq).trans (lamXq_app _ _))
    have := betaEtaReduces_lam (betaEtaReduces_xPow (x + 1) h1 m)
    rw [xPow_app_self] at this
    exact this

/-- **The index of a grammar member is unique.** -/
theorem TGram.index_unique {x i j : ℕ} {P : Lambda} (hi : TGram x i P) (hj : TGram x j P) :
    i = j := by
  obtain ⟨w, h1, h2⟩ := betaEta_church_rosser hi.reduces_tAnf hj.reduces_tAnf
  exact tAnf_injective x ((h1.eq_of_nf (tAnf_nf x i)).trans (h2.eq_of_nf (tAnf_nf x j)).symm)

theorem TGram.ne_var {x i : ℕ} {P : Lambda} (h : TGram x i P) (y : ℕ) : P ≠ .var y := by
  cases h <;> simp

theorem TGram.ne_lamM' {x i : ℕ} {P : Lambda} (h : TGram x i P) (hP : P = lamM) : False := by
  cases h with
  | bm _ => simp [lamM] at hP
  | bm1 _ => simp [lamM] at hP
  | bm2 _ => simp [lamM] at hP
  | bx _ => simp [lamM] at hP
  | bx1 _ => simp [lamM] at hP
  | @rq i₀ i' m R hR hm =>
    cases m with
    | zero =>
      simp only [lamM, xPow, Lambda.lam.injEq, Lambda.app.injEq] at hP
      cases R <;> simp [Lambda.lift] at hP
    | succ m => simp [lamM, xPow] at hP
  | @qr i₀ m R hR hm =>
    cases m with
    | zero =>
      simp only [lamM, xPow, Lambda.lam.injEq, Lambda.app.injEq] at hP
      exact hR.ne_var hP.2
    | succ m => simp [lamM, xPow] at hP
  | @mr i₀ m R hR hm =>
    cases m with
    | zero => simp [lamM, xPow] at hP
    | succ m => simp [lamM, xPow] at hP
  | @rr i₀ m R₁ R₂ h₁ h₂ hm =>
    cases m with
    | zero =>
      simp only [lamM, xPow, Lambda.lam.injEq, Lambda.app.injEq] at hP
      exact h₁.ne_var hP.1
    | succ m => simp [lamM, xPow] at hP

theorem TGram.ne_lamM {x i : ℕ} (h : TGram x i lamM) : False := h.ne_lamM' rfl

/-! ### The contradiction -/

theorem xPow_app_unique {x : ℕ} : ∀ {k k' : ℕ} {A B A' B' : Lambda}, A ≠ .var x → A' ≠ .var x →
    xPow (.var x) k (.app A B) = xPow (.var x) k' (.app A' B') → k = k' ∧ A = A' ∧ B = B'
  | 0, 0, _, _, _, _, _, _, h => by simp only [xPow, Lambda.app.injEq] at h; exact ⟨rfl, h⟩
  | 0, k' + 1, _, _, _, _, hA, _, h => by
    simp only [xPow, Lambda.app.injEq] at h; exact absurd h.1 hA
  | k + 1, 0, _, _, _, _, _, hA', h => by
    simp only [xPow, Lambda.app.injEq] at h; exact absurd h.1.symm hA'
  | k + 1, k' + 1, _, _, _, _, hA, hA', h => by
    simp only [xPow, Lambda.app.injEq] at h
    obtain ⟨rfl, h2, h3⟩ := xPow_app_unique hA hA' h.2
    exact ⟨rfl, h2, h3⟩

theorem lamM_ne_var (x : ℕ) : lamM ≠ .var x := by simp [lamM]

/-- **A term and its `x`-prefix cannot both have shape.** -/
theorem TShape.not_xPrefix {x : ℕ} {N : Lambda} (h : TShape x N) (h' : TShape x (.app (.var x) N)) :
    False := by
  have key : ∀ {k : ℕ} {A B : Lambda}, A ≠ .var x → N = xPow (.var x) k (.app A B) →
      ∀ {k' : ℕ} {A' B' : Lambda}, A' ≠ .var x →
      Lambda.app (.var x) N = xPow (.var x) k' (.app A' B') → k' = k + 1 ∧ A' = A ∧ B' = B := by
    intro k A B hA hN k' A' B' hA' hN'
    rw [hN, show Lambda.app (.var x) (xPow (.var x) k (.app A B)) =
      xPow (.var x) (k + 1) (.app A B) from rfl] at hN'
    obtain ⟨h1, h2, h3⟩ := xPow_app_unique hA hA' hN'
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  cases h with
  | @mstage k j Q hQ hk =>
    generalize hN : Lambda.app (.var x) (xPow (.var x) k (.app lamM Q)) = N' at h'
    cases h' with
    | @mstage k' j' Q' hQ' hk' =>
      obtain ⟨rfl, -, rfl⟩ := key (lamM_ne_var x) rfl (lamM_ne_var x) hN
      obtain rfl := hQ.index_unique hQ'
      omega
    | @pair k' i' j' P' Q' hP' hQ' hk' =>
      obtain ⟨rfl, rfl, rfl⟩ := key (lamM_ne_var x) rfl (hP'.ne_var x) hN
      exact hP'.ne_lamM
  | @pair k i j P Q hP hQ hk =>
    generalize hN : Lambda.app (.var x) (xPow (.var x) k (.app P Q)) = N' at h'
    cases h' with
    | @mstage k' j' Q' hQ' hk' =>
      obtain ⟨rfl, rfl, rfl⟩ := key (hP.ne_var x) rfl (lamM_ne_var x) hN
      exact hP.ne_lamM
    | @pair k' i' j' P' Q' hP' hQ' hk' =>
      obtain ⟨rfl, rfl, rfl⟩ := key (hP.ne_var x) rfl (hP'.ne_var x) hN
      obtain rfl := hP.index_unique hP'
      obtain rfl := hQ.index_unique hQ'
      omega

theorem betaEtaReduces_app_var' {i : ℕ} {R T : Lambda}
    (h : betaEtaReduces (.app (.var i) R) T) : ∃ R', T = .app (.var i) R' ∧ betaEtaReduces R R' := by
  induction h with
  | refl => exact ⟨R, rfl, .refl _⟩
  | tail _ hs ih =>
    obtain ⟨R', rfl, hR⟩ := ih
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · exact (betaEtaStep_var hf).elim
    · exact ⟨a', rfl, hR.tail ha⟩

theorem toLam_rtg {u v : Tm} (h : Relation.ReflTransGen WStep u v) :
    Lambda.reduces (toLam u) (toLam v) := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact Lambda.reduces_trans ih (toLam_wstep hs)

/-- **Imamura's `T = B M (B (B M) B)` is not a βη fixed-point combinator.** -/
theorem T_not_fixedPoint : TNotFixedPoint := by
  intro hconv
  set N₀ : Lambda := .app lamM (toLam (tA 0 0)) with hN₀
  have hT : betaEtaReduces (toLam (app tT (var 0))) N₀ := .of_reduces (toLam_rtg (T_unfold 0))
  have hS : TShape 0 N₀ := TShape.mstage (k := 0) (j := 0) (TComp.toLam_tA 0 0).tGram rfl
  obtain ⟨w, hw₁, hw₂⟩ := hconv.common_reduct
  obtain ⟨w', rfl, hw'⟩ := betaEtaReduces_app_var' hw₂
  have hTw' : betaEtaReduces (toLam (app tT (var 0))) w' := hw'
  obtain ⟨D, hD₁, hD₂⟩ := betaEta_church_rosser hT hTw'
  obtain ⟨E, hE₁, hE₂⟩ := betaEta_church_rosser hT
    (hw₁.trans (betaEtaReduces_app_right (.var 0) hD₂))
  obtain ⟨D', rfl, hD'⟩ := betaEtaReduces_app_var' hE₂
  exact (hS.reduces (hD₁.trans hD')).not_xPrefix (hS.reduces hE₁)

/-- The same statement, written out. -/
theorem T_not_fixedPoint' :
    ¬ Lambda.betaEtaConv (toLam (app tT (var 0))) (toLam (app (var 0) (app tT (var 0)))) :=
  T_not_fixedPoint

end TLCA4
