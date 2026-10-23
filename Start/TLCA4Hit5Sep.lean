import Start.TLCA4Hit5QFree

/-!
# TLCA open problem 4: separating the `w`-heads from the components of `hit5`
(row M20-TLCA4-BETAETA; big round 2, run 3, item A1)

Step 3 of the route to the `unique` field of `TailCores (Ext (H5Core x) x) x`: the core `(W Q) Y`
(`W` a `w`-reduct) must not also be a core `P Q'` with `P = W Q` a component.

* `not_freeIn_lift_eq`, `not_freeIn1_lift2`, `TC.ne_var'` — tools;
* `TW.not_lam_app_free0` — a two-argument chain under `q` is not `λc` with `c` an application in
  which `0` is free;
* `WT.ne_lamB`, `WT.ne_bm`, `WT.ne_bmPre1`, `WT.ne_bmPre2`, `WT.ne_byl3`, **`WT.not_byR`** — no
  `w`-reduct is `B`, `B M`, `λab. M (a b)`, `λab. a b (a b)`, or a reduct of `B (B x)`;
* `WT.not_YG_app`, **`WT.not_HG_app`** — no component of `hit5` is `W Q` with `W` a `w`-reduct;
* `WqT.not_lift` — the constructor `ST.seta` is vacuous (`WqT` members have `q` free);
* `rq_ne_lift2`, `HC.ne_wP`, `TCYB.ne_wP`, `YG.not_lamB_app`, `ST.not_lamB_app` and
  **`TW.not_HG`** — a two-argument chain over any base of non-variables (such as the levels of
  `Ext`) is not a component of `hit5`; this separates the cores `M W'`, `W' Y` of the extension
  from `M Q` and `P Q`.
-/

set_option autoImplicit false

namespace TLCA4

theorem not_freeIn_lift_eq {t u : Lambda} {c : ℕ} (e : Lambda.lift 1 c t = u) (h : FreeIn c u) :
    False := by
  subst e; exact not_freeIn_lift t c h

theorem not_freeIn1_lift2 (t : Lambda) : ¬ FreeIn 1 (Lambda.lift 1 0 (Lambda.lift 1 0 t)) := by
  rw [lift_lift_zero_one]; exact not_freeIn_lift _ 1

theorem TC.ne_var' {base : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda} {k : ℕ}, base i P → P ≠ .var k) {n : ℤ} {C : Lambda}
    (h : TC base x n C) (k : ℕ) : C ≠ .var k := by
  cases h with
  | base hP => exact hb hP
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

/-- The bodies `W` of the `w`-abstractions are not `λ (a body with variable 0 free at the top)`
of the shapes of `lamB`, `bmPre1`, `bmPre2`, `byl1`, `byl2`, `byl3`. -/
theorem TW.not_lam_app_free0 {x : ℕ} {n : ℤ} {c : Lambda} (h : TW (YB x) (x + 1) n (.lam c))
    (hc : ∀ c', c ≠ .lam c') (h0 : FreeIn 0 c) : False := by
  generalize e : Lambda.lam c = t at h
  cases h with
  | wB _ => cases e
  | wP _ _ =>
    simp only [Lambda.lam.injEq] at e
    exact hc _ e
  | @wK R hR =>
    simp only [Lambda.lam.injEq] at e
    exact not_freeIn_lift_eq e.symm h0

theorem WT.ne_lamB {x : ℕ} (h : WT x lamB) : False := by
  generalize e : lamB = t at h
  cases h with
  | wbb _ => simp [lamB] at e
  | wpre _ => simp [lamB] at e
  | wpre2 _ => simp [lamB] at e
  | @wlam W hW =>
    simp only [lamB, Lambda.lam.injEq] at e
    subst e
    generalize e : Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 2)
      (Lambda.app (Lambda.var 1) (Lambda.var 0)))) = t at hW
    cases hW with
    | wB _ => cases e
    | @wP i' m R T hR hm =>
      simp only [Lambda.lam.injEq] at e
      cases m with
      | zero =>
        simp only [xPow, Lambda.app.injEq] at e
        obtain ⟨e1, -⟩ := e
        have h2 : Lambda.lift 1 0 (Lambda.lift 1 0 (.var 0)) = .var 2 := by simp [Lambda.lift]
        exact hR.ne_var' (fun hP => YB.ne_var hP) 0
          (Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 (e1.symm.trans h2.symm)))
      | succ m =>
        simp only [xPow, Lambda.app.injEq] at e
        obtain ⟨e1, -⟩ := e
        simp at e1
    | @wK R hR =>
      simp only [Lambda.lam.injEq] at e
      obtain ⟨c0, rfl, e2⟩ := Lambda.lift_eq_lam e.symm
      have : FreeIn 1 (Lambda.lift 1 (0 + 1) c0) := by rw [← e2]; simp [FreeIn]
      exact not_freeIn_lift c0 1 this

theorem WT.ne_lam1 {x : ℕ} {c : Lambda} (h : WT x (.lam (.lam c))) (hc : ∀ c', c ≠ .lam c')
    (h0 : FreeIn 0 c) : False := by
  generalize e : Lambda.lam (.lam c) = t at h
  cases h with
  | wbb _ => cases e
  | wpre _ => cases e
  | wpre2 _ => cases e
  | wlam hW =>
    simp only [Lambda.lam.injEq] at e
    subst e
    exact hW.not_lam_app_free0 hc h0

theorem WT.ne_bmPre1 {x : ℕ} (h : WT x bmPre1) : False :=
  WT.ne_lam1 (c := .app lamM (.app (.var 1) (.var 0))) h (fun _ => by simp)
    (Or.inr (Or.inr rfl))

theorem WT.ne_bmPre2 {x : ℕ} (h : WT x bmPre2) : False :=
  WT.ne_lam1 (c := .app (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0))) h (fun _ => by simp)
    (Or.inr (Or.inr rfl))

theorem WT.ne_bm {x : ℕ} (h : WT x (.app lamB lamM)) : False := by
  generalize e : Lambda.app lamB lamM = t at h
  cases h with
  | wbb _ => simp [lamB, lamM] at e
  | wpre _ => simp [lamB, lamM, bbPre] at e
  | wpre2 _ => simp [lamB, lamM, bbPre2] at e
  | wlam _ => cases e

theorem WT.ne_byl3 {x : ℕ} (h : WT x (byl3 x)) : False := by
  generalize e : byl3 x = t at h
  cases h with
  | wbb _ => simp [byl3] at e
  | wpre _ => simp [byl3] at e
  | wpre2 _ => simp [byl3] at e
  | @wlam W hW =>
    simp only [byl3, Lambda.lam.injEq] at e
    subst e
    generalize e : Lambda.lam (Lambda.lam (Lambda.app (Lambda.var (x + 3))
      (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 1)) (Lambda.var 0)))) = t at hW
    cases hW with
    | wB _ => cases e
    | @wP i' m R T hR hm =>
      simp only [Lambda.lam.injEq] at e
      cases m with
      | zero =>
        simp only [xPow, Lambda.app.injEq] at e
        obtain ⟨e1, -⟩ := e
        have h2 : Lambda.lift 1 0 (Lambda.lift 1 0 (.var (x + 1))) = .var (x + 3) := by
          simp [Lambda.lift]
        exact hR.ne_var' (fun hP => YB.ne_var hP) (x + 1)
          (Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 (e1.symm.trans h2.symm)))
      | succ m =>
        cases m with
        | zero =>
          simp only [xPow, Lambda.app.injEq] at e
          obtain ⟨-, e2, -⟩ := e
          exact not_freeIn1_lift2 R (by rw [← e2]; exact Or.inr rfl)
        | succ m =>
          simp [xPow] at e
    | @wK R hR =>
      simp only [Lambda.lam.injEq] at e
      obtain ⟨c0, rfl, e2⟩ := Lambda.lift_eq_lam e.symm
      have : FreeIn 1 (Lambda.lift 1 (0 + 1) c0) := by rw [← e2]; simp [FreeIn]
      exact not_freeIn_lift c0 1 this

/-- **A reduct of `B (B x)` is not a `w`-reduct.** -/
theorem WT.not_byR {x : ℕ} {R : Lambda} (hR : ByR x R) (h : WT x R) : False := by
  cases hR with
  | bb =>
    generalize e : bbx x = t at h
    cases h with
    | wbb _ => simp [bbx, lamB] at e
    | wpre _ => simp [bbx, lamB, bbPre] at e
    | wpre2 _ => simp [bbx, lamB, bbPre2] at e
    | wlam _ => cases e
  | bpre =>
    generalize e : bbpre x = t at h
    cases h with
    | wbb _ => simp [bbpre, lamB] at e
    | wpre _ => simp [bbpre, lamB, bbPre] at e
    | wpre2 _ => simp [bbpre, lamB, bbPre2] at e
    | wlam _ => cases e
  | l1 =>
    exact WT.ne_lam1 (c := .app (.app lamB (.var (x + 2))) (.app (.var 1) (.var 0))) h
      (fun _ => by simp) (Or.inr (Or.inr rfl))
  | l2 =>
    exact WT.ne_lam1 (c := .app (bxPre (x + 2)) (.app (.var 1) (.var 0))) h
      (fun _ => by simp) (Or.inr (Or.inr rfl))
  | l3 => exact WT.ne_byl3 h

theorem WT.not_YG_app {x i : ℕ} {W Q : Lambda} (hW : WT x W) (h : YG x i (.app W Q)) : False := by
  generalize e : Lambda.app W Q = t at h
  cases h with
  | bm _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.ne_bm
  | bm1 _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.ne_bmPre1
  | bm2 _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.ne_bmPre2
  | byApp hR _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.not_byR hR
  | lam _ => cases e

/-- **A component of `hit5` is not of the form `W Q` with `W` a `w`-reduct.** -/
theorem WT.not_HG_app {x i : ℕ} {W Q : Lambda} (hW : WT x W) (h : HG x i (.app W Q)) : False := by
  generalize e : Lambda.app W Q = t at h
  cases h with
  | yg hY => subst e; exact hW.not_YG_app hY
  | st hS =>
    subst e
    generalize e : Lambda.app W Q = t at hS
    cases hS with
    | sbm _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.ne_bm
    | sbm1 _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.ne_bmPre1
    | sbm2 _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.ne_bmPre2
    | slam _ => cases e
    | sv hV => subst e; exact hW.not_YG_app hV
    | seta hW' =>
      subst e
      simp only [Lambda.lift] at hW'
      generalize e : Lambda.app (Lambda.lift 1 0 W) (Lambda.lift 1 0 Q) = t at hW'
      cases hW' with
      | ap _ =>
        simp only [Lambda.app.injEq] at e
        exact not_freeIn_lift_eq e.2 rfl
      | body hT =>
        cases hT with
        | wB _ =>
          simp only [Lambda.app.injEq] at e
          have : W = lamB := Lambda.lift_one_injective 0 (e.1.trans (lift_lamB 0).symm)
          subst this; exact hW.ne_lamB
        | wP _ _ => cases e
        | wK _ => cases e
  | byApp hR _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hW.not_byR hR
  | lam _ _ => cases e

/-- **The constructor `ST.seta` is vacuous**: `WqT` members have `q` free, lifted terms do not. -/
theorem WqT.not_lift {x : ℕ} {f : Lambda} (h : WqT x (Lambda.lift 1 0 f)) : False :=
  not_freeIn_lift f 0 h.freeIn0

theorem lift1_ne_var {R : Lambda} {y : ℕ} (h : R ≠ .var y) : Lambda.lift 1 0 R ≠ .var (y + 1) := by
  intro e
  cases R with
  | var k =>
    simp only [Lambda.lift] at e
    split at e
    · omega
    · simp at e; exact h (by rw [e])
  | app _ _ => simp [Lambda.lift] at e
  | lam _ => simp [Lambda.lift] at e

/-- A chain-shaped abstraction `λd. xᵐ (lift R' T')` with `R'` having `q` free is not
`λd. xᵐ (lift (lift R) T)`. -/
theorem rq_ne_lift2 {x m m' : ℕ} {R R' T T' : Lambda} (hR : R ≠ .var x) (hR' : R' ≠ .var (x + 1))
    (h0 : FreeIn 0 R')
    (e : xPow (.var (x + 2)) m' (.app (Lambda.lift 1 0 R') T') =
      xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)) : False := by
  obtain ⟨-, e1, -⟩ := xPow_app_unique (lift1_ne_var hR') (lift2_ne_var hR) e
  have := Lambda.lift_one_injective 0 e1
  subst this
  exact not_freeIn_lift R 0 h0

theorem HC.ne_wP {x : ℕ} {n : ℤ} {C c R T : Lambda} {m : ℕ} (hC : HC x n C) (hR : R ≠ .var x)
    (e : C = .lam c) (ec : c = xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)) :
    False := by
  cases hC with
  | base hb => subst e; exact hb.not_lam
  | bx _ => cases e
  | bx1 _ => cases e
  | rq hR' _ =>
    simp only [Lambda.lam.injEq] at e
    subst e
    exact rq_ne_lift2 hR (hR'.ne_var) hR'.freeIn0 ec

theorem TCYB.ne_wP {x : ℕ} {n : ℤ} {C c R T : Lambda} {m : ℕ} (hC : TC (YB x) (x + 1) n C)
    (hR : R ≠ .var x) (e : C = .lam c)
    (ec : c = xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)) : False := by
  cases hC with
  | base hb => subst e; exact YB.not_lam hb
  | bx _ => cases e
  | bx1 _ => cases e
  | rq hR' _ =>
    simp only [Lambda.lam.injEq] at e
    subst e
    exact rq_ne_lift2 hR (hR'.ne_var' (fun hP => YB.ne_var hP) _) (hR'.freeIn0 YB.freeIn0) ec

theorem YG.not_lamB_app {x i : ℕ} {R : Lambda} (h : YG x i (.app lamB R)) : False := by
  generalize e : Lambda.app lamB R = t at h
  cases h with
  | bm _ => simp [lamB, lamM] at e
  | bm1 _ => simp [lamB, bmPre1] at e
  | bm2 _ => simp [lamB, bmPre2] at e
  | byApp hR _ => simp only [Lambda.app.injEq] at e; exact hR.ne_lamB e.1.symm
  | lam _ => cases e

theorem ST.not_lamB_app {x : ℕ} {R : Lambda} (h : ST x (.app lamB R)) : False := by
  generalize e : Lambda.app lamB R = t at h
  cases h with
  | sbm _ => simp [lamB, lamM] at e
  | sbm1 _ => simp [lamB, bmPre1] at e
  | sbm2 _ => simp [lamB, bmPre2] at e
  | slam _ => cases e
  | sv hV => subst e; exact hV.not_lamB_app
  | seta hW => exact hW.not_lift

/-- **A two-argument chain over a base of non-variables is not a component of `hit5`.** -/
theorem TW.not_HG {base : ℤ → Lambda → Prop} {x : ℕ}
    (hbv : ∀ {i : ℤ} {P : Lambda} {k : ℕ}, base i P → P ≠ .var k) {n : ℤ} {j : ℕ} {W : Lambda}
    (hW : TW base x n W) (h : HG x j W) : False := by
  cases hW with
  | wB hR =>
    generalize e : Lambda.app lamB _ = t at h
    cases h with
    | yg hY => subst e; exact hY.not_lamB_app
    | st hS => subst e; exact hS.not_lamB_app
    | byApp hR' _ => simp only [Lambda.app.injEq] at e; exact hR'.ne_lamB e.1.symm
    | lam _ _ => cases e
  | @wP i' m R T hR hm =>
    have hRv : R ≠ .var x := hR.ne_var' hbv x
    generalize e : Lambda.lam (.lam (xPow (.var (x + 2)) m
      (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))) = t at h
    cases h with
    | yg hY =>
      subst e
      generalize e : Lambda.lam (.lam (xPow (.var (x + 2)) m
        (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))) = t at hY
      cases hY with
      | bm _ => cases e
      | bm1 _ => cases e
      | bm2 _ => cases e
      | byApp _ _ => cases e
      | lam hc =>
        simp only [Lambda.lam.injEq] at e
        exact HC.ne_wP (YC.toHC hc) hRv e.symm rfl
    | st hS =>
      subst e
      generalize e : Lambda.lam (.lam (xPow (.var (x + 2)) m
        (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))) = t at hS
      cases hS with
      | sbm _ => cases e
      | sbm1 _ => cases e
      | sbm2 _ => cases e
      | slam hS' =>
        simp only [Lambda.lam.injEq] at e
        subst e
        generalize e : Lambda.lam (xPow (.var (x + 2)) m
          (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)) = t at hS'
        cases hS' with
        | mw _ => cases e
        | ww _ => cases e
        | core hP => exact TCYB.ne_wP hP hRv e.symm rfl
      | sv hV =>
        subst e
        generalize e : Lambda.lam (.lam (xPow (.var (x + 2)) m
          (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))) = t at hV
        cases hV with
        | bm _ => cases e
        | bm1 _ => cases e
        | bm2 _ => cases e
        | lam hc =>
          simp only [Lambda.lam.injEq] at e
          exact HC.ne_wP (YC.toHC hc) hRv e.symm rfl
      | seta hW => exact hW.not_lift
    | byApp _ _ => cases e
    | lam hc _ =>
      simp only [Lambda.lam.injEq] at e
      exact HC.ne_wP hc hRv e.symm rfl
  | @wK R hR =>
    generalize e : Lambda.lam (Lambda.lift 1 0 R) = t at h
    cases h with
    | yg hY =>
      subst e
      generalize e : Lambda.lam (Lambda.lift 1 0 R) = t at hY
      cases hY with
      | bm _ => cases e
      | bm1 _ => cases e
      | bm2 _ => cases e
      | byApp _ _ => cases e
      | lam hc =>
        simp only [Lambda.lam.injEq] at e
        subst e
        exact not_freeIn_lift R 0 (YC.toHC hc).freeIn0
    | st hS =>
      subst e
      generalize e : Lambda.lam (Lambda.lift 1 0 R) = t at hS
      cases hS with
      | sbm _ => cases e
      | sbm1 _ => cases e
      | sbm2 _ => cases e
      | slam hS' =>
        simp only [Lambda.lam.injEq] at e
        subst e
        exact not_freeIn_lift R 0 hS'.freeIn0
      | sv hV =>
        subst e
        generalize e : Lambda.lam (Lambda.lift 1 0 R) = t at hV
        cases hV with
        | bm _ => cases e
        | bm1 _ => cases e
        | bm2 _ => cases e
        | lam hc =>
          simp only [Lambda.lam.injEq] at e
          subst e
          exact not_freeIn_lift R 0 (YC.toHC hc).freeIn0
      | seta hW => exact hW.not_lift
    | byApp _ _ => cases e
    | lam hc _ =>
      simp only [Lambda.lam.injEq] at e
      subst e
      exact not_freeIn_lift R 0 hc.freeIn0

end TLCA4
