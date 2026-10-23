import Start.TLCA4Hit5Sep

/-!
# TLCA open problem 4: the syntactic fields of `TailCores` for the extended cores of `hit5`
(row M20-TLCA4-BETAETA; big round 2, run 3, item A1)

Of the six fields of `TailCores (Ext (H5Core x) x) x`, `step` is `H5Ext.step` and `not_lam` is
`Ext.not_lam H5Core.not_lam`.  This module proves three more:

* **`H5Ext.ne_var`** — no core is a variable;
* **`H5Ext.ne_bx`** — no core is `B x Q` (`HG.not_lamB_app`: no component has head `B` applied
  to one argument);
* **`H5Ext.ne_bx1`** — no core is `(λab. x (a b)) Q` (`HG.not_bxPre`: `λab. x (a b)` is not a
  component, through `rq_ne_bxBody`, `HC.ne_bxPreBody`, `TCYB.ne_bxPreBody`);
* `TW.not_WT_app` — a two-argument chain is not `W Q` with `W` a `w`-reduct.

Only the field `unique` remains.
-/

set_option autoImplicit false

namespace TLCA4

/-- No component of `hit5` has head `B` applied to one argument. -/
theorem HG.not_lamB_app {x i : ℕ} {R : Lambda} (h : HG x i (.app lamB R)) : False := by
  generalize e : Lambda.app lamB R = t at h
  cases h with
  | yg hY => subst e; exact hY.not_lamB_app
  | st hS => subst e; exact hS.not_lamB_app
  | byApp hR _ => simp only [Lambda.app.injEq] at e; exact hR.ne_lamB e.1.symm
  | lam _ _ => cases e

/-- A two-argument chain over a base of non-variables is not `W Q` with `W` a `w`-reduct. -/
theorem TW.not_WT_app {base : ℤ → Lambda → Prop} {x : ℕ} {n : ℤ} {W Q : Lambda}
    (hT : TW base x n (.app W Q)) (hW : WT x W) : False := by
  generalize e : Lambda.app W Q = t at hT
  cases hT with
  | wB _ =>
    simp only [Lambda.app.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact hW.ne_lamB
  | wP _ _ => cases e
  | wK _ => cases e

theorem H5ExtL.ne_var {x : ℕ} {K : ℤ} {k : ℕ} :
    ∀ (l : ℕ) {i : ℤ} {P : Lambda}, ExtL (H5Core x) x l K i P → P ≠ .var k
  | 0, _, _, hl => by cases hl <;> simp
  | l + 1, _, _, hl => by
    rcases hl with hl | ⟨W, rfl, -⟩ | ⟨W, Y, rfl, -⟩
    · exact H5ExtL.ne_var l hl
    · simp
    · simp

/-- The cores of the extension are not variables. -/
theorem H5Ext.ne_var {x : ℕ} {K i : ℤ} {P : Lambda} {k : ℕ} (h : Ext (H5Core x) x K i P) :
    P ≠ .var k := by
  obtain ⟨l, hl⟩ := h
  exact H5ExtL.ne_var l hl

theorem H5ExtL.ne_bx {x : ℕ} {K : ℤ} {Q : Lambda} :
    ∀ (l : ℕ) {i : ℤ} {P : Lambda}, ExtL (H5Core x) x l K i P →
      P ≠ .app (.app lamB (.var x)) Q
  | 0, _, _, hl => by
    intro e
    cases hl with
    | pq hP _ _ =>
      simp only [Lambda.app.injEq] at e
      rw [e.1] at hP; exact hP.not_lamB_app
    | mq _ _ => simp [lamM, lamB] at e
    | mwq _ _ _ => simp [lamM, lamB] at e
    | wqy hW _ _ =>
      simp only [Lambda.app.injEq] at e
      obtain ⟨⟨rfl, -⟩, -⟩ := e
      exact hW.ne_lamB
  | l + 1, _, _, hl => by
    rcases hl with hl | ⟨W, rfl, -⟩ | ⟨W, Y, rfl, hW⟩
    · exact H5ExtL.ne_bx l hl
    · simp [lamM, lamB]
    · intro e
      simp only [Lambda.app.injEq] at e
      obtain ⟨rfl, -⟩ := e
      generalize e : Lambda.app lamB (.var x) = t at hW
      cases hW with
      | wB hR =>
        simp only [Lambda.app.injEq, true_and] at e
        exact hR.ne_var' (fun hP => H5ExtL.ne_var l hP) x e.symm
      | wP _ _ => cases e
      | wK _ => cases e

/-- The cores of the extension are not `B x Q`. -/
theorem H5Ext.ne_bx {x : ℕ} {K i : ℤ} {P Q : Lambda} (h : Ext (H5Core x) x K i P) :
    P ≠ .app (.app lamB (.var x)) Q := by
  obtain ⟨l, hl⟩ := h
  exact H5ExtL.ne_bx l hl

theorem rq_ne_bxBody {x m : ℕ} {R T : Lambda} (hR : ∀ k, R ≠ .var k)
    (e : xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) T) =
      .app (.var (x + 2)) (.app (.var 1) (.var 0))) : False := by
  match m, e with
  | 0, e =>
    simp only [xPow, Lambda.app.injEq] at e
    exact lift1_ne_var (hR (x + 1)) e.1
  | 1, e =>
    simp only [xPow, Lambda.app.injEq, true_and] at e
    exact lift1_ne_var (hR 0) e.1
  | m + 2, e =>
    simp only [xPow, Lambda.app.injEq, true_and] at e
    obtain ⟨e1, -⟩ := e
    simp at e1

theorem HC.ne_bxPreBody {x : ℕ} {n : ℤ} {c : Lambda} (hC : HC x n (.lam c))
    (e : c = .app (.var (x + 2)) (.app (.var 1) (.var 0))) : False := by
  generalize e' : Lambda.lam c = t at hC
  cases hC with
  | base hb => subst e'; exact hb.not_lam
  | bx _ => cases e'
  | bx1 _ => cases e'
  | rq hR _ =>
    simp only [Lambda.lam.injEq] at e'
    subst e'
    exact rq_ne_bxBody (fun k => hR.ne_var) e

theorem TCYB.ne_bxPreBody {x : ℕ} {n : ℤ} {c : Lambda} (hC : TC (YB x) (x + 1) n (.lam c))
    (e : c = .app (.var (x + 2)) (.app (.var 1) (.var 0))) : False := by
  generalize e' : Lambda.lam c = t at hC
  cases hC with
  | base hb => subst e'; exact YB.not_lam hb
  | bx _ => cases e'
  | bx1 _ => cases e'
  | rq hR _ =>
    simp only [Lambda.lam.injEq] at e'
    subst e'
    exact rq_ne_bxBody (fun k => hR.ne_var' (fun hP => YB.ne_var hP) k) e

theorem YG.not_bxPre {x i : ℕ} (h : YG x i (bxPre x)) : False := by
  generalize e : bxPre x = t at h
  cases h with
  | bm _ => simp [bxPre] at e
  | bm1 _ => simp [bxPre] at e
  | bm2 _ => simp [bxPre] at e
  | byApp _ _ => simp [bxPre] at e
  | lam hc =>
    simp only [bxPre, Lambda.lam.injEq] at e
    subst e
    exact HC.ne_bxPreBody (YC.toHC hc) rfl

/-- **`λab. x (a b)` is not a component of `hit5`.** -/
theorem HG.not_bxPre {x i : ℕ} (h : HG x i (bxPre x)) : False := by
  generalize e : bxPre x = t at h
  cases h with
  | yg hY => subst e; exact hY.not_bxPre
  | st hS =>
    subst e
    generalize e : bxPre x = t at hS
    cases hS with
    | sbm _ => simp [bxPre] at e
    | sbm1 _ => simp [bxPre] at e
    | sbm2 _ => simp [bxPre] at e
    | slam hS' =>
      simp only [bxPre, Lambda.lam.injEq] at e
      subst e
      generalize e : Lambda.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0))) = t at hS'
      cases hS' with
      | mw _ => cases e
      | ww _ => cases e
      | core hP => subst e; exact TCYB.ne_bxPreBody hP rfl
    | sv hV => subst e; exact hV.not_bxPre
    | seta hW => exact hW.not_lift
  | byApp _ _ => simp [bxPre] at e
  | lam hc _ =>
    simp only [bxPre, Lambda.lam.injEq] at e
    subst e
    exact HC.ne_bxPreBody hc rfl

theorem H5ExtL.ne_bx1 {x : ℕ} {K : ℤ} {Q : Lambda} :
    ∀ (l : ℕ) {i : ℤ} {P : Lambda}, ExtL (H5Core x) x l K i P → P ≠ .app (bxPre x) Q
  | 0, _, _, hl => by
    intro e
    cases hl with
    | pq hP _ _ =>
      simp only [Lambda.app.injEq] at e
      rw [e.1] at hP; exact hP.not_bxPre
    | mq _ _ => simp [lamM, bxPre] at e
    | mwq _ _ _ => simp [lamM, bxPre] at e
    | wqy _ _ _ => simp [bxPre] at e
  | l + 1, _, _, hl => by
    rcases hl with hl | ⟨W, rfl, -⟩ | ⟨W, Y, rfl, hW⟩
    · exact H5ExtL.ne_bx1 l hl
    · simp [lamM, bxPre]
    · intro e
      simp only [Lambda.app.injEq] at e
      obtain ⟨rfl, -⟩ := e
      generalize e : bxPre x = t at hW
      cases hW with
      | wB _ => simp [bxPre] at e
      | @wP i' m R T hR hm =>
        simp only [bxPre, Lambda.lam.injEq] at e
        have hRv := hR.ne_var' (fun hP => H5ExtL.ne_var l hP)
        match m, e with
        | 0, e =>
          simp only [xPow, Lambda.app.injEq] at e
          exact lift2_ne_var (hRv x) e.1.symm
        | 1, e =>
          simp only [xPow, Lambda.app.injEq, true_and] at e
          exact not_freeIn1_lift2 R (by rw [← e.1]; exact rfl)
        | m + 2, e =>
          simp only [xPow, Lambda.app.injEq, true_and] at e
          obtain ⟨e1, -⟩ := e
          simp at e1
      | @wK R hR =>
        simp only [bxPre, Lambda.lam.injEq] at e
        obtain ⟨c0, rfl, e2⟩ := Lambda.lift_eq_lam e.symm
        have : FreeIn 1 (Lambda.lift 1 (0 + 1) c0) := by rw [← e2]; simp [FreeIn]
        exact not_freeIn_lift c0 1 this

theorem H5Ext.ne_bx1 {x : ℕ} {K i : ℤ} {P Q : Lambda} (h : Ext (H5Core x) x K i P) :
    P ≠ .app (bxPre x) Q := by
  obtain ⟨l, hl⟩ := h
  exact H5ExtL.ne_bx1 l hl

end TLCA4
