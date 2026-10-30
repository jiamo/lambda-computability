import Start.TLCA4Hit5Core

/-!
# TLCA open problem 4: a grammar of normalized stage components
(row M20-TLCA4-BETAETA; big round 2, item A2, rebuilt in run 6 after the move to a new project)

The grammars for `Q` and `hit5` follow the combinators through every intermediate form.  This
module starts instead from a partly normalized reduct.  Under a binder `q` (variable `0`, `x` at
index `x + 1`), write

    G_q = qG x T = λz w'. x (q z T)          (`T` arbitrary).

* `NG x i` — components of index `i`: abstractions `λq. C` with `C` a chain of height `i + 1`;
* `NC x n` — chains under `q` of integer height `n` with **arbitrary tails** (as `HC`);
* `NB x n` — their cores: `q G_q` (height `0`) and `R q` with `R` a component of index `i'`
  (height `i' + 1`);
* **`NG.step`**, `NC.step`, `NB.step` — closure under one βη-step; `NG.reduces`;
* `NG.fire_q`, `NG.exists_lam`, `NC.ne_var`, `NB.not_lam`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- `G_q = λz w'. x (q z T)` under the binder `q` (`q` = variable `0`, `x` at index `x + 1`). -/
def qG (x : ℕ) (T : Lambda) : Lambda :=
  .lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) T)))

mutual
/-- Normalized stage components of index `i` (`x` at index `x`). -/
inductive NG (x : ℕ) : ℕ → Lambda → Prop
  | lam {i : ℕ} {n : ℤ} {c : Lambda} : NC x n c → n = (i : ℤ) + 1 → NG x i (.lam c)
/-- `x`-chains under the binder `q` (so `x` at index `x + 1`) with arbitrary tails. -/
inductive NC (x : ℕ) : ℤ → Lambda → Prop
  | base {n : ℤ} {P : Lambda} : NB x n P → NC x n P
  | bx {n : ℤ} {P : Lambda} : NC x n P → NC x (n + 1) (.app (.app lamB (.var (x + 1))) P)
  | bx1 {n : ℤ} {P : Lambda} : NC x n P → NC x (n + 1) (.app (bxPre (x + 1)) P)
  | rq {n n' : ℤ} {m : ℕ} {R T : Lambda} : NC x n' R → (m : ℤ) + n' = n →
      NC x n (.lam (xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) T)))
/-- The cores of the chains (`q` = variable `0`). -/
inductive NB (x : ℕ) : ℤ → Lambda → Prop
  | q {T : Lambda} : NB x 0 (.app (.var 0) (qG x T))
  | comp {i' : ℕ} {n : ℤ} {R : Lambda} : NG x i' R → n = (i' : ℤ) + 1 →
      NB x n (.app (Lambda.lift 1 0 R) (.var 0))
end

theorem NB.not_lam {x : ℕ} {n : ℤ} {c : Lambda} (h : NB x n (.lam c)) : False := by
  cases h

theorem NB.ne_var {x : ℕ} {n : ℤ} {P : Lambda} {j : ℕ} (h : NB x n P) : P ≠ .var j := by
  cases h <;> simp

theorem NC.ne_var {x : ℕ} {n : ℤ} {P : Lambda} {j : ℕ} (h : NC x n P) : P ≠ .var j := by
  cases h with
  | base hb => exact hb.ne_var
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

theorem NG.exists_lam {x i : ℕ} {P : Lambda} (h : NG x i P) : ∃ c, P = .lam c := by
  cases h with
  | lam _ _ => exact ⟨_, rfl⟩

theorem NG.ne_var {x i : ℕ} {P : Lambda} {j : ℕ} (h : NG x i P) : P ≠ .var j := by
  obtain ⟨c, rfl⟩ := h.exists_lam; simp

/-- Firing a component on `q`: the body of a component of index `i'` is a chain of height
`i' + 1`. -/
theorem NG.fire_q {x i' : ℕ} {c0 : Lambda} (hR : NG x i' (.lam c0)) :
    NC x ((i' : ℤ) + 1) c0 := by
  generalize e : Lambda.lam c0 = t at hR
  cases hR with
  | lam hc hn =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [← hn]; exact hc

/-- A chain that is an abstraction, applied to a tail, gives a chain under the same binder. -/
theorem NC.beta_lift {x : ℕ} {n' : ℤ} {R c0 T : Lambda} (hR : NC x n' R) (e : R = .lam c0)
    (m : ℕ) :
    NC x ((m : ℤ) + n') (.lam (xPow (.var (x + 2)) m (Lambda.subst T 0 (Lambda.lift 1 1 c0)))) := by
  cases hR with
  | base hb => subst e; exact hb.not_lam.elim
  | bx _ => cases e
  | bx1 _ => cases e
  | @rq _ i'' m' R' T' hR' hm =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [lift_xPow, subst_xPow]
    simp only [Lambda.lift, Lambda.subst, subst_lift_lift_one]
    have hx : Lambda.subst T 0 (.var (x + 2 + 1)) = .var (x + 2) := by
      simp [Lambda.subst]
    rw [ite_eq_right (by omega), hx, xPow_add]
    exact .rq hR' (by push_cast; omega)

/-- The η-contractum of a component `λq. c` is a component of the same index. -/
theorem NC.eta_inv {x i : ℕ} {n : ℤ} {c f : Lambda} (h : NC x n c) (hn : n = (i : ℤ) + 1)
    (hf : c = .app (Lambda.lift 1 0 f) (.var 0)) : NG x i f := by
  subst hf
  generalize e : Lambda.app (Lambda.lift 1 0 f) (.var 0) = t at h
  cases h with
  | base hb =>
    cases hb with
    | q =>
      simp only [Lambda.app.injEq] at e
      exact absurd e.2.symm (by simp [qG])
    | @comp i' _ R hR hn' =>
      simp only [Lambda.app.injEq] at e
      rw [Lambda.lift_one_injective 0 e.1]
      have : i' = i := by omega
      subst this; exact hR
  | bx hP => simp only [Lambda.app.injEq] at e; exact (hP.ne_var e.2.symm).elim
  | bx1 hP => simp only [Lambda.app.injEq] at e; exact (hP.ne_var e.2.symm).elim
  | rq _ _ => cases e

/-- A βη-step of `G_q` happens inside its tail. -/
theorem qG_step {x : ℕ} {T P' : Lambda} (hs : betaEtaStep (qG x T) P') :
    ∃ T', P' = qG x T' := by
  unfold qG at hs
  rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
  · rcases betaEtaStep_lam_cases hb with ⟨b'', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · rcases betaEtaStep_app_cases hb' with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
      · cases hc
      · exact (betaEtaStep_var hf).elim
      · rcases betaEtaStep_app_cases ha with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a'', ha', rfl⟩
        · rcases hc
        · rcases betaEtaStep_app_cases hf with ⟨c, hc, _⟩ | ⟨f'', hf', _⟩ | ⟨a''', ha'', _⟩
          · cases hc
          · exact (betaEtaStep_var hf').elim
          · exact (betaEtaStep_var ha'').elim
        · exact ⟨a'', rfl⟩
    · simp only [Lambda.app.injEq] at hf
      exact absurd hf.2 (by simp)
  · cases hf

mutual
theorem NG.step {x i : ℕ} {P P' : Lambda} (h : NG x i P) (hs : betaEtaStep P P') :
    NG x i P' := by
  match h with
  | .lam hc hn =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .lam (NC.step hc hb) hn
    · exact NC.eta_inv hc hn hf
theorem NC.step {x : ℕ} {n : ℤ} {P P' : Lambda} (h : NC x n P) (hs : betaEtaStep P P') :
    NC x n P' := by
  match h with
  | .base hb => exact NB.step hb hs
  | .bx h =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bx1 h
      · exact (nf_lamB _ hf').elim
      · exact (betaEtaStep_var ha).elim
    · exact .bx (NC.step h ha)
  | .bx1 h =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bxPre, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ P : Lambda, Lambda.subst P 0
          (.lam (.app (.var (x + 1 + 2)) (.app (.var 1) (.var 0)))) =
          .lam (xPow (.var (x + 2)) 1 (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst, xPow]
      rw [e]; exact NC.rq (m := 1) h (by push_cast; ring)
    · exact (nf_bxPre _ _ hf).elim
    · exact .bx1 (NC.step h ha)
  | @NC.rq _ i₀ i' m R T h hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        have := NC.beta_lift (T := T) h rfl m
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (NC.step h hR') hm
      · exact .rq h hm
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by push_cast at hm; omega
      subst e
      exact h
theorem NB.step {x : ℕ} {n : ℤ} {P P' : Lambda} (h : NB x n P) (hs : betaEtaStep P P') :
    NC x n P' := by
  match h with
  | .q =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · exact (betaEtaStep_var hf).elim
    · obtain ⟨T', rfl⟩ := qG_step ha
      exact .base .q
  | .comp hR hn =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
    · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
      rw [Lambda.subst_var_lift_succ c0 0, hn]
      exact hR.fire_q
    · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
      exact .base (.comp (NG.step hR hR') hn)
    · exact (betaEtaStep_var ha).elim
end

theorem NG.reduces {x i : ℕ} {P Q : Lambda} (h : NG x i P) (hr : betaEtaReduces P Q) :
    NG x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- The explicit stage shape `λa w. x (a G_a T)`, `G_a = λz w'. x (a z T')` (`x` free, at index
`x` outside). -/
def nfStage (x : ℕ) (T T' : Lambda) : Lambda :=
  .lam (.lam (.app (.var (x + 2)) (.app (.app (.var 1) (Lambda.lift 1 0 (qG x T'))) T)))

/-- **The explicit stage shape is a component of index `0`.** -/
theorem nfStage_NG (x : ℕ) (T T' : Lambda) : NG x 0 (nfStage x T T') := by
  have e : nfStage x T T' = .lam (.lam (xPow (.var (x + 2)) 1
      (.app (Lambda.lift 1 0 (.app (.var 0) (qG x T'))) T))) := by
    simp [nfStage, xPow, Lambda.lift]
  rw [e]
  exact .lam (.rq (m := 1) (.base .q) rfl) (by norm_num)

end TLCA4
