import Start.TLCA4Hit5TW

/-!
# TLCA open problem 4: the components `uⁿ s` of `hit5`
(row M20-TLCA4-BETAETA; big round 2, run 1, item A1)

The components of the stages `s (uⁿ s) Wₙ` of `hit5 x` (`Start/TLCA4Hit5Stages.lean`) are the
terms `uⁿ s`, `u = B (B x)`.  This module gives a βη-closed grammar for them and their reducts,
built like the grammar `YG` of the components of `Q` (`Start/TLCA4YGrammar.lean`), with three
changes:

* the `s`-reducts (`ST`, `Start/TLCA4Hit5TW.lean`) are components of index `0`, besides the
  `v`-reducts (`YG`);
* the chains under the component binder `q` have **arbitrary tails** (`λd. xᵐ (C T)`), because
  the bodies `Wq Y` of the `s`-reducts fire into such chains;
* the cores under `q` include `M Wq` and `Wq Y` with `Wq` a reduct of `W q`, `W` a `w`-reduct.

* `HG x i` — components of index `i`; `HC x n` — chains of integer height `n` under `q`;
  `HB x n` — their cores;
* **`HG.step`**, `HC.step`, `HB.step` — closure under one βη-step; `HG.reduces`;
* **`HG.of_h5A`** — the components `uⁿ s` are in the grammar at index `n`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

mutual
/-- The components of the stages of `hit5 x` (reducts of `uⁱ s` and `uⁱ v`), `x` at index `x`. -/
inductive HG (x : ℕ) : ℕ → Lambda → Prop
  | yg {i : ℕ} {P : Lambda} : YG x i P → HG x i P
  | st {P : Lambda} : ST x P → HG x 0 P
  | byApp {i : ℕ} {R P : Lambda} : ByR x R → HG x i P → HG x (i + 1) (.app R P)
  | lam {i : ℕ} {n : ℤ} {c : Lambda} : HC x n c → n = (i : ℤ) + 1 → HG x i (.lam c)
/-- `x`-chains under the binder `q` (so `x` at index `x + 1`) with arbitrary tails. -/
inductive HC (x : ℕ) : ℤ → Lambda → Prop
  | base {n : ℤ} {P : Lambda} : HB x n P → HC x n P
  | bx {n : ℤ} {P : Lambda} : HC x n P → HC x (n + 1) (.app (.app lamB (.var (x + 1))) P)
  | bx1 {n : ℤ} {P : Lambda} : HC x n P → HC x (n + 1) (.app (bxPre (x + 1)) P)
  | rq {n n' : ℤ} {m : ℕ} {R T : Lambda} : HC x n' R → (m : ℤ) + n' = n →
      HC x n (.lam (xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) T)))
/-- The cores of the chains (`q` = variable `0`). -/
inductive HB (x : ℕ) : ℤ → Lambda → Prop
  | q {R : Lambda} : ByqR (x + 1) R → HB x 0 (.app (.var 0) R)
  | m {R : Lambda} : ByqR (x + 1) R → HB x 1 (.app lamM R)
  | rr {R₁ R₂ : Lambda} : ByqR (x + 1) R₁ → ByqR (x + 1) R₂ → HB x 1 (.app R₁ R₂)
  | comp {i' : ℕ} {n : ℤ} {R : Lambda} : HG x i' R → n = (i' : ℤ) + 1 →
      HB x n (.app (Lambda.lift 1 0 R) (.var 0))
  | mw {W : Lambda} : WqT x W → HB x 1 (.app lamM W)
  | ww {W Y : Lambda} : WqT x W → HB x 1 (.app W Y)
end

theorem HB.not_lam {x : ℕ} {n : ℤ} {c : Lambda} (h : HB x n (.lam c)) : False := by
  cases h

theorem HB.ne_var {x : ℕ} {n : ℤ} {P : Lambda} {j : ℕ} (h : HB x n P) : P ≠ .var j := by
  cases h <;> simp

theorem HC.ne_var {x : ℕ} {n : ℤ} {P : Lambda} {j : ℕ} (h : HC x n P) : P ≠ .var j := by
  cases h with
  | base hb => exact hb.ne_var
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

/-! ### Embeddings of the earlier grammars -/

theorem YC.toHC {x n : ℕ} {P : Lambda} (h : YC x n P) : HC x n P :=
  match h with
  | .base hb => by
    cases hb with
    | q hR => exact .base (.q hR)
    | m hR => exact .base (.m hR)
    | rr h1 h2 => exact .base (.rr h1 h2)
    | comp hR => exact .base (.comp (.yg hR) (by push_cast; ring))
  | .bx h' => by push_cast; exact .bx (YC.toHC h')
  | .bx1 h' => by push_cast; exact .bx1 (YC.toHC h')
  | .rq h' hm => .rq (YC.toHC h') (by rw [← hm]; push_cast; ring)

theorem TC.toHC {x : ℕ} {n : ℤ} {P : Lambda} (h : TC (YB x) (x + 1) n P) : HC x n P := by
  induction h with
  | base hb =>
    obtain ⟨k, rfl, hb⟩ := hb
    cases hb with
    | q hR => exact .base (.q hR)
    | m hR => exact .base (.m hR)
    | rr h1 h2 => exact .base (.rr h1 h2)
    | comp hR => exact .base (.comp (.yg hR) (by push_cast; ring))
  | bx _ ih => exact .bx ih
  | bx1 _ ih => exact .bx1 ih
  | rq _ hm ih => exact .rq ih hm

/-- A chain that is an abstraction, applied to a tail, gives a chain under the same binder. -/
theorem HC.beta_lift {x : ℕ} {n' : ℤ} {R c0 T : Lambda} (hR : HC x n' R) (e : R = .lam c0)
    (m : ℕ) :
    HC x ((m : ℤ) + n') (.lam (xPow (.var (x + 2)) m (Lambda.subst T 0 (Lambda.lift 1 1 c0)))) := by
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
    rw [if_neg (by omega), hx, xPow_add]
    exact .rq hR' (by push_cast; omega)

/-- Firing a lifted component on `q`: an abstraction component `R` of index `i'` applied to the
variable `q` gives a chain of height `i' + 1`. -/
theorem HG.fire_q {x i' : ℕ} {c0 : Lambda} (hR : HG x i' (.lam c0)) :
    HC x ((i' : ℤ) + 1) c0 := by
  generalize e : Lambda.lam c0 = t at hR
  cases hR with
  | yg hY =>
    subst e
    cases hY with
    | lam hc => exact_mod_cast hc.toHC
  | st hS =>
    subst e
    generalize e' : Lambda.lam c0 = t at hS
    cases hS with
    | slam hS' =>
      simp only [Lambda.lam.injEq] at e'
      subst e'
      cases hS' with
      | mw hW => exact .base (.mw hW)
      | ww hW => exact .base (.ww hW)
      | core hP => exact hP.toHC
    | sv hV =>
      subst e'
      cases hV with
      | lam hc => exact_mod_cast hc.toHC
    | seta hW =>
      subst e'
      simp only [Lambda.lift] at hW
      cases hW with
      | body hT =>
        have := hT.fire rfl (.var 0)
        rw [subst_var_lift_succ c0 0] at this
        exact this.toHC
    | sbm _ => cases e'
    | sbm1 _ => cases e'
    | sbm2 _ => cases e'
  | byApp _ _ => cases e
  | lam hc hn =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [← hn]; exact hc

/-- The η-contractum of a component `λq. c` is a component of the same index. -/
theorem HC.eta_inv {x i : ℕ} {n : ℤ} {c f : Lambda} (h : HC x n c) (hn : n = (i : ℤ) + 1)
    (hf : c = .app (Lambda.lift 1 0 f) (.var 0)) : HG x i f := by
  subst hf
  generalize e : Lambda.app (Lambda.lift 1 0 f) (.var 0) = t at h
  cases h with
  | base hb =>
    cases hb with
    | q hR => simp only [Lambda.app.injEq] at e; exact (hR.ne_var e.2.symm).elim
    | m hR => simp only [Lambda.app.injEq] at e; exact (hR.ne_var e.2.symm).elim
    | rr _ hR => simp only [Lambda.app.injEq] at e; exact (hR.ne_var e.2.symm).elim
    | @comp i' _ R hR hn' =>
      simp only [Lambda.app.injEq] at e
      rw [Lambda.lift_one_injective 0 e.1]
      have : i' = i := by omega
      subst this; exact hR
    | mw hW => simp only [Lambda.app.injEq] at e; exact (hW.ne_var e.2.symm).elim
    | ww hW =>
      simp only [Lambda.app.injEq] at e
      obtain ⟨rfl, -⟩ := e
      have : i = 0 := by omega
      subst this
      exact .st (.seta hW)
  | bx hP => simp only [Lambda.app.injEq] at e; exact (hP.ne_var e.2.symm).elim
  | bx1 hP => simp only [Lambda.app.injEq] at e; exact (hP.ne_var e.2.symm).elim
  | rq _ _ => cases e

mutual
theorem HG.step {x i : ℕ} {P P' : Lambda} (h : HG x i P) (hs : betaEtaStep P P') : HG x i P' := by
  match h with
  | .yg hY => exact .yg (hY.step hs)
  | .st hS => exact .st (hS.step hs)
  | .byApp hR hP =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hR with
      | bb => simp [bbx] at hc
      | bpre => simp [bbpre] at hc
      | l1 =>
        simp only [byl1, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ P : Lambda, Lambda.subst P 0
            (.lam (.app (.app lamB (.var (x + 2))) (.app (.var 1) (.var 0)))) =
            .lam (.app (.app lamB (.var (x + 1))) (.app (Lambda.lift 1 0 P) (.var 0))) := by
          intro P; simp [Lambda.subst, lamB]
        rw [e]; exact .lam (.bx (.base (.comp hP rfl))) (by push_cast; ring)
      | l2 =>
        simp only [byl2, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ P : Lambda, Lambda.subst P 0
            (.lam (.app (bxPre (x + 2)) (.app (.var 1) (.var 0)))) =
            .lam (.app (bxPre (x + 1)) (.app (Lambda.lift 1 0 P) (.var 0))) := by
          intro P; simp [Lambda.subst, bxPre]
        rw [e]; exact .lam (.bx1 (.base (.comp hP rfl))) (by push_cast; ring)
      | l3 =>
        simp only [byl3, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ P : Lambda, Lambda.subst P 0
            (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) =
            .lam (.lam (xPow (.var (x + 2)) 1
              (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 P) (.var 0))) (.var 0)))) := by
          intro P
          simp [Lambda.subst, xPow, Lambda.lift, lift_lift_zero_one]
        rw [e]; exact .lam (.rq (m := 1) (.base (.comp hP rfl)) rfl) (by push_cast; ring)
    · exact .byApp (hR.step hf) hP
    · exact .byApp hR (HG.step hP ha)
  | .lam hc hn =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .lam (HC.step hc hb) hn
    · exact HC.eta_inv hc hn hf
theorem HC.step {x : ℕ} {n : ℤ} {P P' : Lambda} (h : HC x n P) (hs : betaEtaStep P P') :
    HC x n P' := by
  match h with
  | .base hb => exact HB.step hb hs
  | .bx h =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bx1 h
      · exact (nf_lamB _ hf').elim
      · exact (betaEtaStep_var ha).elim
    · exact .bx (HC.step h ha)
  | .bx1 h =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bxPre, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ P : Lambda, Lambda.subst P 0
          (.lam (.app (.var (x + 1 + 2)) (.app (.var 1) (.var 0)))) =
          .lam (xPow (.var (x + 2)) 1 (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst, xPow]
      rw [e]; exact HC.rq (m := 1) h (by push_cast; ring)
    · exact (nf_bxPre _ _ hf).elim
    · exact .bx1 (HC.step h ha)
  | @HC.rq _ i₀ i' m R T h hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        have := HC.beta_lift (T := T) h rfl m
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (HC.step h hR') hm
      · exact .rq h hm
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by push_cast at hm; omega
      subst e
      exact h
theorem HB.step {x : ℕ} {n : ℤ} {P P' : Lambda} (h : HB x n P) (hs : betaEtaStep P P') :
    HC x n P' := by
  match h with
  | .q hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · exact (betaEtaStep_var hf).elim
    · exact .base (.q (hR.step ha))
  | .m hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, if_pos]
      exact .base (.rr hR hR)
    · exact (nf_lamM _ hf).elim
    · exact .base (.m (hR.step ha))
  | .rr h1 h2 =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases h1 with
      | bb => simp [bbx] at hc
      | bpre => simp [bbpre] at hc
      | l1 => simp at hc
      | l2 => simp at hc
      | l3 => simp at hc
      | m1 =>
        simp only [bym1, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ R : Lambda, Lambda.subst R 0
            (.app (.app lamB (.var (x + 1 + 1))) (.app (.var 1) (.var 0))) =
            .app (.app lamB (.var (x + 1))) (.app (.var 0) R) := by
          intro R; simp [Lambda.subst, lamB]
        rw [e]; exact .bx (.base (.q h2))
      | m2 =>
        simp only [bym2, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ R : Lambda, Lambda.subst R 0
            (.app (bxPre (x + 1 + 1)) (.app (.var 1) (.var 0))) =
            .app (bxPre (x + 1)) (.app (.var 0) R) := by
          intro R; simp [Lambda.subst, bxPre]
        rw [e]; exact .bx1 (.base (.q h2))
      | m3 =>
        simp only [bym3, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ R : Lambda, Lambda.subst R 0
            (.lam (.app (.var (x + 1 + 2)) (.app (.app (.var 2) (.var 1)) (.var 0)))) =
            .lam (xPow (.var (x + 2)) 1 (.app (Lambda.lift 1 0 (.app (.var 0) R)) (.var 0))) := by
          intro R; simp [Lambda.subst, xPow, Lambda.lift]
        rw [e]; exact HC.rq (m := 1) (.base (.q h2)) (by norm_num)
    · exact .base (.rr (h1.step hf) h2)
    · exact .base (.rr h1 (h2.step ha))
  | .comp hR hn =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
    · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
      rw [Lambda.subst_var_lift_succ c0 0, hn]
      exact hR.fire_q
    · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
      exact .base (.comp (HG.step hR hR') hn)
    · exact (betaEtaStep_var ha).elim
  | .mw hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, if_pos]
      exact .base (.ww hW)
    · exact (nf_lamM _ hf).elim
    · exact .base (.mw (hW.step ha))
  | @HB.ww _ W Y hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hW with
      | ap _ => cases hc
      | body hq => exact (hq.fire hc Y).toHC
    · exact .base (.ww (hW.step hf))
    · exact .base (.ww hW)
end

theorem HG.reduces {x i : ℕ} {P Q : Lambda} (h : HG x i P) (hr : betaEtaReduces P Q) :
    HG x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **The components `uⁿ s` are in the grammar at index `n`.** -/
theorem HG.of_h5A (x : ℕ) : ∀ n : ℕ, HG x n (toLam (h5A x n))
  | 0 => .st (ST.of_h5s x)
  | n + 1 => .byApp .bb (HG.of_h5A x n)

/-- Every βη-reduct of `uⁿ s` is in the grammar at index `n`. -/
theorem HG.of_reduces {x n : ℕ} {P : Lambda} (hr : betaEtaReduces (toLam (h5A x n)) P) :
    HG x n P :=
  (HG.of_h5A x n).reduces hr

end TLCA4
