import Start.TLCA4YComponents

/-!
# TLCA open problem 4: a grammar for the components of `Q x`
(row M20-TLCA4-Q-NOT-FIXPOINT; series V, big round, run 3, item A1)

The components of `Q x` are the components `Aᵢ[y]` of `T y` at `y = B x`
(`Start/TLCA4QStages.lean`).  This module gives an explicit grammar for them and their reducts,
step (2) of the design for `Q_not_fixedPoint`.  It is `TLCA4.TGram` with every `x`-prefix
`xᵐ (·)` replaced by an `x`-chain of height `m` (the constructors of `TLCA4.XC`), and `BxR`,
`BxqR` replaced by the reducts of `B y`, `B y q` (`ByR`, `ByqR`):

* `YG x i P` — components of index `i`: `B M R`, `(λab. M (a b)) R`, `(λab. a b (a b)) R` with
  `R ∈ ByR`; `R P` with `R ∈ ByR` and `P` of index `i - 1`; and abstractions `λq. C` with `C` a
  chain of height `i + 1`;
* `YC x n C` — chains of height `n` under the binder `q` (`B x C`, `(λab. x (a b)) C`,
  `λd. xᵐ (C d)`) over the cores `YBase`;
* `YBase x n P` — the cores `q R` (height `0`), `M R` and `R₁ R₂` (height `1`) with `R, R₁, R₂`
  reducts of `B y q`, and `R q` with `R` a component of index `i'` (height `i' + 1`).

* **`YG.step`**, `YC.step`, `YBase.step` — the grammar is closed under one βη-step (mutual
  structural induction; no hypothesis on the base is needed);
* `YG.reduces` — and under βη-reduction;
* **`YG.of_tAy`** — the components `Aᵢ[B x]` themselves are in the grammar at index `i`;
* `YG.of_reduces` — so is every βη-reduct of `Aᵢ[B x]`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

mutual
/-- The components of `Q x` (reducts of `Aᵢ[B x]`), `x` at index `x`. -/
inductive YG (x : ℕ) : ℕ → Lambda → Prop
  | bm {R : Lambda} : ByR x R → YG x 0 (.app (.app lamB lamM) R)
  | bm1 {R : Lambda} : ByR x R → YG x 0 (.app bmPre1 R)
  | bm2 {R : Lambda} : ByR x R → YG x 0 (.app bmPre2 R)
  | byApp {i : ℕ} {R P : Lambda} : ByR x R → YG x i P → YG x (i + 1) (.app R P)
  | lam {i : ℕ} {c : Lambda} : YC x (i + 1) c → YG x i (.lam c)
/-- `x`-chains under the binder `q` (so `x` at index `x + 1`) over `YBase`. -/
inductive YC (x : ℕ) : ℕ → Lambda → Prop
  | base {n : ℕ} {P : Lambda} : YBase x n P → YC x n P
  | bx {n : ℕ} {P : Lambda} : YC x n P → YC x (n + 1) (.app (.app lamB (.var (x + 1))) P)
  | bx1 {n : ℕ} {P : Lambda} : YC x n P → YC x (n + 1) (.app (bxPre (x + 1)) P)
  | rq {n n' m : ℕ} {R : Lambda} : YC x n' R → m + n' = n →
      YC x n (.lam (xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) (.var 0))))
/-- The cores of the chains (`q` = variable `0`). -/
inductive YBase (x : ℕ) : ℕ → Lambda → Prop
  | q {R : Lambda} : ByqR (x + 1) R → YBase x 0 (.app (.var 0) R)
  | m {R : Lambda} : ByqR (x + 1) R → YBase x 1 (.app lamM R)
  | rr {R₁ R₂ : Lambda} : ByqR (x + 1) R₁ → ByqR (x + 1) R₂ → YBase x 1 (.app R₁ R₂)
  | comp {i' : ℕ} {R : Lambda} : YG x i' R → YBase x (i' + 1) (.app (Lambda.lift 1 0 R) (.var 0))
end

theorem YC.ne_var {x n j : ℕ} {P : Lambda} (h : YC x n P) : P ≠ .var j := by
  cases h with
  | base hb => cases hb <;> simp
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

theorem YC.lam_xPow {x : ℕ} {n : ℕ} {c : Lambda} (h : YC x n (.lam c)) (m : ℕ) :
    YC x (m + n) (.lam (xPow (.var (x + 2)) m c)) := by
  generalize e : Lambda.lam c = t at h
  cases h with
  | base hb => subst e; cases hb
  | bx _ => cases e
  | bx1 _ => cases e
  | rq hR hm =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [xPow_add]
    exact .rq hR (by omega)

theorem YC.eta_inv {x i : ℕ} {c f : Lambda} (h : YC x (i + 1) c)
    (hf : c = .app (Lambda.lift 1 0 f) (.var 0)) : YG x i f := by
  cases h with
  | base hb =>
    cases hb with
    | m hR =>
      simp only [Lambda.app.injEq] at hf
      exact (hR.ne_var hf.2).elim
    | rr _ h2 =>
      simp only [Lambda.app.injEq] at hf
      exact (h2.ne_var hf.2).elim
    | comp hR =>
      simp only [Lambda.app.injEq] at hf
      rw [← Lambda.lift_one_injective 0 hf.1]
      exact hR
  | bx h =>
    simp only [Lambda.app.injEq] at hf
    exact (h.ne_var hf.2).elim
  | bx1 h =>
    simp only [Lambda.app.injEq] at hf
    exact (h.ne_var hf.2).elim
  | rq _ _ => simp at hf

mutual
theorem YG.step {x i : ℕ} {P P' : Lambda} (h : YG x i P) (hs : betaEtaStep P P') : YG x i P' := by
  match h with
  | .bm hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_M]; exact .bm1 hR
      · exact (nf_lamB _ hf').elim
      · exact (nf_lamM _ ha).elim
    · exact .bm (hR.step ha)
  | .bm1 hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre1, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ R : Lambda, Lambda.subst R 0 (.lam (.app lamM (.app (.var 1) (.var 0)))) =
          .lam (.app lamM (.app (Lambda.lift 1 0 R) (.var 0))) := by
        intro R; simp [Lambda.subst, lamM]
      rw [e]; exact .lam (.base (.m hR.lift))
    · rw [step_bmPre1 hf]; exact .bm2 hR
    · exact .bm1 (hR.step ha)
  | .bm2 hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre2, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ R : Lambda, Lambda.subst R 0
          (.lam (.app (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0)))) =
          .lam (.app (.app (Lambda.lift 1 0 R) (.var 0)) (.app (Lambda.lift 1 0 R) (.var 0))) := by
        intro R; simp [Lambda.subst]
      rw [e]; exact .lam (.base (.rr hR.lift hR.lift))
    · exact (nf_bmPre2 _ hf).elim
    · exact .bm2 (hR.step ha)
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
        rw [e]; exact .lam (.bx (.base (.comp hP)))
      | l2 =>
        simp only [byl2, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ P : Lambda, Lambda.subst P 0
            (.lam (.app (bxPre (x + 2)) (.app (.var 1) (.var 0)))) =
            .lam (.app (bxPre (x + 1)) (.app (Lambda.lift 1 0 P) (.var 0))) := by
          intro P; simp [Lambda.subst, bxPre]
        rw [e]; exact .lam (.bx1 (.base (.comp hP)))
      | l3 =>
        simp only [byl3, Lambda.lam.injEq] at hc
        subst hc
        have e : ∀ P : Lambda, Lambda.subst P 0
            (.lam (.lam (.app (.var (x + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) =
            .lam (.lam (xPow (.var (x + 2)) 1
              (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 P) (.var 0))) (.var 0)))) := by
          intro P
          simp [Lambda.subst, xPow, Lambda.lift, lift_lift_zero_one]
        rw [e]; exact .lam (.rq (m := 1) (.base (.comp hP)) (by omega))
    · exact .byApp (hR.step hf) hP
    · exact .byApp hR (YG.step hP ha)
  | .lam hc =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .lam (YC.step hc hb)
    · exact YC.eta_inv hc hf
theorem YC.step {x n : ℕ} {P P' : Lambda} (h : YC x n P) (hs : betaEtaStep P P') : YC x n P' := by
  match h with
  | .base hb => exact YBase.step hb hs
  | .bx h =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bx1 h
      · exact (nf_lamB _ hf').elim
      · exact (betaEtaStep_var ha).elim
    · exact .bx (YC.step h ha)
  | .bx1 h =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bxPre, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ P : Lambda, Lambda.subst P 0
          (.lam (.app (.var (x + 1 + 2)) (.app (.var 1) (.var 0)))) =
          .lam (xPow (.var (x + 2)) 1 (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst, xPow]
      rw [e]; exact YC.rq (m := 1) h (by omega)
    · exact (nf_bxPre _ _ hf).elim
    · exact .bx1 (YC.step h ha)
  | @YC.rq _ i₀ i' m R h hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        rw [Lambda.subst_var_lift_succ c0 0]
        have := YC.lam_xPow h m
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (YC.step h hR') hm
      · exact (betaEtaStep_var ha).elim
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by omega
      subst e
      exact h
theorem YBase.step {x n : ℕ} {P P' : Lambda} (h : YBase x n P) (hs : betaEtaStep P P') :
    YC x n P' := by
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
        rw [e]; exact YC.rq (m := 1) (.base (.q h2)) (by omega)
    · exact .base (.rr (h1.step hf) h2)
    · exact .base (.rr h1 (h2.step ha))
  | .comp hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
    · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
      rw [Lambda.subst_var_lift_succ c0 0]
      cases hR with
      | lam hc' => exact hc'
    · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
      exact .base (.comp (YG.step hR hR'))
    · exact (betaEtaStep_var ha).elim
end

theorem YG.reduces {x i : ℕ} {P Q : Lambda} (h : YG x i P) (hr : betaEtaReduces P Q) :
    YG x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **The components `Aᵢ[B x]` are in the grammar at index `i`.** -/
theorem YG.of_tAy (x : ℕ) : ∀ i : ℕ, YG x i (toLam (tAy (app B (var x)) i))
  | 0 => .bm .bb
  | i + 1 => .byApp .bb (YG.of_tAy x i)

/-- Every βη-reduct of `Aᵢ[B x]` is in the grammar at index `i`. -/
theorem YG.of_reduces {x i : ℕ} {P : Lambda}
    (hr : betaEtaReduces (toLam (tAy (app B (var x)) i)) P) : YG x i P :=
  (YG.of_tAy x i).reduces hr

end TLCA4
