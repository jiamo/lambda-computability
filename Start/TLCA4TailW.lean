import Start.TLCA4TailShape

/-!
# TLCA open problem 4: two-argument chains (the reducts of `B C` for a chain `C`)
(row M20-TLCA4-BETAETA; series V, big round, run 9, item A3)

In `hit5`, the tail is updated through `w Z = B B v Z →w B (v Z)`: the term `B (v Z)` takes the
new tail transformer `Y` and then the old tail, `B (v Z) Y ρ →w v Z (Y ρ)`, and `v Z` is a chain.
This module gives, generically over a base family with the closure hypotheses of `TC.step`, the
βη-closed family of the reducts of `B C` for a chain `C` (`TW`):

* `TW.wB` — `B C`; `TW.wP` — `λb c. xᵐ (C' T)` (with `C'` a chain lifted under `b, c`, `T`
  arbitrary; `B C → λbc. C (b c)` is the case `m = 0`); `TW.wK` — `λb. C` (`b` not free);
* **`TW.step`**, `TW.reduces` — the family is closed under βη;
* **`TW.fire`** — applying a member that is an abstraction to *any* `Y` gives a chain of the same
  height (`λb c. xᵐ (C' T)` gives `λc. xᵐ (C' T[Y/b])`, `λb. C` gives `C`).
-/

set_option autoImplicit false

namespace TLCA4

open Lambda (betaEtaReduces betaEtaStep)

/-- `λab. a (b c)` applied to `R`, reduced: `λbc. R (b c)` with `R` lifted twice. -/
def bPre (R : Lambda) : Lambda :=
  .lam (.lam (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) (.app (.var 1) (.var 0))))

theorem step_lamB_any (R : Lambda) :
    Lambda.subst R 0 (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) = bPre R := by
  simp [Lambda.subst, bPre]

/-- The reducts of `B C` for a chain `C` of height `i`. -/
inductive TW (base : ℤ → Lambda → Prop) (x : ℕ) : ℤ → Lambda → Prop
  | wB {i : ℤ} {R : Lambda} : TC base x i R → TW base x i (.app lamB R)
  | wP {i i' : ℤ} {m : ℕ} {R T : Lambda} : TC base x i' R → (m : ℤ) + i' = i →
      TW base x i (.lam (.lam (xPow (.var (x + 2)) m
        (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))))
  | wK {i : ℤ} {R : Lambda} : TC base x i R → TW base x i (.lam (Lambda.lift 1 0 R))

theorem lift_ne_app_var0 (R f : Lambda) :
    Lambda.lift 1 0 R ≠ .app (Lambda.lift 1 0 f) (.var 0) := by
  intro e
  cases R with
  | var n => simp [Lambda.lift] at e
  | lam b => simp [Lambda.lift] at e
  | app g a =>
    simp only [Lambda.lift, Lambda.app.injEq] at e
    obtain ⟨-, e2⟩ := e
    cases a with
    | var n => simp [Lambda.lift] at e2
    | lam b => simp [Lambda.lift] at e2
    | app _ _ => simp [Lambda.lift] at e2

theorem lift2_beta {base : ℤ → Lambda → Prop} {x : ℕ}
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i' : ℤ} {R c T : Lambda}
    (hR : TC base x i' R) (e : Lambda.lift 1 0 (Lambda.lift 1 0 R) = .lam c) (m : ℕ) :
    ∃ (i'' : ℤ) (m' : ℕ) (R' T' : Lambda), TC base x i'' R' ∧ (m' : ℤ) + i'' = i' ∧
      xPow (.var (x + 2)) m (Lambda.subst T 0 c) =
        xPow (.var (x + 2)) (m + m') (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R')) T') := by
  cases hR with
  | base hb =>
    obtain ⟨c1, e1, -⟩ := Lambda.lift_eq_lam e
    obtain ⟨c2, rfl, -⟩ := Lambda.lift_eq_lam e1
    exact (hl hb).elim
  | bx _ => simp [Lambda.lift] at e
  | bx1 _ => simp [Lambda.lift, bxPre] at e
  | @rq _ i'' m' R' T' hR' hm =>
    refine ⟨i'', m', R', Lambda.subst T 0 (Lambda.lift 1 1 (Lambda.lift 1 1 T')), hR', hm, ?_⟩
    have e' : c = Lambda.lift 1 1 (Lambda.lift 1 1
        (xPow (.var (x + 1)) m' (.app (Lambda.lift 1 0 R') T'))) := by
      simp only [Lambda.lift, Lambda.lam.injEq] at e; exact e.symm
    subst e'
    have hv : Lambda.subst T 0 (Lambda.lift 1 1 (Lambda.lift 1 1 (.var (x + 1)))) =
        .var (x + 2) := by simp [Lambda.lift, Lambda.subst]
    have hR2 : Lambda.subst T 0 (Lambda.lift 1 1 (Lambda.lift 1 1 (Lambda.lift 1 0 R'))) =
        Lambda.lift 1 0 (Lambda.lift 1 0 R') := by
      rw [← lift_lift_zero_one R', ← lift_lift_zero_one (Lambda.lift 1 0 R'), Lambda.subst_lift]
    rw [lift_xPow, lift_xPow, subst_xPow, hv, xPow_add]
    simp only [Lambda.lift, Lambda.subst, hR2]

/-- **The reducts of `B C` are closed under one βη-step.** -/
theorem TW.step {base : ℤ → Lambda → Prop} {x : ℕ}
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ}
    {W W' : Lambda} (h : TW base x i W) (hs : betaEtaStep W W') : TW base x i W' := by
  cases h with
  | wB hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamB, Lambda.lam.injEq] at hc
      subst hc
      rw [step_lamB_any]
      exact .wP (m := 0) hR (by simp)
    · exact (nf_lamB _ hf).elim
    · exact .wB (hR.step hs0 hl ha)
  | @wK R hR =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hb
      exact .wK (hR.step hs0 hl hR')
    · exact (lift_ne_app_var0 R _ hf).elim
  | @wP i' m R T hR hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · rcases betaEtaStep_lam_cases hb with ⟨b'', hb', rfl⟩ | ⟨f, hf, rfl⟩
      · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
        rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
        · obtain ⟨i'', m', R', T', hR', hm', e⟩ := lift2_beta (T := T) hl hR hc 0
          simp only [xPow, zero_add] at e
          rw [e, xPow_add]
          exact .wP hR' (by push_cast; omega)
        · obtain ⟨R1, rfl, h1⟩ := betaEtaStep_lift_inv hf
          obtain ⟨R2, rfl, h2⟩ := betaEtaStep_lift_inv h1
          exact .wP (hR.step hs0 hl h2) hm
        · exact .wP hR hm
      · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
        rw [← Lambda.lift_one_injective 0 h1]
        have e : i' = i := by push_cast at hm; omega
        subst e
        exact .wK hR
    · simp at hf

theorem TW.reduces {base : ℤ → Lambda → Prop} {x : ℕ}
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ}
    {W W' : Lambda} (h : TW base x i W) (hr : betaEtaReduces W W') : TW base x i W' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs0 hl hs

theorem subst_lift_lift_one1 (s X : Lambda) :
    Lambda.subst (Lambda.lift 1 0 s) 1 (Lambda.lift 1 0 (Lambda.lift 1 0 X)) = Lambda.lift 1 0 X := by
  rw [lift_lift_zero_one X, Lambda.subst_lift]

/-- **Firing a two-argument chain on any `Y` gives a chain of the same height.** -/
theorem TW.fire {base : ℤ → Lambda → Prop} {x : ℕ} {i : ℤ} {W c : Lambda}
    (h : TW base x i W) (e : W = .lam c) (Y : Lambda) : TC base x i (Lambda.subst Y 0 c) := by
  cases h with
  | wB _ => cases e
  | wK hR =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [Lambda.subst_lift]; exact hR
  | @wP i' m R T hR hm =>
    simp only [Lambda.lam.injEq] at e
    subst e
    simp only [Lambda.subst, subst_xPow, zero_add]
    rw [if_neg (by omega), if_pos (by omega), show x + 2 - 1 = x + 1 by omega,
      subst_lift_lift_one1]
    exact .rq hR hm

end TLCA4
