import Start.TLCA4TGrammar

/-!
# TLCA open problem 4: `x`-chains over an arbitrary base
(row M20-TLCA4-Q-NOT-FIXPOINT; series V, big round, run 2, item A1)

The `x`-level constructors `bx`, `bx1`, `rq` of `TLCA4.TGram` do not depend on the base
components.  `TLCA4.XC base x i P` is the grammar they generate over an arbitrary indexed family
`base` (with `x` free at de Bruijn index `x`):

* `base i P` is a chain of height `i`;
* `B x P` and its reduct `bxPre x P` raise the height by one;
* `λc. xᵐ (P c)` (the β-reduct of `bxPre x P` iterated) has height `m + i'` for `P` of height `i'`.

* **`XC.step`** — if every one-step reduct of a base member is a chain of the same height, and
  every base abstraction `λc. b` of height `i` gives a chain `λc. xᵐ b` of height `m + i`,
  then the chains are closed under one βη-step;
* **`XC.reduces`** — the same for βη-reduction.

This is step (1) of the design for the shape of the reducts of `Q x`: the `x`-prefixes over
the `y`-components (`y = B x`) are such chains.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda (betaEtaReduces betaEtaStep)

/-- `x`-chains over the indexed family `base`. -/
inductive XC (base : ℕ → Lambda → Prop) (x : ℕ) : ℕ → Lambda → Prop
  | base {i : ℕ} {P : Lambda} : base i P → XC base x i P
  | bx {i : ℕ} {P : Lambda} : XC base x i P → XC base x (i + 1) (.app (.app lamB (.var x)) P)
  | bx1 {i : ℕ} {P : Lambda} : XC base x i P → XC base x (i + 1) (.app (bxPre x) P)
  | rq {i i' m : ℕ} {R : Lambda} : XC base x i' R → m + i' = i →
      XC base x i (.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) (.var 0))))

/-- The hypotheses on the base under which chains are closed under βη-steps. -/
structure XCBase (base : ℕ → Lambda → Prop) (x : ℕ) : Prop where
  step : ∀ {i : ℕ} {P P' : Lambda}, base i P → betaEtaStep P P' → XC base x i P'
  lam : ∀ {i m : ℕ} {c : Lambda}, base i (.lam c) →
    XC base x (m + i) (.lam (xPow (.var (x + 1)) m c))

/-- Prefixing the body of a chain abstraction by more `x`'s. -/
theorem XC.lam_xPow {base : ℕ → Lambda → Prop} {x : ℕ} (hb : XCBase base x) :
    ∀ {i : ℕ} {c : Lambda}, XC base x i (.lam c) → ∀ (m : ℕ),
      XC base x (m + i) (.lam (xPow (.var (x + 1)) m c)) := by
  intro i c h m
  generalize e : Lambda.lam c = t at h
  cases h with
  | base hP => subst e; exact hb.lam hP
  | bx _ => cases e
  | bx1 _ => cases e
  | rq hR hm =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [xPow_add]
    exact .rq hR (by omega)

/-- **Chains are closed under one βη-step**, given closure of the base. -/
theorem XC.step {base : ℕ → Lambda → Prop} {x : ℕ} (hb : XCBase base x) {i : ℕ}
    {P P' : Lambda} (h : XC base x i P) (hs : betaEtaStep P P') : XC base x i P' := by
  induction h generalizing P' with
  | base hP => exact hb.step hP hs
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
          .lam (.app (.var (x + 1)) (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst]
      rw [e]; exact XC.rq (m := 1) h (by omega)
    · exact (nf_bxPre x _ hf).elim
    · exact .bx1 (ih ha)
  | @rq i₀ i' m R h hm ih =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        rw [Lambda.subst_var_lift_succ c0 0]
        have := XC.lam_xPow hb h m
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (ih hR') hm
      · exact (betaEtaStep_var ha).elim
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by omega
      subst e
      exact h

/-- **Chains are closed under βη-reduction**, given closure of the base. -/
theorem XC.reduces {base : ℕ → Lambda → Prop} {x : ℕ} (hb : XCBase base x) {i : ℕ}
    {P Q : Lambda} (h : XC base x i P) (hr : betaEtaReduces P Q) : XC base x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hb hs

/-- A base family with no abstractions that is closed under βη-steps satisfies `XCBase`. -/
theorem XCBase.of_closed {base : ℕ → Lambda → Prop} {x : ℕ}
    (hstep : ∀ {i : ℕ} {P P' : Lambda}, base i P → betaEtaStep P P' → base i P')
    (hlam : ∀ {i : ℕ} {c : Lambda}, ¬ base i (.lam c)) : XCBase base x where
  step hP hs := .base (hstep hP hs)
  lam hP := (hlam hP).elim

/-- Chains are monotone in the base. -/
theorem XC.mono {base base' : ℕ → Lambda → Prop} {x : ℕ}
    (hmono : ∀ {i : ℕ} {P : Lambda}, base i P → base' i P) {i : ℕ} {P : Lambda}
    (h : XC base x i P) : XC base' x i P := by
  induction h with
  | base hP => exact .base (hmono hP)
  | bx _ ih => exact .bx ih
  | bx1 _ ih => exact .bx1 ih
  | rq _ hm ih => exact .rq ih hm

/-- Sanity check: the components of `T x` are `x`-chains over the `TGram` family itself
(`TGram` is closed under steps, `TGram.step`, and under `x`-prefixing of abstraction bodies). -/
theorem TGram.xcBase (x : ℕ) : XCBase (TGram x) x where
  step hP hs := .base (hP.step hs)
  lam {_ m _} hP := .base (hP.lam_inv.xPow m).toGram

end TLCA4
