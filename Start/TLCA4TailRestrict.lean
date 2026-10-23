import Start.TLCA4TailW
import Start.TermSize

/-!
# TLCA open problem 4: restricting the base of a chain to its subterms
(row M20-TLCA4-BETAETA; series V, big round, run 9, item A3)

A core family for hit5 has cores `W Y` whose head `W` is itself a two-argument chain over the
same family (`TW`), and Lean rejects that as a nested inductive (the parameters of `TW` would
contain local variables).  The closure of such a family under βη is then proved by strong
induction on the number of nodes of the core, applying `TC.step`/`TW.step` to the base
*restricted to smaller terms*.  This module supplies the two generic facts needed for that:

* `nodes_xPow_le` — `nodes` grows under `x`-prefixes (and is invariant under lifting,
  `Lambda.nodes_lift`);
* `TC.mono`, `TW.mono` — chains are monotone in the base;
* **`TC.restrict`**, **`TW.restrict`** — every base member used in a chain `H` has at most as many
  nodes as `H` (for `TW`, strictly fewer: `W` is never itself a base member).
-/

set_option autoImplicit false

namespace TLCA4

open Lambda (betaEtaReduces betaEtaStep)

theorem nodes_xPow_le (f : Lambda) : ∀ (m : ℕ) (t : Lambda),
    Lambda.nodes t ≤ Lambda.nodes (xPow f m t)
  | 0, _ => le_rfl
  | m + 1, t => by simp only [xPow, Lambda.nodes_app]; have := nodes_xPow_le f m t; omega

theorem TC.mono {base base' : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → base' i P) {i : ℤ} {H : Lambda}
    (h : TC base x i H) : TC base' x i H := by
  induction h with
  | base hP => exact .base (hb hP)
  | bx _ ih => exact .bx ih
  | bx1 _ ih => exact .bx1 ih
  | rq _ hm ih => exact .rq ih hm

/-- **Every base member used in a chain has at most as many nodes as the chain.** -/
theorem TC.restrict {base : ℤ → Lambda → Prop} {x : ℕ} {i : ℤ} {H : Lambda}
    (h : TC base x i H) :
    TC (fun j Q => base j Q ∧ Lambda.nodes Q ≤ Lambda.nodes H) x i H := by
  induction h with
  | base hP => exact .base ⟨hP, le_rfl⟩
  | @bx i P _ ih =>
    refine .bx (ih.mono ?_)
    rintro j Q ⟨hQ, hn⟩
    exact ⟨hQ, by simp only [Lambda.nodes_app]; omega⟩
  | @bx1 i P _ ih =>
    refine .bx1 (ih.mono ?_)
    rintro j Q ⟨hQ, hn⟩
    exact ⟨hQ, by simp only [Lambda.nodes_app]; omega⟩
  | @rq i i' m R T _ hm ih =>
    refine .rq (ih.mono ?_) hm
    rintro j Q ⟨hQ, hn⟩
    refine ⟨hQ, ?_⟩
    have h1 := nodes_xPow_le (.var (x + 1)) m (.app (Lambda.lift 1 0 R) T)
    simp only [Lambda.nodes_lam]
    simp only [Lambda.nodes_app, Lambda.nodes_lift] at h1
    omega

theorem TW.mono {base base' : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → base' i P) {i : ℤ} {W : Lambda}
    (h : TW base x i W) : TW base' x i W := by
  cases h with
  | wB hR => exact .wB (hR.mono hb)
  | wP hR hm => exact .wP (hR.mono hb) hm
  | wK hR => exact .wK (hR.mono hb)

/-- **Every base member used in a two-argument chain has fewer nodes than it.** -/
theorem TW.restrict {base : ℤ → Lambda → Prop} {x : ℕ} {i : ℤ} {W : Lambda}
    (h : TW base x i W) :
    TW (fun j Q => base j Q ∧ Lambda.nodes Q < Lambda.nodes W) x i W := by
  cases h with
  | @wB R hR =>
    refine .wB (hR.restrict.mono ?_)
    rintro j Q ⟨hQ, hn⟩
    exact ⟨hQ, by simp only [Lambda.nodes_app]; omega⟩
  | @wP i' m R T hR hm =>
    refine .wP (hR.restrict.mono ?_) hm
    rintro j Q ⟨hQ, hn⟩
    refine ⟨hQ, ?_⟩
    have h1 := nodes_xPow_le (.var (x + 2)) m
      (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)
    simp only [Lambda.nodes_lam]
    simp only [Lambda.nodes_app, Lambda.nodes_lift] at h1
    omega
  | @wK R hR =>
    refine .wK (hR.restrict.mono ?_)
    rintro j Q ⟨hQ, hn⟩
    exact ⟨hQ, by simp only [Lambda.nodes_lam, Lambda.nodes_lift]; omega⟩

/-- **A chain over a union of bases uses one of them only** (a chain has a single base member). -/
theorem TC.exists_level {F : ℕ → ℤ → Lambda → Prop} {x : ℕ}
    {i : ℤ} {H : Lambda}
    (h : TC (fun j Q => ∃ k, F k j Q) x i H) : ∃ k, TC (F k) x i H := by
  induction h with
  | base hP => obtain ⟨k, hk⟩ := hP; exact ⟨k, .base hk⟩
  | bx _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k, .bx hk⟩
  | bx1 _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k, .bx1 hk⟩
  | rq _ hm ih => obtain ⟨k, hk⟩ := ih; exact ⟨k, .rq hk hm⟩

theorem TW.exists_level {F : ℕ → ℤ → Lambda → Prop} {x : ℕ}
    {i : ℤ} {W : Lambda}
    (h : TW (fun j Q => ∃ k, F k j Q) x i W) : ∃ k, TW (F k) x i W := by
  cases h with
  | wB hR => obtain ⟨k, hk⟩ := hR.exists_level; exact ⟨k, .wB hk⟩
  | wP hR hm => obtain ⟨k, hk⟩ := hR.exists_level; exact ⟨k, .wP hk hm⟩
  | wK hR => obtain ⟨k, hk⟩ := hR.exists_level; exact ⟨k, .wK hk⟩

/-- **`TC.step` with two bases**: a step of a chain over `base` is a chain over a larger `base'`,
given that steps of `base`-members are chains over `base'`. -/
theorem TC.step2 {base base' : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → base' i P)
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base' x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ}
    {P P' : Lambda} (h : TC base x i P) (hs : betaEtaStep P P') : TC base' x i P' := by
  induction h generalizing P' with
  | base hP => exact hs0 hP hs
  | bx h ih =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bx1 (h.mono hb)
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
      rw [e]; exact TC.rq (m := 1) (h.mono hb) (by push_cast; omega)
    · exact (nf_bxPre x _ hf).elim
    · exact .bx1 (ih ha)
  | @rq i₀ i' m R T h hm ih =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        have := TC.beta_lift (T := T) hl h rfl m
        rw [hm] at this
        exact this.mono hb
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (ih hR') hm
      · exact .rq (h.mono hb) hm
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by push_cast at hm; omega
      subst e
      exact h.mono hb

/-- **`TW.step` with two bases.** -/
theorem TW.step2 {base base' : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → base' i P)
    (hs0 : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → TC base' x i P')
    (hl : ∀ {i : ℤ} {c : Lambda}, base i (.lam c) → False) {i : ℤ}
    {W W' : Lambda} (h : TW base x i W) (hs : betaEtaStep W W') : TW base' x i W' := by
  cases h with
  | wB hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamB, Lambda.lam.injEq] at hc
      subst hc
      rw [step_lamB_any]
      exact .wP (m := 0) (hR.mono hb) (by simp)
    · exact (nf_lamB _ hf).elim
    · exact .wB (hR.step2 hb hs0 hl ha)
  | @wK R hR =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hb'
      exact .wK (hR.step2 hb hs0 hl hR')
    · exact (lift_ne_app_var0 R _ hf).elim
  | @wP i' m R T hR hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · rcases betaEtaStep_lam_cases hb' with ⟨b'', hb'', rfl⟩ | ⟨f, hf, rfl⟩
      · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb''
        rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
        · obtain ⟨i'', m', R', T', hR', hm', e⟩ := lift2_beta (T := T) hl hR hc 0
          simp only [xPow, zero_add] at e
          rw [e, xPow_add]
          exact .wP (hR'.mono hb) (by push_cast; omega)
        · obtain ⟨R1, rfl, h1⟩ := betaEtaStep_lift_inv hf
          obtain ⟨R2, rfl, h2⟩ := betaEtaStep_lift_inv h1
          exact .wP (hR.step2 hb hs0 hl h2) hm
        · exact .wP (hR.mono hb) hm
      · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
        rw [← Lambda.lift_one_injective 0 h1]
        have e : i' = i := by push_cast at hm; omega
        subst e
        exact .wK (hR.mono hb)
    · simp at hf

end TLCA4
