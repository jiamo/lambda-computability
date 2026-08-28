/-
# Reducing full abstraction of `D∞` to a separation principle

`Start/DinfNormalFullAbstraction.lean` proves full abstraction of `D∞` for closed terms that have
a β-normal form, and for the head-divergent terms.  The general statement — Wadsworth's theorem —
is **not** proved in this project.  This file isolates exactly what is missing, by reducing the
general statement to one syntactic principle about separation of *approximants*.

The approximation theorem `ScottDinf.isLUB_ddenot_direct` writes `⟦M⟧ρ` as the least upper bound
of the denotations of the direct approximants `ω(M')` of the reducts `M'` of `M`.  So
`⟦M⟧ρ ≤ ⟦N⟧ρ` follows as soon as `⟦ω(M')⟧ρ ≤ ⟦N⟧ρ` for every reduct.  Suppose that fails for some
`M'`, and suppose one could produce a context `C` with `C[ω(M')]` semantically nontrivial and
`C[N]` head-divergent: since `⟦ω(M')⟧ ≤ ⟦M⟧` pointwise and contexts are monotone in their hole
(`ScottDinf.ddenot_fill_mono`), `C[M]` would then be semantically nontrivial, hence head
normalizing by adequacy, while `C[N]` is not — contradicting observational equivalence.

* `ScottDinf.SeparatesApprox` — the separation principle just described.  It is stated, **not**
  proved; it is the classical hard core of Wadsworth's theorem, and it needs a Böhm-out argument
  for finite approximants with `Ω` which this project does not develop.
* `ScottDinf.ddenot_eq_of_obsEqHnf_of_separatesApprox`,
  `ScottDinf.obsEqHnf_iff_ddenot_eq_of_separatesApprox` — full abstraction of `D∞`, *conditional*
  on that principle.

Nothing here is an axiom: `ScottDinf.SeparatesApprox` is an ordinary proposition and appears as an
explicit hypothesis of the two conditional theorems.
-/

import Start.DinfNormalFullAbstraction

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

noncomputable section

namespace ScottDinf

open Lambda

/-! ## Contexts are monotone in their hole -/

theorem dlamAny_mono {g g' : Dinf → Dinf} (hg : ωScottContinuous g) (hg' : ωScottContinuous g')
    (h : ∀ X, g X ≤ g' X) : dlamAny g ≤ dlamAny g' := by
  rw [dlamAny_eq hg, dlamAny_eq hg']
  exact Psi_mono h

/-- **Monotone compositionality**: a context is monotone in the denotation of the term in its
hole. -/
theorem ddenot_fill_mono {A M : Lambda} (h : ∀ ρ : DEnv, ddenot A ρ ≤ ddenot M ρ) :
    ∀ (C : Ctx) (ρ : DEnv), ddenot (C.fill A) ρ ≤ ddenot (C.fill M) ρ := by
  intro C
  induction C with
  | hole => exact h
  | appL C s ih =>
      intro ρ
      simp only [Ctx.fill, ddenot_app]
      exact Phi_mono (ih ρ) _
  | appR s C ih =>
      intro ρ
      simp only [Ctx.fill, ddenot_app]
      exact (Phi (ddenot s ρ)).monotone (ih ρ)
  | lam C ih =>
      intro ρ
      simp only [Ctx.fill, ddenot_lam]
      exact dlamAny_mono (ddenot_cons_cont _ ρ) (ddenot_cons_cont _ ρ) fun X => ih (dcons X ρ)

theorem ne_botDinf_of_le {x y : Dinf} (hxy : x ≤ y) (hx : x ≠ Dinf.botDinf) :
    y ≠ Dinf.botDinf := by
  intro hy
  exact hx (le_antisymm (hy ▸ hxy) (Dinf.botDinf_le x))

/-! ## The missing separation principle -/

/-- **The separation principle for approximants.**  If a closed finite approximant `A` is not
below a closed term `N` in `D∞`, then some context makes `A` semantically nontrivial while sending
`N` to a head-divergent term.

This proposition is *not proved* in this project: it is the hard core of Wadsworth's full
abstraction theorem, and it requires a Böhm-out argument for finite approximants containing `Ω`,
which is beyond the separation theory developed in `Start/Bohm.lean`, `Start/BohmOut.lean` and
`Start/BohmEta.lean` (those treat β-normal forms).  It appears only as an explicit hypothesis of
the conditional theorems below. -/
def SeparatesApprox : Prop :=
  ∀ (A N : Lambda), Lambda.IsClosed A → Lambda.IsClosed N → ∀ ρ : DEnv,
    ¬ ddenot A ρ ≤ ddenot N ρ →
      ∃ C : Ctx, (∃ σ : DEnv, ddenot (C.fill A) σ ≠ Dinf.botDinf) ∧ ¬ Lambda.HasHnf (C.fill N)

/-! ## Full abstraction, conditionally -/

/-- Given the separation principle, observational equivalence implies the denotational
inequality. -/
theorem ddenot_le_of_obsEqHnf_of_separatesApprox (hsep : SeparatesApprox) {M N : Lambda}
    (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N) (hobs : Lambda.ObsEqHnf M N) (ρ : DEnv) :
    ddenot M ρ ≤ ddenot N ρ := by
  refine (isLUB_ddenot_direct M ρ).2 ?_
  rintro x ⟨M', hM', rfl⟩
  by_contra hcon
  obtain ⟨C, ⟨σ, hσ⟩, hCN⟩ :=
    hsep _ _ (Lambda.IsClosed.direct (hMc.reduces hM')) hNc ρ hcon
  have hle : ∀ τ : DEnv, ddenot (Lambda.direct M') τ ≤ ddenot M τ :=
    fun τ => ddenot_direct_reduct_le hM' τ
  exact hCN ((hobs C).1
    (hasHnf_of_ddenot_ne_botDinf (ne_botDinf_of_le (ddenot_fill_mono hle C σ) hσ)))

/-- **Full abstraction of `D∞`, conditional on `ScottDinf.SeparatesApprox`.** -/
theorem ddenot_eq_of_obsEqHnf_of_separatesApprox (hsep : SeparatesApprox) {M N : Lambda}
    (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N) (hobs : Lambda.ObsEqHnf M N) (ρ : DEnv) :
    ddenot M ρ = ddenot N ρ :=
  le_antisymm (ddenot_le_of_obsEqHnf_of_separatesApprox hsep hMc hNc hobs ρ)
    (ddenot_le_of_obsEqHnf_of_separatesApprox hsep hNc hMc hobs.symm ρ)

/-- **Wadsworth's theorem, conditional on `ScottDinf.SeparatesApprox`**: two closed terms are
observationally equivalent exactly when they have the same denotation in `D∞`. -/
theorem obsEqHnf_iff_ddenot_eq_of_separatesApprox (hsep : SeparatesApprox) {M N : Lambda}
    (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N) :
    Lambda.ObsEqHnf M N ↔ ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ :=
  ⟨fun hobs ρ => ddenot_eq_of_obsEqHnf_of_separatesApprox hsep hMc hNc hobs ρ,
    obsEqHnf_of_ddenot_eq⟩

end ScottDinf

end
