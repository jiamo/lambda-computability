/-
**Poll's Lemma 10, repaired with what is proved** (tasks `M29-EP-IMPREDICATIVE`,
`M29-EP-CUBE-REST`, round 6, route C2).

Poll's Lemma 10 (substitution for the canonical judgement `⊢nf`) fails at its abstraction case:
from the induction hypothesis `Γ, Δσ ⊢nf Π Cσ. Bσ↑ : s` it must pass to
`Γ, Δσ ⊢nf Π nf(Cσ). nf(Bσ↑) : s`.  That step is a canonicalisation of a sort-typed *product*
judgement.  This module states the step as a property of a specification and proves that, with
everything now available (strong normalisation of every corner, hereditary substitution into
product premises gives expansion postponement), the repaired step is **equivalent** to
`HSubstPi` in every corner of the cube:

* `PureTypeSystem.PollProductCanon P` — the missing step: a full-system judgement
  `Γ ⊢ Π C E : s`, read in a canonically valid reduct `Γ'` of `Γ`, has a canonical derivation of
  `Π C' E' : s` for reducts `C'`, `E'`;
* `PureTypeSystem.hsubstPi_of_pollProductCanon` — the repaired step gives `HSubstPi` (in any
  specification over the cube's sorts);
* `PureTypeSystem.pollProductCanon_of_hsubstPi` — conversely, in every corner, `HSubstPi` gives the
  repaired step (through expansion postponement and the normalisation of reduction-only
  derivations);
* `PureTypeSystem.pollProductCanon_iff_hsubstPi` — the equivalence;
* `PureTypeSystem.cube_expansionPostponement_of_pollProductCanon` — expansion postponement from the
  repaired step.

So the gap in Lemma 10 is not repairable by the results proved so far without proving the open
statement itself: the repair of Lemma 10 *is* `HSubstPi`.
-/

import Start.PTSExpansionMeasures

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- **The missing step of Poll's Lemma 10**: canonicalisation of sort-typed product judgements,
read in a canonically valid reduct of the context. -/
def PollProductCanon (P : Specification Srt) : Prop :=
  ∀ {Γ Γ' : List (Expr Srt)} {C E : Expr Srt} {s : Srt},
    HasType P Γ (.pi C E) (.sort s) → List.Forall₂ Reduces Γ Γ' → ValidContextNW P Γ' →
    ∃ C' E', Reduces C C' ∧ Reduces E E' ∧ HasTypeNW P Γ' (.pi C' E') (.sort s)

/-- The entries of a canonically valid context are normal. -/
theorem ValidContextNW.normal_entries {P : Specification Srt} {Γ : List (Expr Srt)}
    (h : ValidContextNW P Γ) : ∀ X ∈ Γ, Normal X := by
  induction h with
  | nil => simp
  | cons _ hA ih =>
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hA.normal.1
      · exact ih X hX

/-- The context of a substitution at depth reduces to any `CtxSubstRed` target. -/
theorem CtxSubstRed.forall₂_append {N : Expr Srt} {Δ Δ' : List (Expr Srt)}
    (h : CtxSubstRed N Δ Δ') (Γ : List (Expr Srt)) :
    List.Forall₂ Reduces (ctxSubstAt N Δ ++ Γ) (Δ' ++ Γ) := by
  induction h with
  | nil =>
      simp only [ctxSubstAt, List.nil_append]
      induction Γ with
      | nil => exact .nil
      | cons X Γ ih => exact .cons .refl ih
  | cons _ hr ih => exact .cons hr ih

/-- **The repaired step gives hereditary substitution into product premises.** -/
theorem hsubstPi_of_pollProductCanon {P : Specification Srt} (h : PollProductCanon P) :
    HSubstPi P := by
  intro Γ N A Δ Δ' C E s hN hc hv hP
  have hT := HasType.subst_at (Δ := Δ) hN.toHasType hP.toHasType
  simp only [Expr.subst] at hT
  obtain ⟨C', E', h1, h2, h3⟩ := h hT (hc.forall₂_append Γ) hv
  refine ⟨C', E', h1, ?_, h3⟩
  first | exact h2 | (rw [Expr.substAt_succ]; exact h2)

/-- **Conversely, in every corner, `HSubstPi` gives the repaired step.** -/
theorem pollProductCanon_of_hsubstPi (f : CubeFeatures) (hpi : HSubstPi (cubeSpec f)) :
    PollProductCanon (cubeSpec f) := by
  intro Γ Γ' C E s hT hc hv
  obtain ⟨B, hB, hR⟩ := (cube_expansionPostponement_of_hsubstPi f hpi).2 _ _ _ hT
  rw [Reduces.sort_eq hB] at hR
  obtain ⟨Γ'', M', T', hc', hM, hT', hNW⟩ :=
    hR.normalizeNW_of_hsubst f (hsubstNW_of_hsubstPi f hpi)
  rw [Reduces.sort_eq hT'] at hNW
  obtain rfl := forall₂_reduces_unique hc' hc hNW.normal.2.2 hv.normal_entries
  obtain ⟨C', E', rfl, hC, hE⟩ := Reduces.pi_inv hM
  exact ⟨C', E', hC, hE, hNW⟩

/-- **The repair of Poll's Lemma 10 is the open lemma**: in every corner of the cube, the missing
step of Lemma 10 is equivalent to hereditary substitution into product premises. -/
theorem pollProductCanon_iff_hsubstPi (f : CubeFeatures) :
    PollProductCanon (cubeSpec f) ↔ HSubstPi (cubeSpec f) :=
  ⟨hsubstPi_of_pollProductCanon, pollProductCanon_of_hsubstPi f⟩

/-- Expansion postponement in every corner from the repaired step of Lemma 10. -/
theorem cube_expansionPostponement_of_pollProductCanon (f : CubeFeatures)
    (h : PollProductCanon (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f) :=
  cube_expansionPostponement_of_hsubstPi f (hsubstPi_of_pollProductCanon h)

end PureTypeSystem
