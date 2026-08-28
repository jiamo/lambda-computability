/-
# Sharpening the reduction of full abstraction of `D∞`

`Start/DinfWadsworth.lean` reduces Wadsworth's theorem to `ScottDinf.SeparatesApprox`, a principle
which mixes two very different ingredients: a *syntactic* Böhm-out (produce a separating context)
and a *semantic* comparison (recognise when one denotation fails to be below another).  The
syntactic ingredient is now available: `Start/TagFail.lean` proves `Lambda.sepDiv_of_tagFail`, a
Böhm-out that compares an arbitrary term against another arbitrary term along a finite failure
witness `Lambda.TagFail`, and produces closed arguments on which the first term head-converges
while the second head-diverges.

This module feeds that Böhm-out into the reduction.  What is left over is the purely semantic
principle `ScottDinf.TagBelowSound`: *absence* of a finite failure witness implies the
denotational inequality.  No syntax remains in it — the Böhm-out has been discharged.

* `ScottDinf.separatesApprox_ctx_of_sepDiv` — one-sided separation gives a separating context;
* `ScottDinf.sepDiv_of_closed_of_tagFail` — a failure witness for two *closed* terms gives
  one-sided separation, by instantiating the tag bounds of `Lambda.sepDiv_of_tagFail`;
* `ScottDinf.TagBelowSound` — the remaining semantic principle;
* `ScottDinf.separatesApprox_of_tagBelowSound` — it implies `ScottDinf.SeparatesApprox`;
* `ScottDinf.obsEqHnf_iff_ddenot_eq_of_tagBelowSound` — hence full abstraction of `D∞`,
  conditional on it alone;
* `ScottDinf.not_ddenot_le_of_tagFail` — the *converse* of that principle, proved
  unconditionally: a failure witness does refute the `D∞` inequality.  In particular
  `ScottDinf.not_tagFail_self`: no closed term admits a failure witness against itself, so
  `Lambda.TagFail` is not vacuously satisfiable.

Nothing here is an axiom: `ScottDinf.TagBelowSound` is an ordinary proposition and appears as an
explicit hypothesis.
-/

import Start.DinfWadsworth
import Start.TagFail

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ScottDinf

open Lambda

/-! ## From one-sided separation to a separating context -/

/-- A list of closed arguments on which `A` head-converges and `N` head-diverges is a separating
context in the sense required by `ScottDinf.SeparatesApprox`. -/
theorem separatesApprox_ctx_of_sepDiv {A N : Lambda} (h : Lambda.SepDiv A N) :
    ∃ C : Ctx, (∃ σ : DEnv, ddenot (C.fill A) σ ≠ Dinf.botDinf) ∧ ¬ Lambda.HasHnf (C.fill N) := by
  obtain ⟨l, -, hA, hN⟩ := h
  refine ⟨Ctx.appListC Ctx.hole l, ?_, ?_⟩
  · have hfill : (Ctx.appListC Ctx.hole l).fill A = appList A l := Ctx.fill_appListC l Ctx.hole A
    rw [hfill]
    exact exists_ddenot_ne_botDinf_of_hasHnf hA
  · have hfill : (Ctx.appListC Ctx.hole l).fill N = appList N l := Ctx.fill_appListC l Ctx.hole N
    rw [hfill]
    exact hN

/-! ## The Böhm-out for closed terms -/

/-- **Böhm out two closed terms.**  For closed terms the tagged instantiation of
`Lambda.sepDiv_of_tagFail` is the identity, so a failure witness separates them outright. -/
theorem sepDiv_of_closed_of_tagFail {M N : Lambda} (hM : Lambda.IsClosed M)
    (hN : Lambda.IsClosed N) (h : Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) N) :
    Lambda.SepDiv M N := by
  obtain ⟨a, s, hs⟩ := Lambda.sepDiv_of_tagFail h
  have hsep := hs (s + 1) a (le_refl a) (by omega) (fun _ => by omega) (fun _ => by omega)
  simpa only [Lambda.csub, Lambda.substEnv_of_isClosed hM,
    Lambda.substEnv_of_isClosed hN] using hsep

/-! ## The remaining semantic principle -/

/-- **The semantic half of Wadsworth's theorem.**  If the comparison of two closed terms admits no
finite failure witness `Lambda.TagFail`, then the first is below the second in `D∞`.

This is what is left of `ScottDinf.SeparatesApprox` once the Böhm-out of `Start/TagFail.lean` is
taken into account: it mentions no contexts and no separation, only the `D∞` order.  Note that the
hypothesis has to be the *negation* of the inductive relation `Lambda.TagFail` rather than a
positive inductive "below" relation, because `D∞` identifies a term with its infinite
η-expansions, which no inductive relation on finite witnesses can reach. -/
def TagBelowSound : Prop :=
  ∀ (M N : Lambda), Lambda.IsClosed M → Lambda.IsClosed N →
    ¬ Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) N → ∀ ρ : DEnv, ddenot M ρ ≤ ddenot N ρ

/-- The semantic principle implies the separation principle of `Start/DinfWadsworth.lean`. -/
theorem separatesApprox_of_tagBelowSound (h : TagBelowSound) : SeparatesApprox := by
  intro A N hA hN ρ hle
  refine separatesApprox_ctx_of_sepDiv (sepDiv_of_closed_of_tagFail hA hN ?_)
  by_contra hc
  exact hle (h A N hA hN hc ρ)

/-! ## A failure witness really witnesses a semantic failure -/

/-- One-sided separation refutes the denotational inequality: the separating context is
semantically nontrivial on the first term and head-divergent, hence bottom, on the second. -/
theorem not_ddenot_le_of_sepDiv {M N : Lambda} (h : Lambda.SepDiv M N) :
    ¬ ∀ ρ : DEnv, ddenot M ρ ≤ ddenot N ρ := by
  intro hle
  obtain ⟨C, ⟨σ, hσ⟩, hCN⟩ := separatesApprox_ctx_of_sepDiv h
  exact hCN (hasHnf_of_ddenot_ne_botDinf (ne_botDinf_of_le (ddenot_fill_mono hle C σ) hσ))

/-- **The converse of `ScottDinf.TagBelowSound`, unconditionally.**  A finite failure witness for
two closed terms refutes the `D∞` inequality.  So `ScottDinf.TagBelowSound` is exactly the missing
converse implication, and the failure witnesses are never spurious. -/
theorem not_ddenot_le_of_tagFail {M N : Lambda} (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N)
    (h : Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) N) :
    ¬ ∀ ρ : DEnv, ddenot M ρ ≤ ddenot N ρ :=
  not_ddenot_le_of_sepDiv (sepDiv_of_closed_of_tagFail hM hN h)

/-- In particular no closed term admits a failure witness against itself: the relation
`Lambda.TagFail` is not vacuously satisfiable. -/
theorem not_tagFail_self {M : Lambda} (hM : Lambda.IsClosed M) :
    ¬ Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) M :=
  fun h => not_ddenot_le_of_tagFail hM hM h fun _ => le_refl _

/-- Granting the semantic principle, absence of a finite failure witness *characterises* the `D∞`
inequality between closed terms. -/
theorem ddenot_le_iff_not_tagFail (h : TagBelowSound) {M N : Lambda} (hM : Lambda.IsClosed M)
    (hN : Lambda.IsClosed N) :
    (∀ ρ : DEnv, ddenot M ρ ≤ ddenot N ρ) ↔ ¬ Lambda.TagFail 0 (fun _ => 0) M (fun _ => 0) N :=
  ⟨fun hle hf => not_ddenot_le_of_tagFail hM hN hf hle, fun hf => h M N hM hN hf⟩

/-! ## Full abstraction, conditional on the semantic principle alone -/

/-- **Full abstraction of `D∞`, conditional on `ScottDinf.TagBelowSound`.** -/
theorem ddenot_eq_of_obsEqHnf_of_tagBelowSound (h : TagBelowSound) {M N : Lambda}
    (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N) (hobs : Lambda.ObsEqHnf M N) (ρ : DEnv) :
    ddenot M ρ = ddenot N ρ :=
  ddenot_eq_of_obsEqHnf_of_separatesApprox (separatesApprox_of_tagBelowSound h) hMc hNc hobs ρ

/-- **Wadsworth's theorem, conditional on `ScottDinf.TagBelowSound`**: two closed terms are
observationally equivalent exactly when they have the same denotation in `D∞`. -/
theorem obsEqHnf_iff_ddenot_eq_of_tagBelowSound (h : TagBelowSound) {M N : Lambda}
    (hMc : Lambda.IsClosed M) (hNc : Lambda.IsClosed N) :
    Lambda.ObsEqHnf M N ↔ ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ :=
  obsEqHnf_iff_ddenot_eq_of_separatesApprox (separatesApprox_of_tagBelowSound h) hMc hNc

end ScottDinf

end
