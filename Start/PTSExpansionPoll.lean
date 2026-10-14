/-
**Poll's theorem (expansion postponement for normalizing PTSs): a reduction to one lemma.**

Poll's theorem is *not* proved here.  This module isolates what remains.

* `ProductNormalizationR P`: if `Γ ⊢R Π A B : s` and `B` reduces to a normal form `B'`, then
  `Γ ⊢R Π A B' : s`.  It is a special case of `SortedSubjectReductionR P`.
* `productNormalizationR_of_expansionPostponement`: expansion postponement implies it, for every
  specification.
* `expansionPostponement_of_productNormalizationR`: for weakly normalizing specifications it
  implies expansion postponement.  So, for weakly normalizing `P`,
  `expansionPostponement_iff_productNormalizationR`.

This is the reduction that route (a) of the M29 instruction (Poll's system `⊢nf` with the relaxed
abstraction rule) arrives at: with the relaxed rule, `⊢ ⊆ ⊢nf` is immediate, and the abstraction
case of the bridge `⊢nf ⊆ ⊢R` is exactly an instance of `ProductNormalizationR`.  See
`docs/goal/evidence/M29-EP.md`.
-/

import Start.PTSExpansion
import Start.PTSLambdaPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-- Normalizing the codomain of a sort-typed product preserves the reduction-only judgement. -/
def ProductNormalizationR {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ A B B' s, HasTypeR P Γ (.pi A B) (.sort s) → Reduces B B' → Normal B' →
    HasTypeR P Γ (.pi A B') (.sort s)

/-- Expansion postponement implies product normalization, for every specification. -/
theorem productNormalizationR_of_expansionPostponement {S : Type u} {P : Specification S}
    (h : ExpansionPostponement P) : ProductNormalizationR P :=
  fun _ _ _ _ _ hP hr _ =>
    ((expansionPostponement_iff_sortedSubjectReductionR P).1 h).reduces hP (Reduces.pi .refl hr)

/-- For weakly normalizing specifications, product normalization implies expansion
postponement. -/
theorem expansionPostponement_of_productNormalizationR {S : Type u} {P : Specification S}
    (hw : SystemWeaklyNormalizing P) (hpn : ProductNormalizationR P) :
    ExpansionPostponement P := by
  intro Γ M A h
  induction h with
  | ax h => exact ⟨_, .refl, .ax h⟩
  | var _ ih =>
      obtain ⟨B, hB, hA⟩ := ih
      rw [HasTypeR.sort_reduces hB] at hA
      exact ⟨_, .refl, .var hA⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨B', hB', hM⟩ := ihM
      obtain ⟨T, hT, hA⟩ := ihA
      rw [HasTypeR.sort_reduces hT] at hA
      exact ⟨_, Reduces.rename hB' Nat.succ, .weaken hM hA⟩
  | product _ _ hr ihA ihB =>
      obtain ⟨T₁, hT₁, hA⟩ := ihA
      obtain ⟨T₂, hT₂, hB⟩ := ihB
      rw [HasTypeR.sort_reduces hT₁] at hA
      rw [HasTypeR.sort_reduces hT₂] at hB
      exact ⟨_, .refl, .product hA hB hr⟩
  | @abstraction Γ A b B s hb _ ihb ihP =>
      obtain ⟨B', hB', hbR⟩ := ihb
      obtain ⟨T, hT, hP⟩ := ihP
      rw [HasTypeR.sort_reduces hT] at hP
      obtain ⟨N, hBN, hN⟩ := hb.type_weaklyNormalizing hw
      obtain ⟨E, hE₁, hE₂⟩ := Reduces.confluent hB' hBN
      obtain rfl := hN.reduces_eq hE₂
      exact ⟨_, Reduces.pi .refl hBN,
        .abstraction (hbR.reduces hE₁) (hpn Γ A B _ s hP hBN hN)⟩
  | @application Γ f a A B _ _ ihf iha =>
      obtain ⟨D, hD, hf⟩ := ihf
      obtain ⟨A₂, hA₂, ha⟩ := iha
      obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hD
      obtain ⟨E, hE₁, hE₂⟩ := Reduces.confluent hA₁ hA₂
      have hf' := hf.reduces (Reduces.pi hE₁ .refl)
      have ha' := ha.reduces hE₂
      exact ⟨_, Reduces.subst hB₁ (Expr.single a), .application hf' ha'⟩
  | conversion _ _ hc ihM _ =>
      obtain ⟨A', hA', hM⟩ := ihM
      obtain ⟨K, hK₁, hK₂⟩ := hc.join
      obtain ⟨E, hE₁, hE₂⟩ := Reduces.confluent hA' hK₁
      exact ⟨E, hK₂.trans hE₂, hM.reduces hE₁⟩

/-- **Poll's theorem, reduced to one lemma.**  For a weakly normalizing specification, expansion
postponement is equivalent to `ProductNormalizationR`. -/
theorem expansionPostponement_iff_productNormalizationR {S : Type u} {P : Specification S}
    (hw : SystemWeaklyNormalizing P) :
    ExpansionPostponement P ↔ ProductNormalizationR P :=
  ⟨productNormalizationR_of_expansionPostponement,
    expansionPostponement_of_productNormalizationR hw⟩

/-- The strongly normalizing form of the reduction. -/
theorem expansionPostponement_of_productNormalizationR_sn {S : Type u} {P : Specification S}
    (hsn : SystemStronglyNormalizing P) (hpn : ProductNormalizationR P) :
    ExpansionPostponement P :=
  expansionPostponement_of_productNormalizationR
    (fun Γ hΓ M hM => weaklyNormalizing_of_stronglyNormalizing (hsn Γ hΓ M hM)) hpn

end PureTypeSystem
