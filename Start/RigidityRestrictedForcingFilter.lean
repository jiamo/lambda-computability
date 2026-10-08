import Start.RigidityInternalProjectedGeneric

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/RestrictedForcingFilter.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RestrictedForcingFilter
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def inclusion (c q : ZFSet.{0}) (hqc : q ⊆ c) (p : Conditions q) : Conditions c :=
  equivShrink c ⟨label q p,hqc (label_mem q p)⟩

theorem label_inclusion (c q : ZFSet.{0}) (hqc : q ⊆ c) (p : Conditions q) :
    label c (inclusion c q hqc p) = label q p := by simp [inclusion,label]

theorem inclusion_le_iff (c q : ZFSet.{0}) (hqc : q ⊆ c) (p r : Conditions q) :
    inclusion c q hqc p ≤ inclusion c q hqc r ↔ p ≤ r := by
  change label c (inclusion c q hqc r) ⊆ label c (inclusion c q hqc p) ↔ _
  rw [label_inclusion,label_inclusion]; rfl

noncomputable def restrict (c q : ZFSet.{0}) (hqc : q ⊆ c)
    (G : GenericFilter (Conditions c)) (hGq : ∀ p ∈ G.carrier, label c p ∈ q) :
    GenericFilter (Conditions q) where
  carrier := {p | inclusion c q hqc p ∈ G.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    obtain ⟨r,hr⟩ := label_surjective q (hGq p hp)
    have he : inclusion c q hqc r = p := label_injective c ((label_inclusion c q hqc r).trans hr)
    exact ⟨r,(show inclusion c q hqc r ∈ G.carrier from he.symm ▸ hp)⟩
  upper := fun hpr hp => G.upper ((inclusion_le_iff c q hqc _ _).mpr hpr) hp
  directed := by
    intro p r hp hr
    obtain ⟨s,hs,hsp,hsr⟩ := G.directed hp hr
    obtain ⟨t,ht⟩ := label_surjective q (hGq s hs)
    have he : inclusion c q hqc t = s := label_injective c ((label_inclusion c q hqc t).trans ht)
    exact ⟨t,(show inclusion c q hqc t ∈ G.carrier from he.symm ▸ hs),(inclusion_le_iff c q hqc t p).mp (he.symm ▸ hsp),
      (inclusion_le_iff c q hqc t r).mp (he.symm ▸ hsr)⟩

theorem original_condition (c q : ZFSet.{0}) (hqc : q ⊆ c)
    (G : GenericFilter (Conditions c)) (hGq : ∀ p ∈ G.carrier, label c p ∈ q)
    (p : Conditions c) (hp : p ∈ G.carrier) :
    ∃ r ∈ (restrict c q hqc G hGq).carrier, label q r = label c p := by
  obtain ⟨r,hr⟩ := label_surjective q (hGq p hp)
  have he : inclusion c q hqc r = p := label_injective c ((label_inclusion c q hqc r).trans hr)
  exact ⟨r,(show inclusion c q hqc r ∈ G.carrier from he.symm ▸ hp),hr⟩

theorem filterSet_eq (c q : ZFSet.{0}) (hqc : q ⊆ c)
    (G : GenericFilter (Conditions c)) (hGq : ∀ p ∈ G.carrier, label c p ∈ q) :
    genericFilterSet q (restrict c q hqc G hGq).carrier = genericFilterSet c G.carrier := by
  apply ZFSet.ext; intro x
  rw [mem_genericFilterSet,mem_genericFilterSet]
  constructor
  · rintro ⟨p,hp,hx⟩
    exact ⟨inclusion c q hqc p,hp,(label_inclusion c q hqc p).trans hx⟩
  · rintro ⟨p,hp,hx⟩
    obtain ⟨r,hr,he⟩ := original_condition c q hqc G hGq p hp
    exact ⟨r,hr,he.trans hx⟩

end TuringRigidity.RestrictedForcingFilter

