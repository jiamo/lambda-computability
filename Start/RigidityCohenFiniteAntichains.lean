import Start.RigidityCohenNiceNames

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenFiniteAntichains.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.CohenFiniteAntichains
open Set CohenSymmetry CohenCoordinates CohenChainCondition CohenNiceNames
universe u
variable {ι : Type u}

theorem finite_extension (U V E : Set (Condition ι)) (hVU : V ⊆ U)
    (hEU : E ⊆ U) (hE : Antichain E) (hfin : E.Finite)
    (n : ℕ) (hn : ∀ p ∈ V, (support p).card ≤ n) :
    ∃ F, F.Finite ∧ E ⊆ F ∧ F ⊆ U ∧ Antichain F ∧
      ∀ p ∈ V, ∃ q ∈ F, Compatible p q := by
  classical
  let W := {p ∈ V | ∀ q ∈ E, ¬ Compatible p q}
  obtain ⟨B,hBW,hB,_,hpred⟩ := countable_predense_antichain W
  have hBfin : B.Finite := bounded_antichain_finite n B hB
    (fun p hp => hn p (hBW hp).1)
  refine ⟨E ∪ B,hfin.union hBfin,Set.subset_union_left,
    Set.union_subset hEU (fun p hp => hVU (hBW hp).1),?_,?_⟩
  · intro p hp q hq hpq
    rcases hp with hp|hp <;> rcases hq with hq|hq
    · exact hE hp hq hpq
    · exact fun hc => (hBW hq).2 p hp (compatible_symm hc)
    · exact (hBW hp).2 q hq
    · exact hB hp hq hpq
  · intro p hp
    by_cases he : ∃ q ∈ E, Compatible p q
    · obtain ⟨q,hq,hpq⟩ := he; exact ⟨q,Or.inl hq,hpq⟩
    · obtain ⟨q,hq,hpq⟩ := hpred p ⟨hp,fun q hq hc => he ⟨q,hq,hc⟩⟩
      exact ⟨q,Or.inr hq,hpq⟩

end TuringRigidity.CohenFiniteAntichains

