import Start.RigidityCountedRealsPresentation
import Start.RigidityWeakExtensionContext
import Start.RigidityCollapseInternalCountingWithoutChoice

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/RealCollapseReconstruction.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing AtomicForcing SetDegreeDecoding
open PersistentRestrictions
universe u
attribute [local instance] order collapsePreorder

theorem real_collapse_reconstructs (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {R c : ZFSet.{u}} (hRM : R ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix R p) (hne : ∃ x, x ∈ R)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
    (I : CountableIdeal)
    (hIR : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    automorphismSet ρ ∈ genericExtensionSet M c G.carrier := by
  have hω := omega_mem M hM hS.bounded hI
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hc ∅).mpr ⟨hM _ hω _ ZFSet.omega_zero,prefix_empty R⟩
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have ho := orderSet_mem_without_choice M hM hP hU hPow hS.bounded hcM
  have C := BoundedForcing.extension_context_without_choice M hM hP hU hPow hS hR hI
    hcM ho (orderSet_pair c) G hG htop
  have hME := ground_inclusion_set M c hM hP hU hPow hS.bounded hR hI hcM G.carrier htop
  have hcount := internal_counting_without_choice M hM hP hU hPow hS.bounded hR hI
    hRM hcM hc hne G hG
  exact SetModelCountability.persistent_mem_of_counted_reals C (hME hRM) hreal hcount I hIR ρ hρ hz

end TuringRigidity.BoundedSetTheory.InternalCollapse

