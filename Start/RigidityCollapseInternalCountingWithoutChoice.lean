import Start.RigidityCollapseCountWithoutChoice

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/CollapseInternalCountingWithoutChoice.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem unionGraph_mem_extension_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {c : ZFSet.{u}} (hcM : c ∈ M) (h0 : (∅ : ZFSet.{u}) ∈ c)
    (G : GenericFilter (Conditions c)) :
    unionGraph G ∈ genericExtensionSet M c G.carrier := by
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have hEU := extension_union M c (orderSet c) hM hP hU hPow hS hcM
    (orderSet_mem_without_choice M hM hP hU hPow hS hcM) (orderSet_pair c) G
  apply union_mem _ (genericExtensionSet_transitive M c hM G.carrier) hEU
  exact genericFilterSet_mem_extension M c hM hP hU hPow hS hR hI hcM G.carrier htop

theorem internal_counting_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    InternallyCountable (genericExtensionSet M c G.carrier) A := by
  have hω := omega_mem M hM hS hI
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hc ∅).mpr ⟨hM _ hω _ ZFSet.omega_zero,prefix_empty A⟩
  exact ⟨unionGraph G,unionGraph_mem_extension_without_choice M hM hP hU hPow hS hR hI hcM h0 G,
    unionGraph_function_without_choice M hM hP hU hS hω hA hcM hc hne G hG,
    unionGraph_onto_without_choice M hM hP hU hS hω hA hcM hc G hG⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

