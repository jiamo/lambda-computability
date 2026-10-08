import Start.RigidityInternalOrderIsoTransport
import Start.RigidityInternalInverseGraph

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/InternalInverseIso.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.InternalInverseIso
open TransitiveNameModel BoundedSetTheory CountableForcing InternalInverseGraph
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem inverse_graph (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p) :
    inverse a b f ∈ M ∧ ∀ p q,
      ZFSet.pair (label b p) (label a q) ∈ inverse a b f ↔ q = e.symm p := by
  refine ⟨inverse_mem M a b f hM hT ha hb hf,?_⟩
  intro p q
  rw [pair_inverse]
  simp only [label_mem,true_and,he]
  constructor
  · intro h
    apply e.injective
    rw [OrderIso.apply_symm_apply]
    exact h.symm
  · intro h
    rw [h,OrderIso.apply_symm_apply]

end TuringRigidity.InternalInverseIso

