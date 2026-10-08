import Start.RigidityExtensionSigmaSeparation
import Start.RigidityExtensionPowerSet
import Start.RigiditySourceTheory
import Start.RigiditySetModelFunctionGraphs

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Syntax/WeakExtensionContext.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem extension_context_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (hc : c ∈ M) {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier) :
    SetModelFunctions.Context (genericExtensionSet M c G.carrier) := by
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_pairing M c hM hP hc G.carrier htop,
    extension_union M c o hM hP hU hPow hS.bounded hc hoM ho G,
    extension_powerSet M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG htop,
    (extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG).bounded,
    extension_infinity M c hM hP hU hPow hS.bounded hR hI hc G.carrier htop⟩

end TuringRigidity.BoundedForcing

