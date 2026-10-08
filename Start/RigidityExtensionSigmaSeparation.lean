import Start.RigiditySigmaSeparationName

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/ExtensionSigmaSeparation.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem extension_sigmaSeparation (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : SigmaSeparation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    SigmaSeparation (genericExtensionSet M c G.carrier) := by
  classical
  intro φ env henv x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
  have names_exist (i) := (mem_extensionSet M c G.carrier (env i)).mp (henv i)
  choose e he hval using names_exist
  obtain ⟨B,hB,hBS,hBval⟩ := sigma_separation_name M hM hP hU hPow hS hR hI hc hoM ho G hG φ a ha e he
  have hcode : (a.restrict (label c) B).encode (label c) ∈ M := by
    rw [Name.encode_restrict _ _ _ hBS]
    exact hB
  refine ⟨(a.restrict (label c) B).val G.carrier,
    (mem_extensionSet M c G.carrier _).mpr ⟨_,hcode,rfl⟩,?_⟩
  intro z _
  rw [hBval z]
  have hev : (fun i => (e i).val G.carrier) = env := funext hval
  rw [hev]

end TuringRigidity.BoundedForcing

