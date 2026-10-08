import Start.RigidityPrefixSingletonRealization
import Start.RigidityCohenPrefixOverwrite

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/GroundPrefixOverwrite.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.GroundPrefixOverwrite
open TransitiveNameModel BoundedSetTheory CountableForcing CohenColumnRealName
open FiniteOverwrite
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem overwrite_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) (s : List Bool) :
    AtomicForcing.GroundGeneric M
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter (overwrite s A))) := by
  have ha : natSet 0 ∈ M := hM _ (sourceT_omega_mem M hM hT) _
    ((mem_omega _).mpr ⟨0,rfl⟩)
  have hs := singleton_mem M hM hT.pairing ha
  have hm : natSet 0 ∈ ({natSet 0} : ZFSet.{0}) := ZFSet.mem_singleton.mpr rfl
  obtain ⟨J,hJ,_,hJA⟩ := PrefixSingletonRealization.singleton_realization M (natSet 0) hM hT ha A hA
  obtain ⟨hF,_,hFA⟩ := CohenFiniteFlip.prefixFilter_properties M {natSet 0} (natSet 0)
    hM hT hs hm s A J hJ hJA
  exact selected_real_prefix_generic M {natSet 0} (natSet 0) hM hT hs hm _ hF _ hFA

theorem overwrite_realizes (s : List Bool) (A : Oracle) :
    ShuffleRequirements.Realizes s (overwrite s A) :=
  fun n hn => (overwrite_below s A n hn).symm

end TuringRigidity.GroundPrefixOverwrite

