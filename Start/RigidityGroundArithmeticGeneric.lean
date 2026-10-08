import Start.RigidityArithmeticPrefixForcing
import Start.RigidityNumericalCohenSets
import Start.RigidityInternalCohenFilters

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/GroundArithmeticGeneric.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.GroundArithmeticGeneric
open TransitiveNameModel BoundedSetTheory UniformArithmetic ArithmeticPrefixForcing
open InternalCohen CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem ground_arithmetic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M) (G : Oracle)
    (hG : AtomicForcing.GroundGeneric M (pushFilter (realFilter G))) :
    Generic O G := by
  intro D hD hd
  let A := arithmeticReal (fun O n => D O (EncodedForcing.word n)) O
  have hA : realCode A ∈ M := sourceT_arithmetic_comprehension M hM hT hD O hO
  have hspec (s : List Bool) : wordCode s ∈ wordImage A ↔ D O s :=
    wordImage_spec (D O) A (arithmeticReal_true _ O) s
  have hden : Dense {q : Condition | wordCode q.word ∈ wordImage A} := by
    intro q
    obtain ⟨s,hqs,hs⟩ := hd.1 q.word
    exact ⟨⟨s⟩,hqs,(hspec s).mpr hs⟩
  obtain ⟨q,hq,hqD⟩ := (groundGeneric_iff M _).mp hG (wordImage A)
    (wordImage_mem M hM hT A hA) hden
  rw [pull_push] at hq
  exact ⟨q.word,(hspec q.word).mp hqD,hq⟩

end TuringRigidity.GroundArithmeticGeneric

