import Start.RigidityCohenPrefixOverwrite
import Start.RigidityGenericTotality

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenProgramTotality.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset CohenColumnRealName CohenFiniteFlip FiniteOverwrite GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem column_program_totality_dense (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (p : OracleCode) (R : Oracle)
    (ht : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → Total p R A) :
    _root_.Dense {A | Total p R A} := by
  obtain ⟨A₀,hA₀,_,_⟩ := generic_real_value M K a hM hT hK ha G hG
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨B,hB⟩
  obtain ⟨n,hn⟩ := GenericTopology.cylinder_basis U hU B hB
  let s := FiniteShuffle.initial B n
  obtain ⟨hGs,_,hval⟩ := prefixFilter_properties M K a hM hT hK ha s A₀ G hG hA₀
  refine ⟨overwrite s A₀,hn _ ?_,ht _ hGs _ hval⟩
  intro i hi
  rw [overwrite_below _ _ _ (by simpa [s] using hi),FiniteShuffle.prefix_getD _ _ _ hi]

theorem column_program_generic_totality (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (p : OracleCode) (R : Oracle)
    (ht : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → Total p R A) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
      (∀ A, ShuffleRequirements.GenericFor D A → Total p R A) ∧
      ContinuousOn (value p R) {A | ShuffleRequirements.GenericFor D A} :=
  generic_totality_of_dense p R (column_program_totality_dense M K a hM hT hK ha G hG p R ht)

end TuringRigidity.RelativeConstructible

