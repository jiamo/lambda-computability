import Start.RigidityParameterCoveringModels
import Start.RigidityGroundDegreeCollapse

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Constructibility/ParameterPersistentCollapse.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel PersistentRestrictions PersistentPresentation PersistentCountability OracleJump
open CountableForcing ElementaryModel
universe u
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem parameter_persistent_collapse (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{u}, Transitive M ∧ SourceT M ∧ Countable (Conditions M) ∧
      (∀ n, A n ∈ modelReals M) ∧
    ∃ c ∈ M, ∃ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G ∧
      let N := genericExtensionSet M c G.carrier
      M ⊆ N ∧ Transitive N ∧ SourceT N ∧
      ∃ I : CountableIdeal, ∃ H ∈ modelReals N, ∃ hH : Presented I H,
        (∀ a : Degree, a ∈ I.carrier ↔ ∃ X ∈ modelReals M, degree X = a) ∧
        (∀ n, degree (A n) ∈ I.carrier) ∧
        ∃ ρ : I ≃o I, RestrictsTo π I ρ ∧ Persistent I ρ ∧
          graphOracle hH ρ ∈ modelReals N ∧
          ∃ S ∈ N, degreeUniverse S ∈ N ∧ degreeOrder S ∈ N ∧
            presentationGraph S H (graphOracle hH ρ) ∈ N ∧
            (LevySigma.persistent 0 1 2 3 4).Realize N
              (modelDegreeEnv S (presentationSet S H) (presentationGraph S H (graphOracle hH ρ))) := by
  obtain ⟨X,hX⟩ := degree_surjective (π (degree (jump FixedArithmetic.zero)))
  obtain ⟨Y,hY⟩ := degree_surjective (π.symm (degree (jump FixedArithmetic.zero)))
  let B : ℕ → Oracle | 0 => X | 1 => Y | n+2 => A n
  obtain ⟨M,hM,hT,hcount,hB⟩ := parameter_covering_models.{u} B
  let : Countable (Conditions M) := hcount
  obtain ⟨c,hc,G,hG,hMN,hN,hTN,I,H,hHN,hH,hI,ρ,hρ,hp,hRN,S,hSN,hU,hO,hgraph⟩ :=
    ground_degree_persistent_collapse M hM hT π X Y (hB 0) (hB 1) hX hY
  refine ⟨M,hM,hT,hcount,(fun n => hB (n+2)),c,hc,G,hG,hMN,hN,hTN,
    I,H,hHN,hH,hI,?_,ρ,hρ,hp,hRN,S,hSN,hU,hO,hgraph⟩
  intro n
  exact (hI _).mpr ⟨A n,hB (n+2),rfl⟩

end TuringRigidity.BoundedSetTheory

