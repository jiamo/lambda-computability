import Start.RigidityGenericPersistenceDescent
import Start.RigidityPersistentOneRealDefinition

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/GenericDescentDefinition.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ArithmeticTree
universe u

theorem generically_persistent_ground_graph_definition (M N : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hTM : SourceT M)
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (ρ : modelIdeal M hM hTM ≃o modelIdeal M hM hTM)
    (hρN : automorphismSet ρ ∈ N)
    (hgen : SetGenericallyPersistent N (modelIdeal M hM hTM) ρ) :
    automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals M) δ ∧
        automorphismSet ρ = definedSubset (level (groundReals M) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  have hd := generically_persistent_ground_graph_descent M N hM hTM hN hTN hMN ρ hρN hgen
  obtain ⟨t,P,hP,hi,ht,hval⟩ := construction_of_relativeModel M hM hTM _ hd
  obtain ⟨p,hbound,hdef⟩ := t.cofinal_one_real_definition
  obtain ⟨β,_,_,_,hidx,hreal,hset⟩ := hdef M hM hTM P hP ht hi 0 (internal_ordinal_zero M hM hTM)
  exact ⟨hd,heightDomainIndex (OrdinalCoding.paddedCode t.ordinalVector β),
    P,p,hidx,hP,hbound,hreal,hval ▸ hset⟩

end TuringRigidity.RelativeConstructible

