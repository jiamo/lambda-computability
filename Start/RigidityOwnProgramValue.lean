import Start.RigidityUniformTableSimulation
import Start.RigidityBoundedAutomorphismOutput
import Start.RigidityGenericIdentity
import Start.RigidityConstructibleGroundReals

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Representation/OwnProgramValue.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory PersistentRestrictions SetDegreeDecoding
open GenericIdentity TableIndices IndexMatrix

def OwnProgramAt (E f : ZFSet.{0}) (p : OracleCode) (R A : Oracle) : Prop :=
  Total p R A ∧
    ∃ u ∈ degreeUniverse (groundReals E), ∃ v ∈ degreeUniverse (groundReals E),
      realCode A ∈ u ∧ realCode (value p R A) ∈ v ∧ ZFSet.pair u v ∈ f

theorem own_program_of_table (d : ℕ) :
    ∃ p : OracleCode, ∀ (E f : ZFSet.{0}) (R A : Oracle),
      (∃ X : Oracle, Represents (join A R) (machine d) X ∧
        ∃ u ∈ degreeUniverse (groundReals E), ∃ v ∈ degreeUniverse (groundReals E),
          realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f) → OwnProgramAt E f p R A := by
  obtain ⟨p,hp⟩ := UniformPrograms.table_program d
  refine ⟨p,fun E f R A ⟨X,hX,hrel⟩ => ?_⟩
  have he := hp (join A R) X hX
  refine ⟨⟨X,he⟩,?_⟩
  have hv : value p R A = X := programOutput_eq p (join A R) X he
  rwa [hv]

theorem graph_pair_action (I : CountableIdeal) (σ : I ≃o I) (A B : Oracle)
    (u v : ZFSet.{0}) (hAu : realCode A ∈ u) (hBv : realCode B ∈ v)
    (hpair : ZFSet.pair u v ∈ automorphismSet σ) :
    ∃ hA : degree A ∈ I.carrier, degree B = (σ ⟨degree A,hA⟩).val := by
  obtain ⟨a,he⟩ := (mem_automorphismSet σ _).mp hpair
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  have ha : degree A = a.val := (real_mem_degreeSet A a.val).mp hAu
  have hA : degree A ∈ I.carrier := ha.symm ▸ a.property
  have he' : (⟨degree A,hA⟩ : I) = a := Subtype.ext ha
  exact ⟨hA,by rw [he']; exact (real_mem_degreeSet B _).mp hBv⟩

theorem OwnProgramAt.action (E : ZFSet.{0}) (I : CountableIdeal) (σ : I ≃o I)
    (p : OracleCode) (R A : Oracle) (h : OwnProgramAt E (automorphismSet σ) p R A) :
    ∃ hA : degree A ∈ I.carrier, degree (value p R A) = (σ ⟨degree A,hA⟩).val := by
  obtain ⟨u,_,v,_,hAu,hBv,hpair⟩ := h.2
  exact graph_pair_action I σ A (value p R A) u v hAu hBv hpair

theorem OwnProgramAt.prescribed (E : ZFSet.{0}) (I : CountableIdeal) (σ : I ≃o I)
    (π : Degree ≃o Degree) (hσ : RestrictsTo π I σ)
    (p : OracleCode) (R A : Oracle) (h : OwnProgramAt E (automorphismSet σ) p R A) :
    Total p R A ∧ degree (value p R A) = π (degree A) := by
  obtain ⟨hA,hval⟩ := h.action E I σ p R A
  exact ⟨h.1,hval.trans (hσ ⟨degree A,hA⟩).symm⟩

end TuringRigidity.RelativeConstructible

