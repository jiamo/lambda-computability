import Start.RigidityRelativeOmegaCertificates
import Start.RigidityOrdinalCodeOperations

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/OrdinalCodes/SumCertificates.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

def SumCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  sumDomain a.toZFSet b.toZFSet ∈ M ∧ sumRelation a.toZFSet b.toZFSet ∈ M ∧
    ∃ f ∈ M, OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
      (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f

theorem SumCertificates.context (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : SumCertificates M a b := by
  have h0 := C.transitive _ C.omega_mem _ ZFSet.omega_zero
  obtain ⟨_,f,hf,hc⟩ := ordinal_add_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep h0 a b ha hb
  exact ⟨sumDomain_mem M _ _ C.transitive C.pairing C.union C.power C.separation h0 ha hb,
    sumRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation h0 ha hb,
    f,hf,hc⟩

theorem SumCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : SumCertificates M a b) (hMN : M ⊆ N) : SumCertificates N a b :=
  ⟨hMN h.1,hMN h.2.1,let ⟨f,hf,hc⟩ := h.2.2; ⟨f,hMN hf,hc⟩⟩

theorem sumSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hc : SumCertificates M a b) (hy : e 0 = (a+b).toZFSet) :
    sumSentence.Sat (M : Set ZFSet) e := by
  have h1 : ({∅} : ZFSet.{u}) ∈ M := by
    have h := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  exact (sumSentence_spec_of_certificate M hM e he a b ha hb
    (hM _ hω _ ZFSet.omega_zero) h1 hc.1 hc.2.1 hc.2.2).mpr hy

end TuringRigidity.OrdinalArithmetic

