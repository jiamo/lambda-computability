import Start.RigidityConstructibleSatisfaction
import Start.RigidityConstructibleStages

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Constructibility/ConstructibleSuccessorCode.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem tupleEnv_cons {n : ℕ} (x : ZFSet.{u}) (v : Fin n → ZFSet.{u}) :
    tupleEnv (Fin.cases x v) = cons x (tupleEnv v) := by
  funext i
  cases i with
  | zero => simp [tupleEnv,cons]
  | succ i =>
    by_cases hi : i < n
    · simp only [tupleEnv,cons_succ,Nat.succ_lt_succ_iff,hi,dif_pos]
      rfl
    · simp [tupleEnv,cons_succ,hi]

theorem definedSubset_record (A x : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n+1) :
    x ∈ definedSubset A p v ↔ x ∈ A ∧
      ZFSet.pair (natSet (Encodable.encode p)) (tupleCode (Fin.cases x v)) ∈ satisfactionSet A := by
  rw [mem_definedSubset]
  apply and_congr_right; intro hx
  rw [satisfactionSet_spec A p _ (fun i => Fin.cases hx hv i) hb,tupleEnv_cons]

theorem definablePower_records (A S : ZFSet.{u}) :
    S ∈ definablePower A ↔
      ∃ (n : ℕ) (p : SentenceForm) (v : Fin n → ZFSet.{u}),
        p.bound ≤ n+1 ∧ (∀ i, v i ∈ A) ∧ ∀ x,
          (x ∈ S ↔ x ∈ A ∧ ZFSet.pair (natSet (Encodable.encode p))
            (tupleCode (Fin.cases x v)) ∈ satisfactionSet A) := by
  rw [mem_definablePower]
  constructor
  · rintro ⟨n,p,v,hb,hv,rfl⟩
    exact ⟨n,p,v,hb,hv,fun x => definedSubset_record A x p v hv hb⟩
  · rintro ⟨n,p,v,hb,hv,hS⟩
    refine ⟨n,p,v,hb,hv,?_⟩
    apply ZFSet.ext; intro x
    exact (hS x).trans (definedSubset_record A x p v hv hb).symm

theorem level_succ_records (R S : ZFSet.{u}) (o : Ordinal.{u}) :
    S ∈ level R (o+1) ↔
      ∃ (n : ℕ) (p : SentenceForm) (v : Fin n → ZFSet.{u}),
        p.bound ≤ n+1 ∧ (∀ i, v i ∈ level R o) ∧ ∀ x,
          (x ∈ S ↔ x ∈ level R o ∧ ZFSet.pair (natSet (Encodable.encode p))
            (tupleCode (Fin.cases x v)) ∈ satisfactionSet (level R o)) := by
  rw [level_succ,definablePower_records]

end TuringRigidity.RelativeConstructible

