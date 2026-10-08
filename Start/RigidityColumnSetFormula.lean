import Start.RigidityDegreeSetFormula

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/ColumnSetFormula.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
open EncodedForcing
universe u
namespace Formula

def columnBit (o Q n H k : ℕ) : Formula := .existsMem o
  (.conj (naturalPair (o+1) (Q+1) (n+1) (k+1) 0) (.member 0 (H+1)))

theorem columnBit_spec (o Q n H k : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ i, finiteNaturalGraph f i ∈ e Q)
    (A : Oracle) (hA : e H = realCode A) (N K : ℕ) (hn : e n = natSet N) (hk : e k = natSet K) :
    (columnBit o Q n H k).Eval e ↔ columns A N K = true := by
  simp only [columnBit,Formula.Eval,cons_zero,cons_succ]
  constructor
  · rintro ⟨v,_,hp,hm⟩
    have hv : v = natSet (Nat.pair N K) :=
      (naturalPair_spec (o+1) (Q+1) (n+1) (k+1) 0 (cons v e) ho hQ N K hn hk).mp hp
    rw [hv,hA,natSet_mem_realCode] at hm
    exact hm
  · intro h
    refine ⟨natSet (Nat.pair N K),?_,?_,?_⟩
    · rw [ho]; exact (mem_omega _).mpr ⟨Nat.pair N K,rfl⟩
    · exact (naturalPair_spec (o+1) (Q+1) (n+1) (k+1) 0 (cons (natSet (Nat.pair N K)) e)
        ho hQ N K hn hk).mpr rfl
    · rw [hA,natSet_mem_realCode]; exact h

def columnSet (o Q n H B : ℕ) : Formula := .conj (.subset B o)
  (allMem o (iff (.member 0 (B+1)) (columnBit (o+1) (Q+1) (n+1) (H+1) 0)))

theorem columnSet_spec (o Q n H B : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ i, finiteNaturalGraph f i ∈ e Q)
    (A : Oracle) (hA : e H = realCode A) (N : ℕ) (hn : e n = natSet N) :
    (columnSet o Q n H B).Eval e ↔ e B = realCode (columns A N) := by
  simp only [columnSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,cons_zero,cons_succ]
  rw [ho]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro w
    by_cases hw : w ∈ ZFSet.omega.{u}
    · obtain ⟨k,rfl⟩ := (mem_omega w).mp hw
      rw [natSet_mem_realCode]
      exact (h _ ((mem_omega _).mpr ⟨k,rfl⟩)).trans
        (columnBit_spec (o+1) (Q+1) (n+1) (H+1) 0 (cons (natSet k) e) ho hQ A hA N k hn rfl)
    · exact ⟨fun h => False.elim (hw (hsub h)),fun h => False.elim (hw (realCode_subset _ h))⟩
  · intro hb
    refine ⟨hb.symm ▸ realCode_subset (columns A N),?_⟩
    intro w hw
    obtain ⟨k,rfl⟩ := (mem_omega w).mp hw
    rw [hb,natSet_mem_realCode]
    exact (columnBit_spec (o+1) (Q+1) (n+1) (H+1) 0 (cons (natSet k) e) ho hQ A hA N k hn rfl).symm
end Formula

end TuringRigidity.BoundedSetTheory

