import Start.RigidityModelDegreeCodes

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/DegreeSetFormula.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
universe u

def DegreeEqualityFormula (φ : Formula) : Prop := ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ degree A = degree B)

namespace Formula
def degreeSet (φ : Formula) (o Q z R A D : ℕ) : Formula :=
  .conj (.subset D R) (allMem R (iff (.member 0 (D+1)) (twoOracles φ (o+1) (Q+1) (z+1) 0 (A+1))))

theorem degreeSet_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R x D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : e x = realCode A) :
    (degreeSet φ o Q z R x D).Eval e ↔ e D = degreeCode (e R) A := by
  simp only [degreeSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro w
    by_cases hw : w ∈ e R
    · obtain ⟨B,rfl⟩ := hR w hw
      rw [realCode_mem_degreeCode]
      have hh := (h _ hw).trans (hφ (o+1) (Q+1) (z+1) 0 (x+1) (cons (realCode B) e)
        ho hQ hz B A rfl hA)
      exact hh.trans (and_iff_right hw).symm
    · exact ⟨fun h => False.elim (hw (hsub h)),fun h => False.elim (hw (degreeCode_subset _ _ h))⟩
  · intro hd
    refine ⟨hd.symm ▸ degreeCode_subset (e R) A,?_⟩
    intro w hw
    obtain ⟨B,rfl⟩ := hR w hw
    rw [hd,realCode_mem_degreeCode,and_iff_right hw]
    exact (hφ (o+1) (Q+1) (z+1) 0 (x+1) (cons (realCode B) e) ho hQ hz B A rfl hA).symm
end Formula

end TuringRigidity.BoundedSetTheory

