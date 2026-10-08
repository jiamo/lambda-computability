import Start.RigiditySentenceInlining

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Constructibility/FiniteDefinitionTransfer.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem finite_real_tail (p : SentenceForm) (D : Set ZFSet.{u})
    (z P : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    p.Sat D (cons z (cons P (tupleEnv (fun i : Fin p.bound => e i)))) ↔
      p.Sat D (cons z (cons P e)) := by
  apply p.finite_support
  intro i hi
  rcases i with _|_|i
  · rfl
  · rfl
  · simp only [cons_succ,tupleEnv,dif_pos (show i < p.bound by omega)]

theorem definedSubset_of_membership (M V : ZFSet.{u}) (hM : Transitive M)
    (hV : V ∈ M) (p : SentenceForm) (e : ℕ → ZFSet.{u})
    (hp : ∀ z ∈ M, p.Sat (M : Set ZFSet) (cons z e) ↔ z ∈ V) :
    V = definedSubset M p (fun i : Fin p.bound => e i) := by
  apply ZFSet.ext; intro z
  rw [mem_definedSubset]
  have hs := p.finite_support (M : Set ZFSet) (cons z e)
    (cons z (tupleEnv (fun i : Fin p.bound => e i)))
    (by
      intro i hin
      cases i with
      | zero => rfl
      | succ i => simp only [cons_succ,tupleEnv,dif_pos (show i < p.bound by omega)])
  constructor
  · intro hz
    have hzM := hM V hV z hz
    exact ⟨hzM,hs.mp ((hp z hzM).mpr hz)⟩
  · rintro ⟨hzM,hz⟩
    exact (hp z hzM).mp (hs.mpr hz)

end TuringRigidity.RelativeConstructible

