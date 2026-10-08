import Start.RigidityAutomorphismOutputSentence

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Syntax/BoundedAutomorphismOutput.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory SetDegreeDecoding PersistentRestrictions
universe u

def boundedOutputFormula : Formula :=
  .existsMem 3 (.existsMem 4 (.conj (.member 3 1)
    (.conj (.member 4 0) (.pairMem 1 0 2))))

theorem boundedOutputFormula_raw (f x y D : ZFSet.{u}) :
    boundedOutputFormula.Eval (cons f (cons x (cons y (fun _ => D)))) ↔
      ∃ d ∈ D, ∃ b ∈ D, x ∈ d ∧ y ∈ b ∧ ZFSet.pair d b ∈ f := by
  simp only [boundedOutputFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]

theorem boundedOutputFormula_spec (I : CountableIdeal) (σ : I ≃o I)
    (A : Oracle) (hA : degree A ∈ I.carrier) (y : ZFSet.{u}) :
    boundedOutputFormula.Eval
      (cons (automorphismSet σ) (cons (realCode A) (cons y (fun _ => idealSet I)))) ↔
      ∃ B : Oracle, realCode B = y ∧ degree B = (σ ⟨degree A,hA⟩).val := by
  rw [boundedOutputFormula_raw]
  constructor
  · rintro ⟨d,_,b,_,had,hbb,hf⟩
    obtain ⟨a,hpair⟩ := (mem_automorphismSet σ _).mp hf
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    have ha : degree A = a.val := (real_mem_degreeSet A a.val).mp had
    have ha' : (⟨degree A,hA⟩ : I) = a := Subtype.ext ha
    obtain ⟨B,hB,hdeg⟩ := (mem_degreeSet (σ a).val y).mp hbb
    exact ⟨B,hB.symm,by rwa [ha']⟩
  · rintro ⟨B,hB,hdeg⟩
    have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
      (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
    refine ⟨degreeSet (degree A),hi ⟨degree A,hA⟩,
      degreeSet (σ ⟨degree A,hA⟩).val,hi (σ ⟨degree A,hA⟩),
      (real_mem_degreeSet A _).mpr rfl,?_,?_⟩
    · rw [←hB]; exact (real_mem_degreeSet B _).mpr hdeg
    · exact (mem_automorphismSet σ _).mpr ⟨⟨degree A,hA⟩,rfl⟩

end TuringRigidity.BoundedForcing

