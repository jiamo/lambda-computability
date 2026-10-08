import Start.RigidityArithmeticModelDecoding

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Effective/CodingBounds.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedDecoding
open SetCoding RelationCoding ArithmeticModelDecoding

theorem AntichainBelow.mono {p : AntichainCode} {x y : Degree} (hp : AntichainBelow p x) (h : x ≤ y) :
    AntichainBelow p y := ⟨hp.1.trans h,hp.2.1.trans h,hp.2.2.trans h⟩

theorem SetBelow.mono {p : SetCode} {x y : Degree} (hp : SetBelow p x) (h : x ≤ y) :
    SetBelow p y := ⟨hp.1.trans h,hp.2.1.mono h,hp.2.2.mono h⟩

theorem RelationBelow.mono {n : ℕ} {p : RelationCode n} {x y : Degree}
    (hp : RelationBelow p x) (h : x ≤ y) : RelationBelow p y :=
  ⟨fun i => (hp.1 i).mono h,hp.2.mono h⟩

def unary (p : SetCode) : RelationCode 1 := ⟨fun _ => p,p.tags⟩

theorem unary_below {p : SetCode} {y : Degree} (hp : SetBelow p y) : RelationBelow (unary p) y :=
  ⟨fun _ => hp,hp.2.1⟩

theorem unary_holds (p : SetCode) (x : Degree) : (unary p).Holds (one x) ↔ p.Holds x := by
  constructor
  · rintro ⟨c,hc,_⟩
    exact ⟨c 0,hc 0⟩
  · rintro ⟨c,hc⟩
    refine ⟨fun _ => c,fun i => ?_,?_⟩
    · fin_cases i
      exact hc
    · simpa only [Finset.sup_const,Finset.univ_nonempty,if_pos,unary] using hc.2.1

end TuringRigidity.BoundedDecoding

