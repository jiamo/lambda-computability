import Start.RigidityNaturalDefinitions

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalProjectionFormula.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

def naturalProjection (right : Bool) : Formula := .existsMem 2 (.existsMem 3
  (.conj (naturalPair 4 5 1 0 3) (.equal 2 (if right then 0 else 1))))

theorem naturalProjection_spec (right : Bool) : DefinesNatural.{u} (naturalProjection right)
    (fun n => if right then (Nat.unpair n).2 else (Nat.unpair n).1) := by
  intro e ho hQ n hn
  have select (a b : ZFSet.{u}) : cons b (cons a e) (if right then 0 else 1) =
      if right then b else a := by cases right <;> rfl
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  simp only [naturalProjection,Formula.Eval,cons_succ,select]
  constructor
  · rintro ⟨a,ha,b,hb,hpair,hy⟩
    rw [ho] at ha hb
    obtain ⟨a,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨b,rfl⟩ := (mem_omega b).mp hb
    have hp := (naturalPair_spec 4 5 1 0 3 (cons (natSet b) (cons (natSet a) e))
      ho hQ a b rfl rfl).mp hpair
    have he : n = Nat.pair a b := natSet_injective (hn.symm.trans hp)
    subst n
    cases right <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.unpair_pair] using hy
  · intro hy
    refine ⟨natSet (Nat.unpair n).1,hmem _,natSet (Nat.unpair n).2,hmem _,?_,?_⟩
    · apply (naturalPair_spec 4 5 1 0 3
        (cons (natSet (Nat.unpair n).2) (cons (natSet (Nat.unpair n).1) e))
        ho hQ _ _ rfl rfl).mpr
      simpa only [cons_succ,Nat.pair_unpair] using hn
    · cases right <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using hy

end Formula
end TuringRigidity.BoundedSetTheory

