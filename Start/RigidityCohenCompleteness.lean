import Start.RigidityEffectiveCohen

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenCompleteness.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump

theorem sigma1_enumeration {Y : Oracle} {P : ℕ → Prop} (h : Sigma Y 1 P) :
    ∃ e, ∀ n, P n ↔ Halts Y e n := by
  classical
  obtain ⟨Q,hQ,he⟩ := h
  have hf := Nat.RecursiveIn.rfind (recursive_not hQ)
  obtain ⟨e,hd⟩ := partial_table hf
  refine ⟨e,fun n => (he n).trans ?_⟩
  rw [hd n]
  erw [Nat.rfind_dom]
  simp [Quant]

theorem OneGeneric.decides {Y G : Oracle} (hG : OneGeneric Y G)
    {P : ℕ → Prop} (hP : Sigma Y 1 P) : ∃ p : List Bool,
      (∀ n < p.length, G n = p.getD n false) ∧
        (P (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ P (encode q)) := by
  obtain ⟨e,he⟩ := sigma1_enumeration hP
  obtain ⟨p,hp,hd⟩ := hG e
  refine ⟨p,hp,?_⟩
  simpa only [he] using hd

theorem relative_one_generic (Y : Oracle) : ∃ G : Oracle, Reduces G (jump Y) ∧
    ∀ P : ℕ → Prop, Sigma Y 1 P → ∃ p : List Bool,
      (∀ n < p.length, G n = p.getD n false) ∧
        (P (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ P (encode q)) :=
  ⟨generic Y,generic_reduces Y,fun _ hP => (generic_oneGeneric Y).decides hP⟩

end TuringRigidity.EffectiveCohen

