/-
**Cones and the size of the degree structure.**

Every oracle computes only countably many partial functions
(`Lambda.Oracle.countable_cone`): the cone below a degree is the range of the indexing `Φ^A`.
Since there are uncountably many oracles, but each degree only accounts for countably many of
them, there must be uncountably many Turing degrees
(`Lambda.Oracle.not_countable_turingDegree`).

Together with `Start/OracleJump.lean` (no maximum degree), `Start/OracleJoin.lean` (binary
suprema) and `Start/KleenePost.lean` (incomparable degrees), this pins down the coarse shape of
the degree structure.
-/

import Start.OracleSound
import Mathlib.Data.Set.Countable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open scoped Computability

/-- **The cone below an oracle is countable**: only countably many partial functions are
recursive in a given oracle. -/
theorem countable_cone (A : ℕ → Bool) :
    Set.Countable {f : ℕ →. ℕ | RecursiveIn {oracleFun A} f} := by
  refine Set.Countable.mono ?_ (Set.countable_range fun e : ℕ => Phi A e)
  intro f hf
  obtain ⟨e, he⟩ := recursiveIn_iff_exists_index.1 hf
  exact ⟨e, he⟩

theorem oracleFun_injective : Function.Injective oracleFun := by
  intro A B h
  funext n
  have := congrFun h n
  simp only [oracleFun, Part.some_inj] at this
  by_cases hA : A n <;> by_cases hB : B n <;> simp_all

theorem not_countable_fun_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hf fun k => !(f k k)
  have := congrFun hn n
  simp at this

/-- **There are uncountably many Turing degrees.**  Each degree contains only countably many
oracles, while there are uncountably many oracles. -/
theorem not_countable_turingDegree : ¬ Countable (Antisymmetrization (ℕ →. ℕ) TuringReducible) := by
  classical
  intro hcount
  have : Countable (Antisymmetrization (ℕ →. ℕ) TuringReducible) := hcount
  set F : (ℕ → Bool) → Antisymmetrization (ℕ →. ℕ) TuringReducible :=
    fun A => toAntisymmetrization TuringReducible (oracleFun A) with hF
  -- a representative oracle for each degree that has one
  set rep : Antisymmetrization (ℕ →. ℕ) TuringReducible → ℕ → Bool := fun d =>
    if h : ∃ A, F A = d then h.choose else fun _ => false with hrep
  have hrepF : ∀ A, F (rep (F A)) = F A := by
    intro A
    have hex : ∃ B, F B = F A := ⟨A, rfl⟩
    rw [hrep]
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hindex : ∀ A, ∃ e : ℕ, Phi (rep (F A)) e = oracleFun A := by
    intro A
    refine recursiveIn_iff_exists_index.1 ?_
    exact toAntisymmetrization_le_toAntisymmetrization_iff.1 (le_of_eq (hrepF A).symm)
  choose idx hidx using hindex
  have hinj : Function.Injective fun A => (F A, idx A) := by
    intro A B hAB
    have h1 : F A = F B := congrArg Prod.fst hAB
    have h2 : idx A = idx B := congrArg Prod.snd hAB
    refine oracleFun_injective ?_
    rw [← hidx A, ← hidx B, h1, h2]
  exact not_countable_fun_bool hinj.countable

end Oracle
end Lambda
