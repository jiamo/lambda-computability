/-
Programs and the Kolmogorov complexity function.

A *program* for a natural number `s` is a closed lambda term that reduces to the Church numeral
`church s`, and `Lambda.kolm s` is the least size of such a program.  This module contains only
the definition and its immediate consequences; the incompressibility, non-computability and
invariance theorems are in `Start/Kolmogorov.lean`, and the conditional version `K(x | y)` is in
`Start/KolmogorovCond.lean`.
-/

import Start.TermSize
import Start.Combinators
import Mathlib.Order.Lattice.Nat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Programs and the complexity function
------------------------------------------------------------------------

/-- `t` is a *program* for `s`: a closed term reducing to the Church numeral of `s`. -/
def IsProgramFor (t : Lambda) (s : ℕ) : Prop :=
  Lambda.IsClosed t ∧ Lambda.reduces t (Lambda.church s)

theorem isProgramFor_church (s : ℕ) : IsProgramFor (Lambda.church s) s :=
  ⟨Lambda.church_closed s, Lambda.reduces.refl _⟩

/-- **Kolmogorov complexity** of a natural number in the lambda calculus: the least size of a
closed term reducing to its Church numeral. -/
def kolm (s : ℕ) : ℕ := sInf {n | ∃ t : Lambda, IsProgramFor t s ∧ size t = n}

theorem kolm_le_of_isProgramFor {t : Lambda} {s : ℕ} (h : IsProgramFor t s) : kolm s ≤ size t :=
  Nat.sInf_le ⟨t, h, rfl⟩

theorem exists_program_of_kolm (s : ℕ) : ∃ t : Lambda, IsProgramFor t s ∧ size t = kolm s :=
  Nat.sInf_mem (s := {n | ∃ t : Lambda, IsProgramFor t s ∧ size t = n})
    ⟨size (Lambda.church s), Lambda.church s, isProgramFor_church s, rfl⟩

theorem kolm_le_church (s : ℕ) : kolm s ≤ 3 * s + 3 := by
  simpa [size_church] using kolm_le_of_isProgramFor (isProgramFor_church s)

end Lambda

end
