/-
Conditional Kolmogorov complexity `K(s | y)` for the lambda calculus.

A *conditional program* for `s` given `y` is a closed lambda term `t` such that `t (church y)`
reduces to `church s`, and

  `kolmCond s y = sInf { size t | t closed and t (church y) ↠ church s }`

is the least size of such a term.  The set is never empty: the constant function
`λ_. church s` is always a conditional program, so `K(s | y)` is well defined and
`K(s | y) ≤ K(s) + 1`.

The basic inequalities proved here are

* `Lambda.kolmCond_le_kolm_succ` — `K(s | y) ≤ K(s) + 1`: conditional complexity never hurts;
* `Lambda.kolmCond_self_le_two` — `K(y | y) ≤ 2`, witnessed by the identity `λx. x`;
* `Lambda.kolm_le_kolmCond_add` — `K(s) ≤ K(s | y) + K(y) + 1`: knowing `y` can save at most
  the cost of describing `y`.  This is the (easy, exact) half of the information-symmetry
  estimate `K(s, y) = K(y) + K(s | y) + O(log)`;
* `Lambda.kolmCond_le_kolmCond_add` — `K(s | y) ≤ K(s | z) + K(z | y) + 4`, transitivity of
  conditional descriptions, using the composition combinator.

The `+1`, `+2`, `+4` constants are exactly the syntactic overhead of the wrappers used
(`λ`, `λx.x`, and `λx. t (u x)` respectively) in the size measure `Lambda.size`.
-/

import Start.KolmogorovDef

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Conditional programs
------------------------------------------------------------------------

/-- `t` is a *conditional program* for `s` given `y`: a closed term such that `t (church y)`
reduces to `church s`. -/
def IsCondProgramFor (t : Lambda) (s y : ℕ) : Prop :=
  Lambda.IsClosed t ∧ Lambda.reduces (Lambda.app t (Lambda.church y)) (Lambda.church s)

/-- Any (unconditional) program can be turned into a conditional one that ignores its input,
at the cost of one extra `λ`. -/
theorem isCondProgramFor_lam_of_isProgramFor {t : Lambda} {s : ℕ} (h : IsProgramFor t s)
    (y : ℕ) : IsCondProgramFor (Lambda.lam t) s y := by
  refine ⟨Lambda.IsClosed_lam h.1, ?_⟩
  refine Lambda.reduces.step _ _ _ (Lambda.step.beta t (Lambda.church y)) ?_
  rw [Lambda.IsClosed_imp_subst_eq h.1]
  exact h.2

/-- The identity is a conditional program for `y` given `y`. -/
theorem isCondProgramFor_id (y : ℕ) : IsCondProgramFor (Lambda.lam (Lambda.var 0)) y y := by
  constructor
  · intro s x
    simp [Lambda.subst]
  · refine Lambda.reduces.step _ _ _ (Lambda.step.beta (Lambda.var 0) (Lambda.church y)) ?_
    have hv : Lambda.subst (Lambda.church y) 0 (Lambda.var 0) = Lambda.church y := by
      simp [Lambda.subst]
    rw [hv]
    exact Lambda.reduces.refl _

------------------------------------------------------------------------
-- The conditional complexity function
------------------------------------------------------------------------

/-- **Conditional Kolmogorov complexity** `K(s | y)`: the least size of a closed term `t` with
`t (church y) ↠ church s`. -/
def kolmCond (s y : ℕ) : ℕ := sInf {n | ∃ t : Lambda, IsCondProgramFor t s y ∧ size t = n}

theorem kolmCond_le_of_isCondProgramFor {t : Lambda} {s y : ℕ} (h : IsCondProgramFor t s y) :
    kolmCond s y ≤ size t :=
  Nat.sInf_le ⟨t, h, rfl⟩

theorem exists_condProgram_of_kolmCond (s y : ℕ) :
    ∃ t : Lambda, IsCondProgramFor t s y ∧ size t = kolmCond s y :=
  Nat.sInf_mem (s := {n | ∃ t : Lambda, IsCondProgramFor t s y ∧ size t = n})
    ⟨size (Lambda.lam (Lambda.church s)), Lambda.lam (Lambda.church s),
      isCondProgramFor_lam_of_isProgramFor (isProgramFor_church s) y, rfl⟩

------------------------------------------------------------------------
-- Basic inequalities
------------------------------------------------------------------------

/-- Conditioning never costs more than one extra symbol: `K(s | y) ≤ K(s) + 1`. -/
theorem kolmCond_le_kolm_succ (s y : ℕ) : kolmCond s y ≤ kolm s + 1 := by
  obtain ⟨t, ht, hsize⟩ := exists_program_of_kolm s
  have := kolmCond_le_of_isCondProgramFor (isCondProgramFor_lam_of_isProgramFor ht y)
  simpa [hsize] using this

/-- `K(y | y) ≤ 2`: given `y`, the identity describes `y`. -/
theorem kolmCond_self_le_two (y : ℕ) : kolmCond y y ≤ 2 := by
  have := kolmCond_le_of_isCondProgramFor (isCondProgramFor_id y)
  simpa using this

/-- Conditional complexity is bounded by the unconditional one applied to the constant
description: `K(s | y) ≤ 3 * s + 4`. -/
theorem kolmCond_le_church (s y : ℕ) : kolmCond s y ≤ 3 * s + 4 := by
  have h := kolmCond_le_kolm_succ s y
  have h' := kolm_le_church s
  omega

/-- Knowing `y` can save at most the cost of describing `y`:
`K(s) ≤ K(s | y) + K(y) + 1`. -/
theorem kolm_le_kolmCond_add (s y : ℕ) : kolm s ≤ kolmCond s y + kolm y + 1 := by
  obtain ⟨t, ht, hts⟩ := exists_condProgram_of_kolmCond s y
  obtain ⟨p, hp, hps⟩ := exists_program_of_kolm y
  have hclosed : Lambda.IsClosed (Lambda.app t p) := Lambda.IsClosed_app ht.1 hp.1
  have hred : Lambda.reduces (Lambda.app t p) (Lambda.church s) :=
    Lambda.reduces_trans (Lambda.reduces_app_right (t1 := t) hp.2) ht.2
  have := kolm_le_of_isProgramFor (t := Lambda.app t p) (s := s) ⟨hclosed, hred⟩
  simp only [size_app] at this
  omega

/-- Composition of conditional descriptions: `K(s | y) ≤ K(s | z) + K(z | y) + 4`.  The witness
is `λx. t (u x)`, where `u` produces `z` from `y` and `t` produces `s` from `z`. -/
theorem kolmCond_le_kolmCond_add (s z y : ℕ) :
    kolmCond s y ≤ kolmCond s z + kolmCond z y + 4 := by
  obtain ⟨t, ht, hts⟩ := exists_condProgram_of_kolmCond s z
  obtain ⟨u, hu, hus⟩ := exists_condProgram_of_kolmCond z y
  -- the composite `λx. t (u x)`
  set c : Lambda := Lambda.lam (Lambda.app t (Lambda.app u (Lambda.var 0))) with hc
  have hcclosed : Lambda.IsClosed c := by
    intro a x
    have hexp : Lambda.subst a x c =
        Lambda.lam (Lambda.app (Lambda.subst (Lambda.lift 1 0 a) (x + 1) t)
          (Lambda.app (Lambda.subst (Lambda.lift 1 0 a) (x + 1) u)
            (Lambda.subst (Lambda.lift 1 0 a) (x + 1) (Lambda.var 0)))) := rfl
    have hv : Lambda.subst (Lambda.lift 1 0 a) (x + 1) (Lambda.var 0) = Lambda.var 0 := by
      simp [Lambda.subst]
    rw [hexp, ht.1, hu.1, hv]
  have hcred : Lambda.reduces (Lambda.app c (Lambda.church y)) (Lambda.church s) := by
    refine Lambda.reduces.step _ _ _
      (Lambda.step.beta (Lambda.app t (Lambda.app u (Lambda.var 0))) (Lambda.church y)) ?_
    have hsub : Lambda.subst (Lambda.church y) 0 (Lambda.app t (Lambda.app u (Lambda.var 0)))
        = Lambda.app t (Lambda.app u (Lambda.church y)) := by
      have hexp : Lambda.subst (Lambda.church y) 0 (Lambda.app t (Lambda.app u (Lambda.var 0))) =
          Lambda.app (Lambda.subst (Lambda.church y) 0 t)
            (Lambda.app (Lambda.subst (Lambda.church y) 0 u)
              (Lambda.subst (Lambda.church y) 0 (Lambda.var 0))) := rfl
      have hv : Lambda.subst (Lambda.church y) 0 (Lambda.var 0) = Lambda.church y := by
        simp [Lambda.subst]
      rw [hexp, ht.1, hu.1, hv]
    rw [hsub]
    exact Lambda.reduces_trans (Lambda.reduces_app_right (t1 := t) hu.2) ht.2
  have := kolmCond_le_of_isCondProgramFor (t := c) (s := s) (y := y) ⟨hcclosed, hcred⟩
  simp only [hc, size_lam, size_app, size_var] at this
  omega

end Lambda

end
