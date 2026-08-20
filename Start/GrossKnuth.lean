/-
Normalization of the Gross–Knuth (complete development) reduction strategy.

`Lambda.rho` contracts *all* redexes of a term simultaneously (a complete
development).  This file proves that iterating `Lambda.rho` is a normalizing
strategy: whenever `t` reduces to a normal form `u`, some finite iterate
`Lambda.rho^[k] t` is literally equal to `u`.

The proof only uses the triangle property of parallel reduction that is already
available (`Lambda.step_p_diamond_aux`): applying it twice shows that `Lambda.rho`
is monotone for parallel reduction, and a normal form admits no proper parallel
reduct.
-/

import Start.Arithmetic


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Complete development is monotone for parallel reduction: this is the triangle
property `Lambda.step_p_diamond_aux` applied twice. -/
theorem Lambda.rho_mono {t t' : Lambda} (h : Lambda.step_p t t') :
    Lambda.step_p (Lambda.rho t) (Lambda.rho t') :=
  Lambda.step_p_diamond_aux (Lambda.step_p_diamond_aux h)

/-- Iterated complete development is monotone for parallel reduction. -/
theorem Lambda.rho_iterate_mono {t t' : Lambda} (h : Lambda.step_p t t') (k : ℕ) :
    Lambda.step_p (Lambda.rho^[k] t) (Lambda.rho^[k] t') := by
  induction k generalizing t t' with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (Lambda.rho_mono h)

/-- A normal form has no proper parallel reduct. -/
theorem Lambda.step_p_normal_eq {t t' : Lambda} (h : Lambda.is_normal t)
    (hp : Lambda.step_p t t') : t' = t :=
  (Lambda.reduces_normal_eq h (Lambda.step_p_imp_reduces hp)).symm

/-- Complete development fixes normal forms. -/
theorem Lambda.rho_normal {t : Lambda} (h : Lambda.is_normal t) : Lambda.rho t = t :=
  Lambda.step_p_normal_eq h (Lambda.step_p_rho t)

/-- A term reduces to its complete development. -/
theorem Lambda.reduces_rho (t : Lambda) : Lambda.reduces t (Lambda.rho t) :=
  Lambda.step_p_imp_reduces (Lambda.step_p_rho t)

/-- A term reduces to every iterate of its complete development. -/
theorem Lambda.reduces_rho_iterate (t : Lambda) (k : ℕ) :
    Lambda.reduces t (Lambda.rho^[k] t) := by
  induction k generalizing t with
  | zero => exact Lambda.reduces.refl t
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact Lambda.reduces_trans (Lambda.reduces_rho t) (ih _)

/-- **Gross–Knuth normalization.**  If `t` reduces to a normal form `u`, then iterating
the complete development `Lambda.rho` reaches `u` after finitely many steps. -/
theorem Lambda.rho_iterate_eq_of_reduces_normal {t u : Lambda} (h : Lambda.reduces t u) :
    Lambda.is_normal u → ∃ k, Lambda.rho^[k] t = u := by
  induction h with
  | refl t => exact fun _ => ⟨0, rfl⟩
  | step t t1 u hs _ ih =>
      intro hu
      obtain ⟨k, hk⟩ := ih hu
      refine ⟨k + 1, ?_⟩
      have h1 : Lambda.step_p t1 (Lambda.rho t) :=
        Lambda.step_p_diamond_aux (Lambda.step_imp_step_p hs)
      have h2 : Lambda.step_p (Lambda.rho^[k] t1) (Lambda.rho^[k] (Lambda.rho t)) :=
        Lambda.rho_iterate_mono h1 k
      rw [hk] at h2
      rw [Function.iterate_succ_apply]
      exact Lambda.step_p_normal_eq hu h2

end
