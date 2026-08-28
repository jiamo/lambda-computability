/-
Syntactic size of a lambda term.

`Lambda.size t` counts the syntax nodes of `t`, with a de Bruijn index `i` costing `i + 1`
(writing the index costs something).  This is the "program length" measure used for Kolmogorov
complexity in `Start/Kolmogorov.lean` and for the size-explosion family in
`Start/SizeExplosion.lean`; it lives in its own module so that developments that only need the
measure do not have to depend on the whole complexity theory.
-/

import Start.Church

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

------------------------------------------------------------------------
-- Size of a term
------------------------------------------------------------------------

/-- Syntactic size of a term: the number of syntax nodes, where a de Bruijn index `i` counts as
`i + 1` (writing the index costs something).  This is the "program length" used for `K`. -/
def size : Lambda → ℕ
  | Lambda.var i => i + 1
  | Lambda.app a b => size a + size b + 1
  | Lambda.lam t => size t + 1

@[simp] theorem size_var (i : ℕ) : size (Lambda.var i) = i + 1 := rfl
@[simp] theorem size_app (a b : Lambda) : size (Lambda.app a b) = size a + size b + 1 := rfl
@[simp] theorem size_lam (t : Lambda) : size (Lambda.lam t) = size t + 1 := rfl

theorem size_pos (t : Lambda) : 0 < size t := by
  cases t <;> simp [size]

theorem size_iterate (n : ℕ) :
    size (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n) = 3 * n + 1 := by
  induction n with
  | zero => simp [Lambda.iterate_zero]
  | succ n ih => rw [Lambda.iterate_succ]; simp [ih]; omega

theorem size_church (n : ℕ) : size (Lambda.church n) = 3 * n + 3 := by
  rw [Lambda.church_eq_iterate]
  simp [size_iterate]

end Lambda
