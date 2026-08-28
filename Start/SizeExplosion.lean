/-
Size explosion in the untyped lambda calculus.

A *reasonable* cost model for the lambda calculus has to relate the number of beta steps to the
work a machine has to do.  The obstruction that makes this delicate is **size explosion**: a term
of linear size can reach, in a linear number of steps, a normal form of exponential size.  So no
evaluator that actually writes down the normal form (or even the intermediate terms) can run in
time polynomial in the number of steps, and any invariance result has to use a shared
representation of the result rather than the term itself.

This module makes the phenomenon explicit with the standard family of iterated duplicators.

* `Lambda.dupTower n` — the closed term `λx₁. (λx₂. … (λxₙ. λy. y) (xₙ₋₁ xₙ₋₁) …) (x₁ x₁)`,
  built so that feeding it an argument duplicates that argument once per level;
* `Lambda.binTree t n` — the complete binary tree of applications of depth `n` with `2 ^ n`
  leaves, all equal to `t`;
* `Lambda.explode n = dupTower n (var 0)` — the exploding family itself.

The results are

* `Lambda.size_explode` — `explode n` has size `5 * n + 4`, i.e. linear in `n`;
* `Lambda.reducesIn_explode` — `explode n` reaches `binTree (var 0) n` in exactly `n + 1` beta
  steps (`Lambda.reducesIn`, the step-counting version of `Lambda.reduces`, is defined in
  `Start/ReducesIn.lean`);
* `Lambda.binTree_var_is_normal` — that term is a normal form;
* `Lambda.two_pow_le_size_binTree_var` — its size is at least `2 ^ n` (in fact `2 ^ (n+1) - 1`);
* `Lambda.exists_size_explosion` — the three facts combined, and
  `Lambda.exists_size_explosion_steps`, the same statement organised by the number of steps: for
  every `k ≥ 1` there is a term of size `≤ 5 * k` whose normal form is reached in `k` steps and
  has size at least `2 ^ (k - 1)`.
-/

import Start.ReducesIn
import Start.TermSize
import Start.EvalSound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

------------------------------------------------------------------------
-- The exploding family
------------------------------------------------------------------------

/-- The `n`-fold duplicator: `dupTower 0` is the identity and `dupTower (n+1)` feeds the square
`x x` of its argument to `dupTower n`. -/
def dupTower : ℕ → Lambda
  | 0 => Lambda.lam (Lambda.var 0)
  | n + 1 => Lambda.lam (Lambda.app (dupTower n) (Lambda.app (Lambda.var 0) (Lambda.var 0)))

/-- The complete binary tree of applications of depth `n`, all of whose `2 ^ n` leaves are `t`. -/
def binTree (t : Lambda) : ℕ → Lambda
  | 0 => t
  | n + 1 => Lambda.app (binTree t n) (binTree t n)

/-- The exploding family: `dupTower n` applied to a variable. -/
def explode (n : ℕ) : Lambda := Lambda.app (dupTower n) (Lambda.var 0)

/-- Every duplicator is closed, so substitution does not touch it. -/
theorem subst_dupTower (n : ℕ) (s : Lambda) (x : ℕ) :
    Lambda.subst s x (dupTower n) = dupTower n := by
  induction n generalizing s x with
  | zero => simp [dupTower, Lambda.subst]
  | succ n ih => simp [dupTower, Lambda.subst, ih]

/-- One level of the tower: the argument gets duplicated. -/
theorem step_dupTower_succ (n : ℕ) (t : Lambda) :
    Lambda.step (Lambda.app (dupTower (n + 1)) t)
      (Lambda.app (dupTower n) (Lambda.app t t)) := by
  have h := Lambda.step.beta
    (Lambda.app (dupTower n) (Lambda.app (Lambda.var 0) (Lambda.var 0))) t
  simpa [dupTower, Lambda.subst, subst_dupTower] using h

/-- The bottom of the tower is the identity. -/
theorem step_dupTower_zero (t : Lambda) :
    Lambda.step (Lambda.app (dupTower 0) t) t := by
  have h := Lambda.step.beta (Lambda.var 0) t
  simpa [dupTower, Lambda.subst] using h

/-- Squaring the leaves adds one level to the tree. -/
theorem binTree_app_self (t : Lambda) (n : ℕ) :
    binTree (Lambda.app t t) n = binTree t (n + 1) := by
  induction n with
  | zero => simp [binTree]
  | succ n ih => simp [binTree, ih]

/-- **The duplicator tower explodes**: `dupTower n` applied to `t` reaches, in exactly `n + 1`
steps, the complete binary tree of depth `n` over `t`. -/
theorem reducesIn_dupTower (n : ℕ) (t : Lambda) :
    reducesIn (n + 1) (Lambda.app (dupTower n) t) (binTree t n) := by
  induction n generalizing t with
  | zero =>
      exact reducesIn.step (step_dupTower_zero t) (reducesIn.refl _)
  | succ n ih =>
      have h := ih (Lambda.app t t)
      have h' : reducesIn (n + 1) (Lambda.app (dupTower n) (Lambda.app t t))
          (binTree t (n + 1)) := by
        simpa [binTree_app_self] using h
      exact reducesIn.step (step_dupTower_succ n t) h'

/-- `explode n` reaches its normal form in exactly `n + 1` beta steps. -/
theorem reducesIn_explode (n : ℕ) :
    reducesIn (n + 1) (explode n) (binTree (Lambda.var 0) n) :=
  reducesIn_dupTower n (Lambda.var 0)

theorem reduces_explode (n : ℕ) :
    Lambda.reduces (explode n) (binTree (Lambda.var 0) n) :=
  reduces_of_reducesIn (reducesIn_explode n)

------------------------------------------------------------------------
-- Sizes
------------------------------------------------------------------------

theorem size_dupTower (n : ℕ) : size (dupTower n) = 5 * n + 2 := by
  induction n with
  | zero => simp [dupTower, size]
  | succ n ih => simp [dupTower, size, ih]; omega

/-- The exploding term has linear size. -/
theorem size_explode (n : ℕ) : size (explode n) = 5 * n + 4 := by
  simp [explode, size, size_dupTower]

/-- The tree of depth `n` over `t` has `2 ^ n` leaves, hence size `2 ^ n * (size t + 1) - 1`. -/
theorem size_binTree_succ (t : Lambda) (n : ℕ) :
    size (binTree t n) + 1 = 2 ^ n * (size t + 1) := by
  induction n with
  | zero => simp [binTree]
  | succ n ih =>
      have : size (binTree t (n + 1)) + 1 = 2 * (size (binTree t n) + 1) := by
        simp [binTree]
        omega
      rw [this, ih, pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]

/-- The normal form of `explode n` has size `2 ^ (n + 1) - 1`. -/
theorem size_binTree_var (n : ℕ) : size (binTree (Lambda.var 0) n) + 1 = 2 ^ (n + 1) := by
  have h := size_binTree_succ (Lambda.var 0) n
  simpa [size, pow_succ, Nat.mul_comm] using h

/-- **The normal form is exponentially large.** -/
theorem two_pow_le_size_binTree_var (n : ℕ) : 2 ^ n ≤ size (binTree (Lambda.var 0) n) := by
  have h := size_binTree_var n
  have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, Nat.mul_two]
  omega

------------------------------------------------------------------------
-- Normality of the result
------------------------------------------------------------------------

theorem binTree_var_ne_lam (n : ℕ) (u : Lambda) : binTree (Lambda.var 0) n ≠ Lambda.lam u := by
  cases n with
  | zero => simp [binTree]
  | succ n => simp [binTree]

/-- The complete tree of variables is a normal form. -/
theorem binTree_var_is_normal (n : ℕ) : Lambda.is_normal (binTree (Lambda.var 0) n) := by
  induction n with
  | zero => simpa [binTree] using Lambda.var_normal 0
  | succ n ih =>
      exact Lambda.app_normal ih ih (binTree_var_ne_lam n)

------------------------------------------------------------------------
-- Size explosion
------------------------------------------------------------------------

/-- **Size explosion.**  For every `n` there is a term of size `5 * n + 4` that reaches a normal
form in `n + 1` beta steps, and that normal form has size at least `2 ^ n`. -/
theorem exists_size_explosion (n : ℕ) :
    ∃ M N : Lambda,
      size M = 5 * n + 4 ∧ reducesIn (n + 1) M N ∧ Lambda.is_normal N ∧ 2 ^ n ≤ size N :=
  ⟨explode n, binTree (Lambda.var 0) n, size_explode n, reducesIn_explode n,
    binTree_var_is_normal n, two_pow_le_size_binTree_var n⟩

/-- The same statement organised by the number of steps: `k` beta steps from a term of size at
most `5 * k` can produce a normal form of size at least `2 ^ (k - 1)`.  So the size of the result
is not bounded by any polynomial in the number of steps and the size of the input, and a cost
model counting beta steps can only be reasonable if the result is kept in a shared
representation. -/
theorem exists_size_explosion_steps (k : ℕ) (hk : 1 ≤ k) :
    ∃ M N : Lambda,
      size M ≤ 5 * k ∧ reducesIn k M N ∧ Lambda.is_normal N ∧ 2 ^ (k - 1) ≤ size N := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine ⟨explode n, binTree (Lambda.var 0) n, ?_, reducesIn_explode n,
    binTree_var_is_normal n, by simpa using two_pow_le_size_binTree_var n⟩
  rw [size_explode]
  omega

end Lambda
