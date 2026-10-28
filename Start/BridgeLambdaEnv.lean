/-
**Parallel substitution of the λ core, for erasures from other calculi** — milestone M31.

Several calculi of the library use parallel substitution with a lifting `up σ` (`0 ↦ var 0`,
`n + 1 ↦ (σ n)` renamed by `succ`).  The λ core (`Start/Syntax.lean`) uses `Lambda.lift` and the
single substitution `Lambda.subst v 0`.  To show that an erasure into the λ core commutes with
substitution, these equations express both operations through the core's parallel substitution
`Lambda.substEnv` (`Start/SelfInterpreter.lean`, `Start/ParallelSubst.lean`):

* `Lambda.renEnv`, `Lambda.upRen` — renamings as environments, and their lifting;
  `Lambda.envCons_renEnv`: lifting commutes with `renEnv`;
* `Lambda.lift_eq_substEnv`, `Lambda.lift_one_zero` — `lift 1 k` is a renaming;
* `Lambda.subst_zero_eq_substEnv` — `subst v 0` is the parallel substitution `v, 0, 1, …`.
-/

import Start.ParallelSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- A renaming as an environment of variables. -/
def renEnv (ξ : ℕ → ℕ) : ℕ → Lambda := fun n => Lambda.var (ξ n)

/-- Lifting a renaming under a binder. -/
def upRen (ξ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ξ n + 1

theorem envCons_renEnv (ξ : ℕ → ℕ) : envCons (renEnv ξ) = renEnv (upRen ξ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [envCons, renEnv, upRen, Lambda.lift]

theorem envCons_var : envCons (fun k => Lambda.var k) = fun k => Lambda.var k := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [envCons, Lambda.lift]

/-- The renaming that `lift 1 k` performs. -/
def liftRen (k : ℕ) (n : ℕ) : ℕ := if n < k then n else n + 1

theorem upRen_liftRen (k : ℕ) : upRen (liftRen k) = liftRen (k + 1) := by
  funext n
  cases n with
  | zero => simp [upRen, liftRen]
  | succ n =>
      simp only [upRen, liftRen]
      split <;> split <;> omega

/-- **`lift 1 k` is a renaming.** -/
theorem lift_eq_substEnv : ∀ (t : Lambda) (k : ℕ), Lambda.lift 1 k t = substEnv (renEnv (liftRen k)) t := by
  intro t
  induction t with
  | var n =>
      intro k
      simp only [Lambda.lift, substEnv, renEnv, liftRen]
      split <;> rfl
  | app a b iha ihb => intro k; simp only [Lambda.lift, substEnv, iha k, ihb k]
  | lam t ih =>
      intro k
      simp only [Lambda.lift, substEnv, envCons_renEnv, upRen_liftRen, ih (k + 1)]

theorem lift_one_zero (t : Lambda) : Lambda.lift 1 0 t = substEnv (renEnv Nat.succ) t := by
  rw [lift_eq_substEnv]
  congr 1

/-- **`subst v 0` is the parallel substitution of `v, 0, 1, …`.** -/
theorem subst_zero_eq_substEnv (v t : Lambda) :
    Lambda.subst v 0 t = substEnv (envScons v (fun k => Lambda.var k)) t := by
  have h := subst_zero_substEnv v t (fun k => Lambda.var k)
  rw [envCons_var, substEnv_var_id] at h
  exact h

end Lambda
