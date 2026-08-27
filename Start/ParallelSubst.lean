/-
The calculus of parallel substitution for the untyped terms.

`Start/SelfInterpreter.lean` defines the parallel substitution `Lambda.substEnv` and its
environment extension `Lambda.envCons`.  This file adds the two equations that any use of
parallel substitution under a binder needs, in the form already available for Gödel's `T`
(`Start/SystemTSyntax.lean`):

* `Lambda.lift_substEnv` — lifting a parallel substitution is the parallel substitution of the
  lifted environment;
* `Lambda.subst_substEnv`, `Lambda.subst_zero_substEnv` — substituting into a parallel
  substitution composes the two environments; in particular
  `(substEnv (envCons σ) t)[v/0] = substEnv (envScons v σ) t`.
-/

import Start.SelfInterpreter

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Extend an environment with a term at index `0` (no lifting: used when the binder is being
substituted away). -/
def envScons (v : Lambda) (u : ℕ → Lambda) : ℕ → Lambda
  | 0 => v
  | k + 1 => u k

@[simp] theorem envScons_zero (v : Lambda) (u : ℕ → Lambda) : envScons v u 0 = v := rfl

@[simp] theorem envScons_succ (v : Lambda) (u : ℕ → Lambda) (k : ℕ) :
    envScons v u (k + 1) = u k := rfl

@[simp] theorem envCons_zero (u : ℕ → Lambda) : envCons u 0 = Lambda.var 0 := rfl

@[simp] theorem envCons_succ (u : ℕ → Lambda) (k : ℕ) :
    envCons u (k + 1) = Lambda.lift 1 0 (u k) := rfl

/-- Lifting commutes with parallel substitution. -/
theorem lift_substEnv : ∀ (t : Lambda) (n j : ℕ) (u : ℕ → Lambda),
    Lambda.lift n j (substEnv u t) = substEnv (fun i => Lambda.lift n j (u i)) t := by
  intro t
  induction t with
  | var m => intro n j u; rfl
  | app a b iha ihb =>
      intro n j u
      simp only [substEnv, Lambda.lift, iha n j u, ihb n j u]
  | lam t ih =>
      intro n j u
      have hcons : (fun i => Lambda.lift n (j + 1) (envCons u i)) =
          envCons (fun i => Lambda.lift n j (u i)) := by
        funext i
        cases i with
        | zero => simp [Lambda.lift]
        | succ i =>
            simp only [envCons_succ]
            exact (Lambda.lift_lift (u i) 1 n 0 j (Nat.zero_le j)).symm
      simp only [substEnv, Lambda.lift, ih n (j + 1) (envCons u), hcons]

/-- Substituting into a parallel substitution composes the two environments. -/
theorem subst_substEnv (v : Lambda) :
    ∀ (t : Lambda) (k : ℕ) (u w : ℕ → Lambda),
      (∀ j, w j = Lambda.subst (Lambda.lift k 0 v) k (u j)) →
      Lambda.subst (Lambda.lift k 0 v) k (substEnv u t) = substEnv w t := by
  intro t
  induction t with
  | var j => intro k u w hw; simp only [substEnv, hw j]
  | app a b iha ihb =>
      intro k u w hw
      simp only [substEnv, Lambda.subst, iha k u w hw, ihb k u w hw]
  | lam t ih =>
      intro k u w hw
      have hlift : Lambda.lift 1 0 (Lambda.lift k 0 v) = Lambda.lift (k + 1) 0 v := by
        rw [Nat.add_comm k 1, Lambda.lift_add]
      have hstep : ∀ j, envCons w j =
          Lambda.subst (Lambda.lift (k + 1) 0 v) (k + 1) (envCons u j) := by
        intro j
        cases j with
        | zero => simp [Lambda.subst]
        | succ j =>
            simp only [envCons_succ, hw j]
            rw [← hlift, Lambda.lift_subst (u j) (Lambda.lift k 0 v) 1 0 k (Nat.zero_le k)]
      have hbody := ih (k + 1) (envCons u) (envCons w) hstep
      simp only [substEnv, Lambda.subst, hlift]
      exact congrArg Lambda.lam hbody

/-- The equation that computes a β-step through a parallel substitution. -/
theorem subst_zero_substEnv (v t : Lambda) (u : ℕ → Lambda) :
    Lambda.subst v 0 (substEnv (envCons u) t) = substEnv (envScons v u) t := by
  have key : ∀ j, envScons v u j = Lambda.subst (Lambda.lift 0 0 v) 0 (envCons u j) := by
    intro j
    rw [Lambda.lift_zero]
    cases j with
    | zero => simp [Lambda.subst]
    | succ j =>
        simp only [envCons_succ, envScons_succ]
        exact (Lambda.subst_lift (u j) v 0).symm
  have h := subst_substEnv v t 0 (envCons u) (envScons v u) key
  rwa [Lambda.lift_zero] at h

end Lambda
