/-
Church numerals: iteration, the `succ` combinator, and their correctness proofs.

Extracted from `Start/Basic.lean` as part of the modular split; this module only
depends on the syntax and reduction layers.
-/

import Start.Syntax
import Start.Reduction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section


/-
Helper definitions and lemmas for `Lambda.iterate`.
-/
def Lambda.iterate (f x : Lambda) (n : ℕ) : Lambda :=
  (List.range n).foldl (fun t _ => Lambda.app f t) x

theorem Lambda.iterate_zero (f x : Lambda) : Lambda.iterate f x 0 = x := rfl

theorem Lambda.iterate_succ (f x : Lambda) (n : ℕ) :
    Lambda.iterate f x (n + 1) = Lambda.app f (Lambda.iterate f x n) := by
  -- By definition of `iterate`, we have `f.iterate x (n + 2) = f.app (f.iterate x (n + 1))`.
  simp [Lambda.iterate];
  simp +decide [ List.range_succ ]

theorem Lambda.church_eq_iterate (n : ℕ) : Lambda.church n = Lambda.lam (Lambda.lam (Lambda.iterate
    (Lambda.var 1) (Lambda.var 0) n)) := rfl

theorem Lambda.lift_church (n k m : ℕ) : Lambda.lift n k (Lambda.church m) = Lambda.church m := by
  rw [Lambda.church_eq_iterate]
  change Lambda.lam
      (Lambda.lam (Lambda.lift n (k + 2) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m))) =
    Lambda.lam (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.var 0) m))
  congr 1
  congr 1
  have h0 : 0 < k + 2 := by omega
  have h1 : 1 < k + 2 := by omega
  induction m with
  | zero =>
      simp [Lambda.iterate_zero, Lambda.lift, h0]
  | succ m ih =>
      simpa [Lambda.iterate, List.range_succ, Lambda.lift, h1] using
        congrArg (fun t => Lambda.app (Lambda.var 1) t) ih

/-
Substitution distributes over `Lambda.iterate`.
-/
theorem Lambda.subst_iterate (s : Lambda) (k : ℕ) (f x : Lambda) (n : ℕ) :
  Lambda.subst s k (Lambda.iterate f x n) = Lambda.iterate (Lambda.subst s k f) (Lambda.subst s k x)
      n := by
  unfold Lambda.iterate
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      simp_all +decide only [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rw [← ih, Lambda.subst]

/-
`Lambda.church n` applied to `f` and `x` reduces to `iterate (subst x 0 f) x n`.
-/
theorem Lambda.church_reduces_iterate (n : ℕ) (f x : Lambda) :
  Lambda.reduces (Lambda.app (Lambda.app (Lambda.church n) f) x) (Lambda.iterate f x n) := by
  have h1 :
      Lambda.reduces
        (Lambda.app (Lambda.lam (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n))) f)
        (Lambda.lam (Lambda.iterate (Lambda.lift 1 0 f) (Lambda.var 0) n)) := by
    have h1 :
        Lambda.reduces
          (Lambda.app (Lambda.lam (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n))) f)
          (Lambda.subst f 0 (Lambda.lam (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n))) := by
      exact Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (Lambda.reduces.refl _)
    have h_subst_iterate :
        Lambda.subst (Lambda.lift 1 0 f) 1 (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n) =
          Lambda.iterate (Lambda.lift 1 0 f) (Lambda.var 0) n := by
      simpa [Lambda.subst] using
        (Lambda.subst_iterate (Lambda.lift 1 0 f) 1 (Lambda.var 1) (Lambda.var 0) n)
    convert h1 using 1
    simp [Lambda.subst, h_subst_iterate]
  have h2 :
      Lambda.reduces
        (Lambda.app (Lambda.lam (Lambda.iterate (Lambda.lift 1 0 f) (Lambda.var 0) n)) x)
        (Lambda.iterate f x n) := by
    have h2 :
        Lambda.reduces
          (Lambda.app (Lambda.lam (Lambda.iterate (Lambda.lift 1 0 f) (Lambda.var 0) n)) x)
          (Lambda.subst x 0 (Lambda.iterate (Lambda.lift 1 0 f) (Lambda.var 0) n)) := by
      exact Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (Lambda.reduces.refl _)
    have h_subst_lift : Lambda.subst x 0 (Lambda.lift 1 0 f) = f := by
      simpa using (Lambda.subst_lift f x 0)
    convert h2 using 1
    simpa [Lambda.subst, h_subst_lift] using
      (Lambda.subst_iterate x 0 (Lambda.lift 1 0 f) (Lambda.var 0) n).symm
  have h_trans :
      ∀ t₁ t₂ t₃,
        Lambda.reduces t₁ t₂ →
          Lambda.reduces (Lambda.app t₂ x) t₃ →
            Lambda.reduces (Lambda.app t₁ x) t₃ := by
    intro t₁ t₂ t₃ h₁ h₂
    induction h₁ with
    | refl _ => exact h₂
    | step _ _ _ hstep _ ih =>
        exact Lambda.reduces.step _ _ _ (Lambda.step.app_left _ _ _ hstep) (ih h₂)
  exact h_trans _ _ _ h1 h2


/-
A lemma stating that a beta reduction step implies reduction in the reflexive transitive closure.
-/
theorem Lambda.beta_reduces {t1 t2 : Lambda} :
  Lambda.reduces (Lambda.app (Lambda.lam t1) t2) (Lambda.subst t2 0 t1) :=
  Lambda.reduces.step _ _ _ (Lambda.step.beta t1 t2) (Lambda.reduces.refl _)

/-
The identity combinator `I` reduces its argument to itself.
-/
theorem Lambda.I_works (x : Lambda) : Lambda.reduces (Lambda.app Lambda.I x) x := by
  -- By definition of `Lambda.reduces`, we know that if `t₁` reduces to `t₂`, then `t₁` reduces to
  -- `t₂`.
  apply Lambda.beta_reduces

/-
`Lambda.succ (church n)` reduces to `\f x. f (church n f x)`.
-/
theorem Lambda.succ_reduces_step1 (n : ℕ) :
  Lambda.reduces (Lambda.app Lambda.succ (Lambda.church n))
    (Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.app (Lambda.church n)
        (Lambda.var 1)) (Lambda.var 0))))) := by
  have h_body_lift :
      Lambda.lift 1 2 ((List.range n).foldl (fun t _ => Lambda.app (Lambda.var 1) t) (Lambda.var 0))
          =
        (List.range n).foldl (fun t _ => Lambda.app (Lambda.var 1) t) (Lambda.var 0) := by
    induction n with
    | zero =>
        simp [Lambda.lift]
    | succ n ih =>
        simp [List.range_succ, ih, Lambda.lift]
  simpa [Lambda.succ, Lambda.church, Lambda.subst, Lambda.lift, h_body_lift] using
    (Lambda.beta_reduces
      (t1 := Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.app (Lambda.var
          2) (Lambda.var 1)) (Lambda.var 0))))
      )
      (t2 := Lambda.church n))

/-
Substituting `s` for `x` in `var x` yields `s`.
-/
theorem Lambda.subst_var_eq (s : Lambda) (x : ℕ) : Lambda.subst s x (Lambda.var x) = s := by
  exact if_pos rfl

/-
Substituting `s` for `x` in `var y` yields `var y` when `y < x`.
-/
theorem Lambda.subst_var_ne (s : Lambda) (x y : ℕ) (h : y < x) :
    Lambda.subst s x (Lambda.var y) = Lambda.var y := by
  have hne : y ≠ x := ne_of_lt h
  have hngt : ¬ y > x := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [Lambda.subst, hne, hngt]


/-
`church n` applied to `var 1` and `var 0` reduces to `iterate (var 1) (var 0) n`.
-/
theorem Lambda.succ_reduces_step2 (n : ℕ) :
  Lambda.reduces (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1)) (Lambda.var 0))
                 (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n) := by
  exact Lambda.church_reduces_iterate n (Lambda.var 1) (Lambda.var 0)

/-
The Lambda term `Lambda.succ` correctly increments a Church numeral.
-/
theorem Lambda.succ_works (n : ℕ) :
    Lambda.reduces (Lambda.app Lambda.succ (Lambda.church n)) (Lambda.church (n + 1)) := by
  -- First, use `Lambda.succ_reduces_step1` to show that the term reduces to the intermediate form.
  have h1 : Lambda.reduces (Lambda.app Lambda.succ (Lambda.church n)) (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.app (Lambda.church n) (Lambda.var 1))
      (Lambda.var 0))))) := by
    exact Lambda.succ_reduces_step1 n;
  -- Apply `Lambda.succ_reduces_step2` to show that the intermediate form reduces to the final form.
  have h2 : Lambda.reduces (Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app
      (Lambda.app (Lambda.church n) (Lambda.var 1)) (Lambda.var 0))))) (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n)))) := by
    apply_rules [ Lambda.reduces_lam, Lambda.reduces_app_right ];
    exact Lambda.succ_reduces_step2 n;
  -- By transitivity of reduction, we can combine h1 and h2 to conclude the proof.
  have h_trans : Lambda.reduces (Lambda.app Lambda.succ (Lambda.church n)) (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 1) (Lambda.iterate (Lambda.var 1) (Lambda.var 0) n)))) := by
    have h_trans : ∀ (t1 t2 t3 : Lambda), Lambda.reduces t1 t2 → Lambda.reduces t2 t3 →
        Lambda.reduces t1 t3 := by
      intros t1 t2 t3 h1 h2;
      induction h1 <;> tauto;
    exact h_trans _ _ _ h1 h2;
  convert h_trans using 1;
  -- By definition of `Lambda.church`, we know that `Lambda.church (n + 1)` is the abstraction of
  -- the iteration of `var 1` and `var 0` `n + 1` times.
  simp [Lambda.church, Lambda.iterate];
  simp ( config := { decide := Bool.true } ) [ List.range_succ ]

/-
The Lambda term `Lambda.succ` correctly increments a Church numeral.
-/
theorem Lambda.succ_correct (n : ℕ) :
    Lambda.reduces (Lambda.app Lambda.succ (Lambda.church n)) (Lambda.church (n + 1)) := by
  exact Lambda.succ_works n

end
