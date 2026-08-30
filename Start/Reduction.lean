/-
Reduction theory: single-step, parallel, multi-step reduction.
Diamond property, strip lemma, confluence (Church-Rosser).
Church numerals, combinators, LambdaComputable.
Extracted from Start/Basic.lean following LACI-style modularization.
-/

import Start.Syntax
import Mathlib.Computability.Partrec

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section


------------------------------------------------------------------------
-- Single-step and parallel reduction
------------------------------------------------------------------------

/-- Single-step beta reduction -/
inductive Lambda.step : Lambda → Lambda → Prop
  | beta (t₁ t₂ : Lambda) : Lambda.step (Lambda.app (Lambda.lam t₁) t₂) (Lambda.subst t₂ 0 t₁)
  | app_left (t₁ t₁' t₂ : Lambda) :
      Lambda.step t₁ t₁' → Lambda.step (Lambda.app t₁ t₂) (Lambda.app t₁' t₂)
  | app_right (t₁ t₂ t₂' : Lambda) :
      Lambda.step t₂ t₂' → Lambda.step (Lambda.app t₁ t₂) (Lambda.app t₁ t₂')
  | lam (t t' : Lambda) : Lambda.step t t' → Lambda.step (Lambda.lam t) (Lambda.lam t')

/-- Parallel reduction: allows multiple reductions in one step. -/
inductive Lambda.step_p : Lambda → Lambda → Prop
  | var (n : ℕ) : Lambda.step_p (Lambda.var n) (Lambda.var n)
  | lam (t t' : Lambda) : Lambda.step_p t t' → Lambda.step_p (Lambda.lam t) (Lambda.lam t')
  | app (t₁ t₁' t₂ t₂' : Lambda) : Lambda.step_p t₁ t₁' → Lambda.step_p t₂ t₂' →
      Lambda.step_p (Lambda.app t₁ t₂) (Lambda.app t₁' t₂')
  | beta (t₁ t₁' t₂ t₂' : Lambda) : Lambda.step_p t₁ t₁' → Lambda.step_p t₂ t₂' →
      Lambda.step_p (Lambda.app (Lambda.lam t₁) t₂) (Lambda.subst t₂' 0 t₁')

/-- Parallel reduction is reflexive. -/
theorem Lambda.step_p_refl (t : Lambda) : Lambda.step_p t t := by
  induction t with
  | var n => exact Lambda.step_p.var n
  | lam t ih => exact Lambda.step_p.lam t t ih
  | app t1 t2 ih1 ih2 => exact Lambda.step_p.app t1 t1 t2 t2 ih1 ih2

/-- Every single-step reduction is also a parallel reduction. -/
theorem Lambda.step_imp_step_p {t t' : Lambda} (h : Lambda.step t t') : Lambda.step_p t t' := by
  induction h with
  | beta t1 t2 => exact Lambda.step_p.beta t1 t1 t2 t2 (Lambda.step_p_refl t1)
                    (Lambda.step_p_refl t2)
  | app_left t1 t1' t2 h ih => exact Lambda.step_p.app t1 t1' t2 t2 ih (Lambda.step_p_refl t2)
  | app_right t1 t2 t2' h ih => exact Lambda.step_p.app t1 t1 t2 t2' (Lambda.step_p_refl t1) ih
  | lam t t' h ih => exact Lambda.step_p.lam t t' ih

------------------------------------------------------------------------
-- Church numerals
------------------------------------------------------------------------

/-- Church numeral for n -/
def Lambda.church (n : ℕ) : Lambda :=
  let f := Lambda.var 1
  let x := Lambda.var 0
  let body := (List.range n).foldl (fun t _ => Lambda.app f t) x
  Lambda.lam (Lambda.lam body)

------------------------------------------------------------------------
-- Reflexive-transitive closure
------------------------------------------------------------------------

/-- Reflexive transitive closure of reduction -/
inductive Lambda.reduces : Lambda → Lambda → Prop
  | refl (t : Lambda) : Lambda.reduces t t
  | step (t₁ t₂ t₃ : Lambda) : Lambda.step t₁ t₂ → Lambda.reduces t₂ t₃ → Lambda.reduces t₁ t₃

/-- Transitivity of reduces. -/
theorem Lambda.reduces_trans {t1 t2 t3 : Lambda} (h1 : Lambda.reduces t1 t2) (h2 : Lambda.reduces t2
    t3) : Lambda.reduces t1 t3 := by
  induction h1 with
  | refl => exact h2
  | step t1 t2 t2' h_step _ ih => exact Lambda.reduces.step t1 t2 t3 h_step (ih h2)

------------------------------------------------------------------------
-- Parallel reduction lemmas
------------------------------------------------------------------------

/-- Parallel reduction is preserved under lifting. -/
theorem Lambda.step_p_lift {t t' : Lambda} (h : Lambda.step_p t t') (n k : ℕ) :
    Lambda.step_p (Lambda.lift n k t) (Lambda.lift n k t') := by
  induction h generalizing n k with
  | var m =>
      by_cases hmk : m < k
      · simp [Lambda.lift, hmk, Lambda.step_p.var]
      · simp [Lambda.lift, hmk, Lambda.step_p.var]
  | lam t t' h ih =>
      simpa [Lambda.lift] using Lambda.step_p.lam _ _ (ih n (k + 1))
  | app t1 t1' t2 t2' h1 h2 ih1 ih2 =>
      simpa [Lambda.lift] using Lambda.step_p.app _ _ _ _ (ih1 n k) (ih2 n k)
  | beta t1 t1' t2 t2' h1 h2 ih1 ih2 =>
      rw [Lambda.lift_subst_zero t1' t2' n k]
      exact Lambda.step_p.beta _ _ _ _ (ih1 n (k + 1)) (ih2 n k)

/-- Substitution lemma for parallel reduction. -/
theorem Lambda.step_p_subst {t t' s s' : Lambda} (ht : Lambda.step_p t t') (hs : Lambda.step_p s s')
    (x : ℕ) :
    Lambda.step_p (Lambda.subst s x t) (Lambda.subst s' x t') := by
  induction ht generalizing x s s' with
  | var y =>
    simp only [Lambda.subst]
    split_ifs <;> first | exact hs | exact Lambda.step_p.var _
  | lam t1 t1' _ ih =>
    simp only [Lambda.subst]
    exact Lambda.step_p.lam _ _ (ih (Lambda.step_p_lift hs 1 0) (x + 1))
  | app t1 t1' t2 t2' _ _ ih1 ih2 =>
    simp only [Lambda.subst]
    exact Lambda.step_p.app _ _ _ _ (ih1 hs x) (ih2 hs x)
  | beta t1 t1' t2 t2' _ _ ih1 ih2 =>
    simp only [Lambda.subst]
    rw [Lambda.subst_subst_zero _ _ _ x]
    exact Lambda.step_p.beta _ _ _ _ (ih1 (Lambda.step_p_lift hs 1 0) (x + 1)) (ih2 hs x)

------------------------------------------------------------------------
-- Full development (rho) and diamond property
------------------------------------------------------------------------

/-- Full development function: reduces all current redexes. -/
def Lambda.rho : Lambda → Lambda
  | Lambda.var n => Lambda.var n
  | Lambda.lam t => Lambda.lam (Lambda.rho t)
  | Lambda.app (Lambda.lam t₁) t₂ => Lambda.subst (Lambda.rho t₂) 0 (Lambda.rho t₁)
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.rho t₁) (Lambda.rho t₂)

/-- Every term parallel-reduces to its full development. -/
theorem Lambda.step_p_rho (t : Lambda) : Lambda.step_p t (Lambda.rho t) := by
  induction t with
  | var n =>
      exact Lambda.step_p.var n
  | lam t ih =>
      simpa [Lambda.rho] using Lambda.step_p.lam t (Lambda.rho t) ih
  | app t1 t2 ih1 ih2 =>
      cases t1 with
      | var n =>
          simpa [Lambda.rho] using
            (Lambda.step_p.app (Lambda.var n) (Lambda.var n) t2 (Lambda.rho t2) (Lambda.step_p.var
                n) ih2)
      | app u v =>
          simpa [Lambda.rho] using
            (Lambda.step_p.app (Lambda.app u v) (Lambda.rho (Lambda.app u v)) t2 (Lambda.rho t2) ih1
                ih2)
      | lam u =>
          cases ih1 with
          | lam _ _ ihu =>
              simpa [Lambda.rho] using
                (Lambda.step_p.beta u (Lambda.rho u) t2 (Lambda.rho t2) ihu ih2)

/-- Triangle: every parallel reduct of t further reduces to rho(t). -/
theorem Lambda.step_p_diamond_aux {t t' : Lambda} (h : Lambda.step_p t t') :
    Lambda.step_p t' (Lambda.rho t) := by
  induction h with
  | var n =>
      exact Lambda.step_p.var n
  | lam t t' h ih =>
      simpa [Lambda.rho] using Lambda.step_p.lam _ _ ih
  | app t1 t1' t2 t2' h1 h2 ih1 ih2 =>
      cases t1 with
      | var n =>
          simpa [Lambda.rho] using
            (Lambda.step_p.app t1' (Lambda.rho (Lambda.var n)) t2' (Lambda.rho t2) ih1 ih2)
      | app u v =>
          simpa [Lambda.rho] using
            (Lambda.step_p.app t1' (Lambda.rho (Lambda.app u v)) t2' (Lambda.rho t2) ih1 ih2)
      | lam u =>
          cases h1 with
          | lam _ u' hu =>
              cases ih1 with
              | lam _ _ ihu =>
                  simpa [Lambda.rho] using
                    (Lambda.step_p.beta u' (Lambda.rho u) t2' (Lambda.rho t2) ihu ih2)
  | beta t1 t1' t2 t2' h1 h2 ih1 ih2 =>
      simpa [Lambda.rho] using Lambda.step_p_subst ih1 ih2 0

/-- Diamond property of parallel reduction. -/
theorem Lambda.step_p_diamond {t t1 t2 : Lambda} (h1 : Lambda.step_p t t1) (h2 : Lambda.step_p t t2)
    :
    ∃ t3, Lambda.step_p t1 t3 ∧ Lambda.step_p t2 t3 := by
  use Lambda.rho t
  exact ⟨Lambda.step_p_diamond_aux h1, Lambda.step_p_diamond_aux h2⟩

------------------------------------------------------------------------
-- Congruence for reduces
------------------------------------------------------------------------

theorem Lambda.reduces_app_left {t1 t1' t2 : Lambda} (h : Lambda.reduces t1 t1') :
    Lambda.reduces (Lambda.app t1 t2) (Lambda.app t1' t2) := by
  induction h with
  | refl => exact Lambda.reduces.refl _
  | step _ _ _ hs _ ih => exact Lambda.reduces.step _ _ _ (Lambda.step.app_left _ _ _ hs) ih

theorem Lambda.reduces_app_right {t1 t2 t2' : Lambda} (h : Lambda.reduces t2 t2') :
    Lambda.reduces (Lambda.app t1 t2) (Lambda.app t1 t2') := by
  induction h with
  | refl => exact Lambda.reduces.refl _
  | step _ _ _ hs _ ih => exact Lambda.reduces.step _ _ _ (Lambda.step.app_right _ _ _ hs) ih

/-- Congruence of `reduces` for applications, in both arguments simultaneously. -/
theorem Lambda.reduces_app {t1 t1' t2 t2' : Lambda} (h1 : Lambda.reduces t1 t1')
    (h2 : Lambda.reduces t2 t2') : Lambda.reduces (Lambda.app t1 t2) (Lambda.app t1' t2') :=
  Lambda.reduces_trans (Lambda.reduces_app_left h1) (Lambda.reduces_app_right h2)

theorem Lambda.reduces_lam {t t' : Lambda} (h : Lambda.reduces t t') :
    Lambda.reduces (Lambda.lam t) (Lambda.lam t') := by
  induction h with
  | refl => exact Lambda.reduces.refl _
  | step _ _ _ hs _ ih => exact Lambda.reduces.step _ _ _ (Lambda.step.lam _ _ hs) ih

/-- Parallel reduction implies standard reduction. -/
theorem Lambda.step_p_imp_reduces {t t' : Lambda} (h : Lambda.step_p t t') :
    Lambda.reduces t t' := by
  induction h with
  | var n =>
      exact Lambda.reduces.refl _
  | lam t t' h ih =>
      exact Lambda.reduces_lam ih
  | app t1 t1' t2 t2' h1 h2 ih1 ih2 =>
      exact Lambda.reduces_trans (Lambda.reduces_app_left ih1) (Lambda.reduces_app_right ih2)
  | beta t1 t1' t2 t2' h1 h2 ih1 ih2 =>
      have h_lam : Lambda.reduces (Lambda.lam t1) (Lambda.lam t1') := Lambda.reduces_lam ih1
      have h_app1 :
          Lambda.reduces (Lambda.app (Lambda.lam t1) t2) (Lambda.app (Lambda.lam t1') t2) := by
        exact Lambda.reduces_app_left h_lam
      have h_app2 :
          Lambda.reduces (Lambda.app (Lambda.lam t1') t2) (Lambda.app (Lambda.lam t1') t2') := by
        exact Lambda.reduces_app_right ih2
      have h_beta :
          Lambda.reduces (Lambda.app (Lambda.lam t1') t2') (Lambda.subst t2' 0 t1') := by
        exact Lambda.reduces.step
          (Lambda.app (Lambda.lam t1') t2')
          (Lambda.subst t2' 0 t1')
          (Lambda.subst t2' 0 t1')
          (Lambda.step.beta t1' t2')
          (Lambda.reduces.refl _)
      exact Lambda.reduces_trans h_app1 (Lambda.reduces_trans h_app2 h_beta)

/-- Reduction is preserved by lifting. -/
theorem Lambda.reduces_lift {t t' : Lambda} (h : Lambda.reduces t t') (n k : ℕ) :
    Lambda.reduces (Lambda.lift n k t) (Lambda.lift n k t') := by
  induction h with
  | refl t => exact Lambda.reduces.refl _
  | step _ _ _ hs _ ih =>
      exact Lambda.reduces_trans
        (Lambda.step_p_imp_reduces (Lambda.step_p_lift (Lambda.step_imp_step_p hs) n k)) ih

------------------------------------------------------------------------
-- Strip lemma and confluence
------------------------------------------------------------------------

theorem Lambda.step_p_confluence {t t1 t2 : Lambda} (h1 : Lambda.step_p t t1) (h2 : Lambda.step_p t
    t2) :
    ∃ t3, Lambda.step_p t1 t3 ∧ Lambda.step_p t2 t3 :=
  Lambda.step_p_diamond h1 h2

/-- Strip lemma. -/
theorem Lambda.strip_lemma {t t1 t2 : Lambda} (hp : Lambda.step_p t t1) (hr : Lambda.reduces t t2) :
    ∃ t3, Lambda.reduces t1 t3 ∧ Lambda.step_p t2 t3 := by
  induction hr generalizing t1 with
  | refl =>
      exact ⟨t1, Lambda.reduces.refl t1, hp⟩
  | step t t' t2 hs hr' ih =>
      have hp' := Lambda.step_imp_step_p hs
      obtain ⟨u, hu1, hu2⟩ := Lambda.step_p_diamond hp hp'
      obtain ⟨t3, ht3_red, ht3_p⟩ := ih (t1 := u) hu2
      exact ⟨t3, Lambda.reduces_trans (Lambda.step_p_imp_reduces hu1) ht3_red, ht3_p⟩

def Lambda.Confluence : Prop :=
  ∀ {t t1 t2 : Lambda}, Lambda.reduces t t1 → Lambda.reduces t t2 → ∃ t3, Lambda.reduces t1 t3 ∧
      Lambda.reduces t2 t3

/-- Confluence of Lambda calculus (Church-Rosser theorem). -/
theorem Lambda.confluence_theorem : Lambda.Confluence := by
  unfold Lambda.Confluence
  intro t t1 t2 h1 h2
  induction h1 generalizing t2 with
  | refl =>
      exact ⟨t2, h2, Lambda.reduces.refl t2⟩
  | step t t' t1 hs hr ih =>
      have hp := Lambda.step_imp_step_p hs
      obtain ⟨u, hu_red, hu_p⟩ := Lambda.strip_lemma hp h2
      obtain ⟨t3, ht3_1, ht3_2⟩ := ih (t2 := u) hu_red
      exact ⟨t3, ht3_1, Lambda.reduces_trans (Lambda.step_p_imp_reduces hu_p) ht3_2⟩

------------------------------------------------------------------------
-- Computability definition
------------------------------------------------------------------------

/-- A partial function f : ℕ →. ℕ is Lambda-computable if there exists a term F such that
    for all n, if f(n) is defined and equals m, then F (church n) reduces to (church m). -/
def LambdaComputable (f : ℕ →. ℕ) : Prop :=
  ∃ F : Lambda, ∀ n m, f n = Part.some m ↔ Lambda.reduces (Lambda.app F (Lambda.church n))
      (Lambda.church m)

------------------------------------------------------------------------
-- Standard combinators
------------------------------------------------------------------------

def Lambda.I : Lambda := Lambda.lam (Lambda.var 0)
def Lambda.K : Lambda := Lambda.lam (Lambda.lam (Lambda.var 1))
def Lambda.S : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 0))
      (Lambda.app (Lambda.var 1) (Lambda.var 0)))))

def Lambda.pair : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.app (Lambda.var 0) (Lambda.var 2))
      (Lambda.var 1))))
def Lambda.fst : Lambda :=
  Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.lam (Lambda.var 1))))
def Lambda.snd : Lambda :=
  Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.lam (Lambda.var 0))))

def Lambda.succ : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.app (Lambda.var
      2) (Lambda.var 1)) (Lambda.var 0)))))

/-- Y combinator: λ f. (λ x. f (x x)) (λ x. f (x x)) -/
def Lambda.fix : Lambda :=
  let omega := Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.var 0) (Lambda.var 0)))
  Lambda.lam (Lambda.app omega omega)

end
