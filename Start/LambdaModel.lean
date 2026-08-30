/-
Abstract λ-models (Meyer–Scott / Hindley–Longo environment models).

The library develops three models of the untyped λ-calculus independently — Scott's graph
model `𝒫ω` (`Start/GraphModelSemantics.lean`), Scott's inverse limit `D∞`
(`Start/ScottDinfModel.lean`) and the filter model of the intersection type system
(`Start/FilterModel.lean`) — each with its own interpretation function and its own soundness
proof.  This file introduces the notion those three developments are instances of.

A **λ-model** is a set `D` with a binary application and an interpretation `⟦t⟧ρ` of the untyped
terms in environments `ρ : ℕ → D` satisfying four axioms:

* `interp_var`, `interp_app` — the interpretation is compositional on variables and application;
* `interp_beta` — `⟦λt⟧ρ · d = ⟦t⟧(d :: ρ)`, i.e. an abstraction applies as its body;
* `interp_lam_ext` — **weak extensionality** (the Meyer–Scott axiom, the rule `ξ`): the value of
  an abstraction depends on its body only through the function `d ↦ ⟦t⟧(d :: ρ)`.

Everything else is derived here, once and for all, from those axioms:

* `Lambda.LambdaModel.interp_lift`, `Lambda.LambdaModel.interp_subst` — the lifting and
  substitution lemmas;
* `Lambda.LambdaModel.interp_step`, `..._reduces`, `..._conv` — **soundness for β**;
* `Lambda.LambdaModel.interp_congr_below`, `..._interp_closed` — the interpretation only depends
  on the environment at the free variables;
* `Lambda.LambdaModel.K`, `.S`, `.eps` and the equations `app_app_K`, `app_app_app_S`,
  `app_app_eps`, `eps_ext`, `app_eps_eps` — every λ-model is a **combinatory algebra** satisfying
  the Meyer–Scott axioms for the "extensionality operator" `ε = λxy.xy`;
* `Lambda.LambdaModel.IsExtensional` and `interp_eta_of_extensional` — extensional models are
  exactly those validating η.
-/

import Start.Scott
import Start.FreeVars

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Lambda

/-- Extend an environment of an arbitrary carrier with a new value for the index `0`. -/
def modelCons {D : Type u} (d : D) (ρ : ℕ → D) : ℕ → D
  | 0 => d
  | (i + 1) => ρ i

@[simp] theorem modelCons_zero {D : Type u} (d : D) (ρ : ℕ → D) : modelCons d ρ 0 = d := rfl
@[simp] theorem modelCons_succ {D : Type u} (d : D) (ρ : ℕ → D) (i : ℕ) :
    modelCons d ρ (i + 1) = ρ i := rfl

/-- A **λ-model** in the sense of Meyer and Scott (an *environment model* in the sense of
Hindley–Longo): an applicative structure together with an interpretation of the untyped terms
which is compositional, satisfies β at the level of application, and is weakly extensional. -/
structure LambdaModel where
  /-- The underlying set of the model. -/
  Carrier : Type u
  /-- Application. -/
  app : Carrier → Carrier → Carrier
  /-- A λ-model is nonempty. -/
  nonempty : Nonempty Carrier
  /-- The interpretation of a term in an environment. -/
  interp : Lambda → (ℕ → Carrier) → Carrier
  /-- A variable denotes its value in the environment. -/
  interp_var : ∀ (i : ℕ) (ρ : ℕ → Carrier), interp (Lambda.var i) ρ = ρ i
  /-- Application is interpreted by the application of the model. -/
  interp_app : ∀ (s t : Lambda) (ρ : ℕ → Carrier),
    interp (Lambda.app s t) ρ = app (interp s ρ) (interp t ρ)
  /-- β: applying an abstraction is evaluating its body in the extended environment. -/
  interp_beta : ∀ (t : Lambda) (ρ : ℕ → Carrier) (d : Carrier),
    app (interp (Lambda.lam t) ρ) d = interp t (modelCons d ρ)
  /-- **Weak extensionality** (the Meyer–Scott axiom): the value of an abstraction depends only
  on the function computed by its body. -/
  interp_lam_ext : ∀ (t t' : Lambda) (ρ ρ' : ℕ → Carrier),
    (∀ d : Carrier, interp t (modelCons d ρ) = interp t' (modelCons d ρ')) →
      interp (Lambda.lam t) ρ = interp (Lambda.lam t') ρ'

namespace LambdaModel

variable (M : LambdaModel.{u})

/-- A default environment, available because the carrier of a λ-model is nonempty. -/
noncomputable def env0 : ℕ → M.Carrier := fun _ => Classical.choice M.nonempty

/-- Weak extensionality for one and the same body. -/
theorem interp_lam_congr_env (t : Lambda) (ρ ρ' : ℕ → M.Carrier)
    (h : ∀ d : M.Carrier, M.interp t (modelCons d ρ) = M.interp t (modelCons d ρ')) :
    M.interp (Lambda.lam t) ρ = M.interp (Lambda.lam t) ρ' :=
  M.interp_lam_ext t t ρ ρ' h

/-! ### The lifting and substitution lemmas -/

/-- The lifting lemma: lifting a term shifts the environment. -/
theorem interp_lift : ∀ (t : Lambda) (k : ℕ) (ρ : ℕ → M.Carrier),
    M.interp (Lambda.lift 1 k t) ρ = M.interp t (fun i => if i < k then ρ i else ρ (i + 1)) := by
  intro t
  induction t with
  | var y =>
      intro k ρ
      by_cases hy : y < k <;> simp [Lambda.lift, hy, M.interp_var]
  | app s u ihs ihu =>
      intro k ρ
      simp only [Lambda.lift, M.interp_app, ihs, ihu]
  | lam s ih =>
      intro k ρ
      refine M.interp_lam_ext _ _ _ _ ?_
      intro d
      rw [ih (k + 1) (modelCons d ρ)]
      congr 1
      funext i
      cases i with
      | zero => simp
      | succ j =>
          by_cases hj : j < k
          · simp [hj, Nat.succ_lt_succ hj]
          · have : ¬ (j + 1 < k + 1) := by omega
            simp [hj, this]

/-- Lifting at `0` inserts a dummy value at the front of the environment. -/
theorem interp_lift_zero (t : Lambda) (ρ : ℕ → M.Carrier) (d : M.Carrier) :
    M.interp (Lambda.lift 1 0 t) (modelCons d ρ) = M.interp t ρ := by
  rw [interp_lift]
  congr 1

/-- The substitution lemma: substitution is evaluation in the modified environment. -/
theorem interp_subst : ∀ (t s : Lambda) (x : ℕ) (ρ : ℕ → M.Carrier),
    M.interp (Lambda.subst s x t) ρ =
      M.interp t (fun i => if i = x then M.interp s ρ else if x < i then ρ (i - 1) else ρ i) := by
  intro t
  induction t with
  | var y =>
      intro s x ρ
      rcases lt_trichotomy y x with hy | hy | hy
      · have h1 : ¬ (y = x) := by omega
        have h2 : ¬ (x < y) := by omega
        simp [Lambda.subst, h1, h2, M.interp_var]
      · subst hy
        simp [Lambda.subst, M.interp_var]
      · have h1 : ¬ (y = x) := by omega
        simp [Lambda.subst, h1, hy, M.interp_var]
  | app a b iha ihb =>
      intro s x ρ
      simp only [Lambda.subst, M.interp_app, iha, ihb]
  | lam a ih =>
      intro s x ρ
      refine M.interp_lam_ext _ _ _ _ ?_
      intro d
      rw [ih (Lambda.lift 1 0 s) (x + 1) (modelCons d ρ), interp_lift_zero]
      congr 1
      funext i
      cases i with
      | zero => simp
      | succ j =>
          by_cases hj : j = x
          · subst hj; simp
          · have h1 : ¬ (j + 1 = x + 1) := by omega
            by_cases hj' : x < j
            · have h2 : x + 1 < j + 1 := by omega
              have h3 : ¬ (j = 0) := by omega
              cases j with
              | zero => omega
              | succ m => simp [h2, hj']
            · have h2 : ¬ (x + 1 < j + 1) := by omega
              simp [h2, hj']

/-- The semantic β-rule. -/
theorem interp_beta_subst (t u : Lambda) (ρ : ℕ → M.Carrier) :
    M.interp (Lambda.app (Lambda.lam t) u) ρ = M.interp (Lambda.subst u 0 t) ρ := by
  rw [M.interp_app, M.interp_beta, interp_subst]
  congr 1
  funext i
  cases i with
  | zero => simp
  | succ j => simp

/-! ### Soundness -/

/-- **Soundness for one β-step.** -/
theorem interp_step : ∀ {t t' : Lambda}, Lambda.step t t' →
    ∀ ρ : ℕ → M.Carrier, M.interp t ρ = M.interp t' ρ := by
  intro t t' h
  induction h with
  | beta a b => intro ρ; exact interp_beta_subst M a b ρ
  | app_left a a' b _ ih => intro ρ; simp only [M.interp_app, ih ρ]
  | app_right a b b' _ ih => intro ρ; simp only [M.interp_app, ih ρ]
  | lam a a' _ ih =>
      intro ρ
      exact M.interp_lam_ext _ _ _ _ fun d => ih (modelCons d ρ)

/-- **Soundness for β-reduction.** -/
theorem interp_reduces {t t' : Lambda} (h : Lambda.reduces t t') (ρ : ℕ → M.Carrier) :
    M.interp t ρ = M.interp t' ρ := by
  induction h with
  | refl a => rfl
  | step a b c hab _ ih => exact (interp_step M hab ρ).trans (ih)

/-- **Soundness for β-conversion**: every λ-model is a model of the β-calculus. -/
theorem interp_conv {t t' : Lambda} (h : Conv t t') (ρ : ℕ → M.Carrier) :
    M.interp t ρ = M.interp t' ρ := by
  obtain ⟨u, h₁, h₂⟩ := h
  exact (interp_reduces M h₁ ρ).trans (interp_reduces M h₂ ρ).symm

/-! ### Dependence on the free variables only -/

/-- The interpretation depends on the environment only at the free variables. -/
theorem interp_congr_below : ∀ (t : Lambda) (k : ℕ), Lambda.freeBelow k t →
    ∀ ρ ρ' : ℕ → M.Carrier, (∀ i < k, ρ i = ρ' i) → M.interp t ρ = M.interp t ρ' := by
  intro t
  induction t with
  | var y =>
      intro k hk ρ ρ' h
      rw [M.interp_var, M.interp_var, h y hk]
  | app a b iha ihb =>
      intro k hk ρ ρ' h
      rw [M.interp_app, M.interp_app, iha k hk.1 ρ ρ' h, ihb k hk.2 ρ ρ' h]
  | lam a ih =>
      intro k hk ρ ρ' h
      refine M.interp_lam_ext _ _ _ _ fun d => ih (k + 1) hk _ _ ?_
      intro i hi
      cases i with
      | zero => rfl
      | succ j => exact h j (by omega)

/-- The interpretation of a closed term does not depend on the environment. -/
theorem interp_closed {t : Lambda} (ht : Lambda.freeBelow 0 t) (ρ ρ' : ℕ → M.Carrier) :
    M.interp t ρ = M.interp t ρ' :=
  interp_congr_below M t 0 ht ρ ρ' (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-! ### Every λ-model is a combinatory algebra -/

/-- The combinator `K = λxy.x` of the model. -/
def K (ρ : ℕ → M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.lam (Lambda.var 1))) ρ

/-- The combinator `S = λxyz. xz(yz)` of the model. -/
def S (ρ : ℕ → M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.lam (Lambda.lam
    (Lambda.app (Lambda.app (Lambda.var 2) (Lambda.var 0))
      (Lambda.app (Lambda.var 1) (Lambda.var 0)))))) ρ

/-- The Meyer–Scott extensionality operator `ε = λxy. xy` of the model. -/
def eps (ρ : ℕ → M.Carrier) : M.Carrier :=
  M.interp (Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.var 0)))) ρ

theorem app_app_K (ρ : ℕ → M.Carrier) (x y : M.Carrier) :
    M.app (M.app (M.K ρ) x) y = x := by
  rw [K, M.interp_beta, M.interp_beta, M.interp_var]
  rfl

theorem app_app_app_S (ρ : ℕ → M.Carrier) (x y z : M.Carrier) :
    M.app (M.app (M.app (M.S ρ) x) y) z = M.app (M.app x z) (M.app y z) := by
  rw [S, M.interp_beta, M.interp_beta, M.interp_beta, M.interp_app, M.interp_app, M.interp_app,
    M.interp_var, M.interp_var, M.interp_var]
  rfl

theorem app_app_eps (ρ : ℕ → M.Carrier) (x y : M.Carrier) :
    M.app (M.app (M.eps ρ) x) y = M.app x y := by
  rw [eps, M.interp_beta, M.interp_beta, M.interp_app, M.interp_var, M.interp_var]
  rfl

/-- **The Meyer–Scott axiom**: `ε` identifies elements with the same applicative behaviour. -/
theorem eps_ext (ρ : ℕ → M.Carrier) {x y : M.Carrier} (h : ∀ z, M.app x z = M.app y z) :
    M.app (M.eps ρ) x = M.app (M.eps ρ) y := by
  rw [eps, M.interp_beta, M.interp_beta]
  refine M.interp_lam_ext _ _ _ _ fun d => ?_
  simp only [M.interp_app, M.interp_var, modelCons_zero, modelCons_succ]
  exact h d

/-- `ε` is idempotent for application: `ε ε = ε`. -/
theorem app_eps_eps (ρ : ℕ → M.Carrier) : M.app (M.eps ρ) (M.eps ρ) = M.eps ρ := by
  rw [eps, M.interp_beta]
  refine M.interp_lam_ext _ _ _ _ fun d => ?_
  rw [M.interp_app, M.interp_var, M.interp_var]
  change M.app (M.eps ρ) d = _
  rw [eps, M.interp_beta]

/-! ### Extensionality and η -/

/-- An **extensional** model: elements with the same applicative behaviour are equal. -/
def IsExtensional : Prop := ∀ x y : M.Carrier, (∀ z, M.app x z = M.app y z) → x = y

/-- In an extensional model, `ε` acts as the identity. -/
theorem app_eps_eq_of_extensional (hM : M.IsExtensional) (ρ : ℕ → M.Carrier) (x : M.Carrier) :
    M.app (M.eps ρ) x = x :=
  hM _ _ fun z => app_app_eps M ρ x z

/-- **An extensional model validates η**: `λx. t x = t` whenever `x` is not free in `t`. -/
theorem interp_eta_of_extensional (hM : M.IsExtensional) (t : Lambda) (ρ : ℕ → M.Carrier) :
    M.interp (Lambda.lam (Lambda.app (Lambda.lift 1 0 t) (Lambda.var 0))) ρ = M.interp t ρ := by
  refine hM _ _ fun z => ?_
  rw [M.interp_beta, M.interp_app, M.interp_var, interp_lift_zero, modelCons_zero]

/-- The model is **nontrivial** if it has at least two elements. -/
def IsNontrivial : Prop := ∃ x y : M.Carrier, x ≠ y

end LambdaModel

end Lambda
