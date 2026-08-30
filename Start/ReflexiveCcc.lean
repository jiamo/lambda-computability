/-
Reflexive objects in an arbitrary cartesian closed category, and the interpretation of the
untyped λ-calculus they carry.

A **reflexive object** of a cartesian closed category `C` is an object `D` together with a
retraction of its internal function space onto it,

    lam : (D ⇒ D) ⟶ D,   app : D ⟶ (D ⇒ D),   lam ≫ app = 𝟙.

This is Scott's categorical account of the untyped λ-calculus: an untyped term is interpreted,
at a *stage* `X` and in an environment `ρ : ℕ → (X ⟶ D)` of generalized elements, as a morphism
`X ⟶ D`.  The file proves that this interpretation is a model of the β-calculus:

* `ReflexiveCcc.ReflexiveObject.interp` — the interpretation;
* `ReflexiveCcc.ReflexiveObject.interp_reindex` — it is natural in the stage: reindexing along
  `u : Y ⟶ X` reindexes the environment;
* `ReflexiveCcc.ReflexiveObject.interp_beta` — `⟦λt⟧ρ` applied to `a` is `⟦t⟧(a :: ρ)`;
* `ReflexiveCcc.ReflexiveObject.interp_lift`, `..._interp_subst` — the lifting and substitution
  lemmas;
* `ReflexiveCcc.ReflexiveObject.interp_conv` — **soundness**: β-convertible terms receive equal
  interpretations, at every stage and in every environment;
* `ReflexiveCcc.ReflexiveObject.interp_eta_of_iso` — an isomorphism `D ≅ (D ⇒ D)` additionally
  validates η.

Together with `Start/KaroubiLambda.lean`, which turns an arbitrary λ-model into a cartesian
closed category with a reflexive object, this is the Scott–Koymans correspondence
"λ-model ⟺ reflexive object in a cartesian closed category".  The special case `C = Type` is
`Start/ReflexiveType.lean`, where the interpretation really is a λ-model
(`Lambda.SetReflexive.toModel`); in a general `C` weak extensionality is a statement about
generalized elements, which is what `interp_lam_congr` below records.
-/

import Start.LambdaModel
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe v u

namespace ReflexiveCcc

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Lambda (modelCons)

/-- A **reflexive object**: an object whose internal function space is a retract of it. -/
structure ReflexiveObject (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] where
  /-- The underlying object. -/
  D : C
  /-- The embedding of the function space. -/
  lam : (D ⟶[C] D) ⟶ D
  /-- The retraction. -/
  app : D ⟶ (D ⟶[C] D)
  /-- The retraction equation, i.e. β. -/
  lam_app : lam ≫ app = 𝟙 (D ⟶[C] D)

namespace ReflexiveObject

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

omit [MonoidalClosed C] in
/-- Reindexing a pairing in the second component. -/
theorem lift_comp_whiskerLeft {T Z Y X : C} (f : T ⟶ Z) (g : T ⟶ Y) (u : Y ⟶ X) :
    lift f g ≫ (Z ◁ u) = lift f (g ≫ u) := by
  refine hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerLeft_fst, lift_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd, lift_snd]

variable (R : ReflexiveObject C)

/-! ### The interpretation -/

/-- Application of two generalized elements of `D`. -/
def appMor {X : C} (f a : X ⟶ R.D) : X ⟶ R.D := lift a (𝟙 X) ≫ uncurry (f ≫ R.app)

/-- Abstraction: a morphism out of `D ⊗ X` becomes a generalized element of `D` at stage `X`. -/
def lamMor {X : C} (t : R.D ⊗ X ⟶ R.D) : X ⟶ R.D := curry t ≫ R.lam

/-- Moving an environment to the extended stage `D ⊗ X`, where the index `0` denotes the new
generic element. -/
def shift {X : C} (ρ : ℕ → (X ⟶ R.D)) : ℕ → (R.D ⊗ X ⟶ R.D) :=
  modelCons (fst R.D X) (fun i => snd R.D X ≫ ρ i)

@[simp] theorem shift_zero {X : C} (ρ : ℕ → (X ⟶ R.D)) : R.shift ρ 0 = fst R.D X := rfl

@[simp] theorem shift_succ {X : C} (ρ : ℕ → (X ⟶ R.D)) (i : ℕ) :
    R.shift ρ (i + 1) = snd R.D X ≫ ρ i := rfl

/-- **The interpretation of an untyped term** at a stage `X`, in an environment of generalized
elements. -/
def interp (R : ReflexiveObject C) : Lambda → ∀ {X : C}, (ℕ → (X ⟶ R.D)) → (X ⟶ R.D)
  | Lambda.var i => fun ρ => ρ i
  | Lambda.app s t => fun ρ => R.appMor (interp R s ρ) (interp R t ρ)
  | Lambda.lam t => fun ρ => R.lamMor (interp R t (R.shift ρ))

@[simp] theorem interp_var {X : C} (i : ℕ) (ρ : ℕ → (X ⟶ R.D)) :
    R.interp (Lambda.var i) ρ = ρ i := rfl

@[simp] theorem interp_app {X : C} (s t : Lambda) (ρ : ℕ → (X ⟶ R.D)) :
    R.interp (Lambda.app s t) ρ = R.appMor (R.interp s ρ) (R.interp t ρ) := rfl

@[simp] theorem interp_lam {X : C} (t : Lambda) (ρ : ℕ → (X ⟶ R.D)) :
    R.interp (Lambda.lam t) ρ = R.lamMor (R.interp t (R.shift ρ)) := rfl

/-- The interpretation only depends on the environment pointwise. -/
theorem interp_congr_env {X : C} (t : Lambda) {ρ ρ' : ℕ → (X ⟶ R.D)} (h : ∀ i, ρ i = ρ' i) :
    R.interp t ρ = R.interp t ρ' := by
  rw [funext h]

/-- Weak extensionality, in the form available in a general cartesian closed category: two
abstractions whose bodies agree on the generic element are equal. -/
theorem interp_lam_congr {X : C} (t t' : Lambda) (ρ ρ' : ℕ → (X ⟶ R.D))
    (h : R.interp t (R.shift ρ) = R.interp t' (R.shift ρ')) :
    R.interp (Lambda.lam t) ρ = R.interp (Lambda.lam t') ρ' := by
  rw [interp_lam, interp_lam, lamMor, lamMor, h]

/-! ### Naturality in the stage -/

/-- Application is natural in the stage. -/
theorem appMor_reindex {X Y : C} (u : Y ⟶ X) (f a : X ⟶ R.D) :
    u ≫ R.appMor f a = R.appMor (u ≫ f) (u ≫ a) := by
  have hR : R.appMor (u ≫ f) (u ≫ a) = lift (u ≫ a) u ≫ uncurry (f ≫ R.app) := by
    rw [appMor, Category.assoc, uncurry_natural_left, ← Category.assoc,
      lift_comp_whiskerLeft, Category.id_comp]
  rw [hR, appMor, ← Category.assoc, comp_lift, Category.comp_id]

/-- Abstraction is natural in the stage. -/
theorem lamMor_reindex {X Y : C} (u : Y ⟶ X) (t : R.D ⊗ X ⟶ R.D) :
    u ≫ R.lamMor t = R.lamMor ((R.D ◁ u) ≫ t) := by
  rw [lamMor, lamMor, ← Category.assoc, curry_natural_left]

/-- **Reindexing**: the interpretation is natural in the stage. -/
theorem interp_reindex : ∀ (t : Lambda) {X Y : C} (u : Y ⟶ X) (ρ : ℕ → (X ⟶ R.D)),
    u ≫ R.interp t ρ = R.interp t (fun i => u ≫ ρ i) := by
  intro t
  induction t with
  | var i => intro X Y u ρ; rfl
  | app s w ihs ihw =>
      intro X Y u ρ
      rw [interp_app, interp_app, appMor_reindex, ihs u ρ, ihw u ρ]
  | lam w ih =>
      intro X Y u ρ
      rw [interp_lam, interp_lam, lamMor_reindex, ih (R.D ◁ u) (R.shift ρ)]
      refine congrArg R.lamMor (R.interp_congr_env w fun i => ?_)
      cases i with
      | zero => exact whiskerLeft_fst _ _
      | succ j => rw [shift_succ, shift_succ, ← Category.assoc, whiskerLeft_snd, Category.assoc]

/-! ### β -/

/-- **The semantic β-rule**: an abstraction applies as its body. -/
theorem interp_beta {X : C} (t : Lambda) (ρ : ℕ → (X ⟶ R.D)) (a : X ⟶ R.D) :
    R.appMor (R.interp (Lambda.lam t) ρ) a = R.interp t (modelCons a ρ) := by
  rw [interp_lam, lamMor, appMor, Category.assoc, R.lam_app, Category.comp_id, uncurry_curry,
    interp_reindex]
  refine R.interp_congr_env t fun i => ?_
  cases i with
  | zero => exact lift_fst _ _
  | succ j => rw [shift_succ, ← Category.assoc, lift_snd, Category.id_comp]; rfl

/-! ### The lifting and substitution lemmas -/

/-- The lifting lemma. -/
theorem interp_lift : ∀ (t : Lambda) (k : ℕ) {X : C} (ρ : ℕ → (X ⟶ R.D)),
    R.interp (Lambda.lift 1 k t) ρ = R.interp t (fun i => if i < k then ρ i else ρ (i + 1)) := by
  intro t
  induction t with
  | var y =>
      intro k X ρ
      by_cases hy : y < k <;> simp [Lambda.lift, hy]
  | app s w ihs ihw =>
      intro k X ρ
      simp only [Lambda.lift, interp_app, ihs, ihw]
  | lam w ih =>
      intro k X ρ
      refine R.interp_lam_congr _ _ _ _ ?_
      rw [ih (k + 1) (R.shift ρ)]
      refine R.interp_congr_env w fun i => ?_
      cases i with
      | zero => simp
      | succ j =>
          by_cases hj : j < k
          · simp [hj, Nat.succ_lt_succ hj]
          · have h : ¬ (j + 1 < k + 1) := by omega
            simp [hj, h]

/-- Lifting at `0` inserts a dummy value at the front of the environment. -/
theorem interp_lift_zero {X : C} (t : Lambda) (ρ : ℕ → (X ⟶ R.D)) (a : X ⟶ R.D) :
    R.interp (Lambda.lift 1 0 t) (modelCons a ρ) = R.interp t ρ := by
  rw [interp_lift]
  refine R.interp_congr_env t fun i => ?_
  simp

/-- Lifting at `0` and moving to the extended stage: the new generic element is ignored. -/
theorem interp_lift_zero_shift {X : C} (t : Lambda) (ρ : ℕ → (X ⟶ R.D)) :
    R.interp (Lambda.lift 1 0 t) (R.shift ρ) = snd R.D X ≫ R.interp t ρ := by
  rw [interp_lift, interp_reindex]
  refine R.interp_congr_env t fun i => ?_
  simp

/-- The substitution lemma: substitution is evaluation in the modified environment. -/
theorem interp_subst : ∀ (t s : Lambda) (x : ℕ) {X : C} (ρ : ℕ → (X ⟶ R.D)),
    R.interp (Lambda.subst s x t) ρ =
      R.interp t (fun i => if i = x then R.interp s ρ else if x < i then ρ (i - 1) else ρ i) := by
  intro t
  induction t with
  | var y =>
      intro s x X ρ
      rcases lt_trichotomy y x with hy | hy | hy
      · have h1 : ¬ (y = x) := by omega
        have h2 : ¬ (x < y) := by omega
        simp [Lambda.subst, h1, h2]
      · subst hy
        simp [Lambda.subst]
      · have h1 : ¬ (y = x) := by omega
        simp [Lambda.subst, h1, hy]
  | app a b iha ihb =>
      intro s x X ρ
      simp only [Lambda.subst, interp_app, iha, ihb]
  | lam a ih =>
      intro s x X ρ
      refine R.interp_lam_congr _ _ _ _ ?_
      rw [ih (Lambda.lift 1 0 s) (x + 1) (R.shift ρ)]
      refine R.interp_congr_env a fun i => ?_
      cases i with
      | zero => simp
      | succ j =>
          by_cases hj : j = x
          · subst hj
            simp only [shift_succ, if_true]
            exact R.interp_lift_zero_shift s ρ
          · by_cases hj' : x < j
            · have h2 : x + 1 < j + 1 := by omega
              cases j with
              | zero => omega
              | succ m => simp [h2, hj', hj]
            · have h2 : ¬ (x + 1 < j + 1) := by omega
              simp [h2, hj', hj]

/-! ### Soundness -/

/-- The syntactic β-rule is validated. -/
theorem interp_beta_subst {X : C} (t u : Lambda) (ρ : ℕ → (X ⟶ R.D)) :
    R.interp (Lambda.app (Lambda.lam t) u) ρ = R.interp (Lambda.subst u 0 t) ρ := by
  rw [interp_app, interp_beta, interp_subst]
  refine R.interp_congr_env t fun i => ?_
  cases i with
  | zero => simp
  | succ j => simp

/-- **Soundness for one β-step.** -/
theorem interp_step : ∀ {t t' : Lambda}, Lambda.step t t' →
    ∀ {X : C} (ρ : ℕ → (X ⟶ R.D)), R.interp t ρ = R.interp t' ρ := by
  intro t t' h
  induction h with
  | beta a b => intro X ρ; exact R.interp_beta_subst a b ρ
  | app_left a a' b _ ih => intro X ρ; simp only [interp_app, ih ρ]
  | app_right a b b' _ ih => intro X ρ; simp only [interp_app, ih ρ]
  | lam a a' _ ih => intro X ρ; exact R.interp_lam_congr _ _ _ _ (ih (R.shift ρ))

/-- **Soundness for β-reduction.** -/
theorem interp_reduces {t t' : Lambda} (h : Lambda.reduces t t') {X : C}
    (ρ : ℕ → (X ⟶ R.D)) : R.interp t ρ = R.interp t' ρ := by
  induction h with
  | refl a => rfl
  | step a b c hab _ ih => exact (R.interp_step hab ρ).trans ih

/-- **Soundness for β-conversion**: a reflexive object in a cartesian closed category is a
model of the untyped λ-calculus. -/
theorem interp_conv {t t' : Lambda} (h : Lambda.Conv t t') {X : C} (ρ : ℕ → (X ⟶ R.D)) :
    R.interp t ρ = R.interp t' ρ := by
  obtain ⟨u, h₁, h₂⟩ := h
  exact (R.interp_reduces h₁ ρ).trans (R.interp_reduces h₂ ρ).symm

/-! ### η -/

/-- If the retraction is an isomorphism, η holds as well. -/
theorem interp_eta_of_iso (hR : R.app ≫ R.lam = 𝟙 R.D) {X : C} (t : Lambda)
    (ρ : ℕ → (X ⟶ R.D)) :
    R.interp (Lambda.lam (Lambda.app (Lambda.lift 1 0 t) (Lambda.var 0))) ρ
      = R.interp t ρ := by
  rw [interp_lam, interp_app, interp_lift_zero_shift, interp_var, shift_zero, lamMor, appMor]
  have h : curry (lift (fst R.D X) (𝟙 (R.D ⊗ X)) ≫
      uncurry ((snd R.D X ≫ R.interp t ρ) ≫ R.app))
      = R.interp t ρ ≫ R.app := by
    rw [Category.assoc, uncurry_natural_left, ← Category.assoc, lift_comp_whiskerLeft,
      Category.id_comp]
    have : lift (fst R.D X) (snd R.D X) = 𝟙 (R.D ⊗ X) := lift_fst_snd
    rw [this, Category.id_comp, curry_uncurry]
  rw [h, Category.assoc, hR, Category.comp_id]

end ReflexiveObject

end ReflexiveCcc
