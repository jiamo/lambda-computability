/-
Reflexive objects in the category of sets, and the λ-models they carry.

A **reflexive object** in a cartesian closed category is an object `D` of which the function
space `D ⇒ D` is a retract.  Taking the cartesian closed category to be the category of sets,
this is a set `D` with maps

    lam : (D → D) → D,    app : D → (D → D),    app ∘ lam = id,

and this file proves the easy half of the Scott–Koymans correspondence for that case: **every
such retraction is a λ-model** in the sense of `Start/LambdaModel.lean`
(`Lambda.SetReflexive.toModel`), and it is extensional exactly when the other composite is the
identity as well (`Lambda.SetReflexive.toModel_extensional`), in which case it validates η.

The general case — a reflexive object in an arbitrary cartesian closed category — is treated in
`Start/ReflexiveCcc.lean`, and the converse construction, turning an arbitrary λ-model into a
cartesian closed category with a reflexive object, is in `Start/KaroubiLambda.lean`.
-/

import Start.LambdaModel

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Lambda

/-- A **reflexive object in the category of sets**: a set whose full function space is a
retract of it. -/
structure SetReflexive where
  /-- The underlying set. -/
  D : Type u
  /-- The embedding of the function space, `λ`. -/
  lam : (D → D) → D
  /-- The retraction, application. -/
  app : D → (D → D)
  /-- The retraction equation, i.e. β. -/
  app_lam : ∀ f : D → D, app (lam f) = f

namespace SetReflexive

variable (R : SetReflexive.{u})

/-- The interpretation of a term determined by the retraction. -/
def interp : Lambda → (ℕ → R.D) → R.D
  | Lambda.var i, ρ => ρ i
  | Lambda.app s t, ρ => R.app (interp s ρ) (interp t ρ)
  | Lambda.lam s, ρ => R.lam (fun d => interp s (modelCons d ρ))

@[simp] theorem interp_var (i : ℕ) (ρ : ℕ → R.D) : R.interp (Lambda.var i) ρ = ρ i := rfl

@[simp] theorem interp_app (s t : Lambda) (ρ : ℕ → R.D) :
    R.interp (Lambda.app s t) ρ = R.app (R.interp s ρ) (R.interp t ρ) := rfl

@[simp] theorem interp_lam (s : Lambda) (ρ : ℕ → R.D) :
    R.interp (Lambda.lam s) ρ = R.lam (fun d => R.interp s (modelCons d ρ)) := rfl

/-- **A reflexive object in the category of sets is a λ-model.** -/
def toModel : LambdaModel.{u} where
  Carrier := R.D
  app := R.app
  nonempty := ⟨R.lam id⟩
  interp := R.interp
  interp_var := fun _ _ => rfl
  interp_app := fun _ _ _ => rfl
  interp_beta := by
    intro t ρ d
    rw [interp_lam, R.app_lam]
  interp_lam_ext := by
    intro t t' ρ ρ' h
    rw [interp_lam, interp_lam]
    exact congrArg R.lam (funext h)

@[simp] theorem toModel_carrier : R.toModel.Carrier = R.D := rfl
@[simp] theorem toModel_app (x y : R.D) : R.toModel.app x y = R.app x y := rfl
@[simp] theorem toModel_interp (t : Lambda) (ρ : ℕ → R.D) :
    R.toModel.interp t ρ = R.interp t ρ := rfl

/-- Soundness for β, an instance of the abstract soundness theorem. -/
theorem interp_conv {t t' : Lambda} (h : Conv t t') (ρ : ℕ → R.D) :
    R.interp t ρ = R.interp t' ρ :=
  R.toModel.interp_conv h ρ

/-- An **isomorphism** `D ≅ (D → D)`, i.e. the second composite is the identity too, makes the
model extensional. -/
theorem toModel_extensional (h : ∀ x : R.D, R.lam (R.app x) = x) : R.toModel.IsExtensional := by
  intro x y hxy
  have : R.lam (R.app x) = R.lam (R.app y) := congrArg R.lam (funext hxy)
  rwa [h x, h y] at this

/-- Conversely, an extensional model of this shape is an isomorphism `D ≅ (D → D)`: `lam` and
`app` are mutually inverse. -/
theorem lam_app_of_extensional (h : R.toModel.IsExtensional) (x : R.D) :
    R.lam (R.app x) = x := by
  refine h _ _ fun z => ?_
  change R.app (R.lam (R.app x)) z = R.app x z
  rw [R.app_lam]

end SetReflexive

end Lambda
