/-
**The Scott–Koymans correspondence**: λ-models and reflexive objects in cartesian closed
categories are the same thing, and both determine a λ-theory.

The two constructions are developed in the two preceding files, and are put together here.

* `Lambda.LambdaModel.toReflexiveObject` — from a λ-model `M` to a reflexive object: the Karoubi
  envelope `Ret M` of `M` is a cartesian closed category (`Start/KaroubiLambda.lean`) and the
  object `D = λz. z` is reflexive in it;
* `ReflexiveCcc.ReflexiveObject.theory` — from a reflexive object in an arbitrary cartesian
  closed category back to the λ-calculus: its interpretation of untyped terms
  (`Start/ReflexiveCcc.lean`) is sound for β, and the equations it validates form a λ-theory in
  the sense of `Start/LambdaTheory.lean`.

The category of sets is treated separately in `Start/ReflexiveType.lean`, where a reflexive
object really is a λ-model (`Lambda.SetReflexive.toModel`); the internal hom of `Type u` in
Mathlib is a coyoneda functor rather than the function type itself, so that case is developed
with the function type directly.

Since the graph model, `D∞` and the filter model are λ-models
(`Start/LambdaModelInstances.lean`), each of them is now also a reflexive object in a cartesian
closed category, and the lattice of λ-theories `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*` of
`Start/LambdaTheory.lean` becomes a statement about reflexive objects.
-/

import Start.KaroubiLambda
import Start.ReflexiveCcc
import Start.ReflexiveType
import Start.LambdaModelInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace ReflexiveCcc

namespace ReflexiveObject

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (R : ReflexiveObject C)

/-- The interpretation is a congruence for one-hole contexts. -/
theorem interp_fill_congr {s t : Lambda}
    (h : ∀ (X : C) (ρ : ℕ → (X ⟶ R.D)), R.interp s ρ = R.interp t ρ) (Ctx : Lambda.Ctx) :
    ∀ (X : C) (ρ : ℕ → (X ⟶ R.D)), R.interp (Ctx.fill s) ρ = R.interp (Ctx.fill t) ρ := by
  induction Ctx with
  | hole => exact h
  | appL Ctx u ih => intro X ρ; simp only [Lambda.Ctx.fill, interp_app, ih X ρ]
  | appR u Ctx ih => intro X ρ; simp only [Lambda.Ctx.fill, interp_app, ih X ρ]
  | lam Ctx ih =>
      intro X ρ
      exact R.interp_lam_congr _ _ _ _ (ih (R.D ⊗ X) (R.shift ρ))

/-- **The theory of a reflexive object**: the equations between untyped terms that hold in it at
every stage.  This is a λ-theory. -/
def theory : Lambda.LambdaTheory where
  Rel s t := ∀ (X : C) (ρ : ℕ → (X ⟶ R.D)), R.interp s ρ = R.interp t ρ
  conv h := fun _ ρ => R.interp_conv h ρ
  symm h := fun X ρ => (h X ρ).symm
  trans h₁ h₂ := fun X ρ => (h₁ X ρ).trans (h₂ X ρ)
  congr Ctx h := R.interp_fill_congr h Ctx

@[simp] theorem theory_rel (s t : Lambda) :
    (theory R).Rel s t ↔ ∀ (X : C) (ρ : ℕ → (X ⟶ R.D)), R.interp s ρ = R.interp t ρ := Iff.rfl

end ReflexiveObject

end ReflexiveCcc

namespace Lambda

namespace LambdaModel

variable (M : LambdaModel.{u})

/-- **Every λ-model is a reflexive object in a cartesian closed category**: take the Karoubi
envelope of the model and the object `D = λz. z` in it. -/
noncomputable def toReflexiveObject : ReflexiveCcc.ReflexiveObject (Ret M) where
  D := dRet M
  lam := dLam M
  app := dApp M
  lam_app := reflexive_dRet

@[simp] theorem toReflexiveObject_D : (toReflexiveObject M).D = dRet M := rfl

end LambdaModel

end Lambda
