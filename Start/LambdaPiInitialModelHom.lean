/-
**The interpretation of `λΠ` is a morphism of models.**

`Start/LambdaPiInitialUniv.lean` builds the comparison morphism of categories with attributes out
of the syntactic model of `λΠ` and proves that it preserves the universe, the products over the
small types, their codes and abstraction; `Start/LambdaPiInitialApp.lean` adds the last clause,
preservation of application.  This module packages all of it as a `LambdaPi.ModelHom`, so that the
syntax is *weakly initial* among the models of `λΠ` with injective products: there is a morphism of
models out of it into every such model.

* `LambdaPiInitial.tmMap_lam_cast` — abstraction is preserved, in the transported form that a
  morphism of models asks for;
* `LambdaPiInitial.obj_empty` — the empty context is interpreted by the empty context of the model;
* `LambdaPiInitial.modelHom` — **the interpretation is a morphism of models** out of the syntactic
  model, and `LambdaPiInitial.nonempty_modelHom` its existence statement.

Together with `LambdaPiSelf.isoModelHom` (every morphism of models out of the syntax is isomorphic
to this one) and `LambdaPiSelf.nonempty_unique_twoCell_modelHom` (between two of them there is
exactly one 2-cell), this makes the hom-category out of the syntactic model *inhabited* and
contractible: `LambdaPiInitial.biInitial_syntacticModel`.
-/

import Start.LambdaPiInitialApp
import Start.LambdaPiSelfMor

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPiInitial

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- A value equality determines the transported term. -/
theorem tmCast_of_val_eq {Γ : C} {A A' : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A} {x' : Cwa.Tm M.T Γ A'}
    (e : A = A') (h : (⟨A, x⟩ : TmVal M Γ) = ⟨A', x'⟩) : Cwa.tmCast e x = x' := by
  cases e
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

variable (hinj : M.PiInj)

/-- **Abstraction is preserved by the comparison morphism**, in the form a morphism of models asks
for: the image of an abstraction, transported along the comparison of the products, is the
abstraction of the image of the body read in the compared extended context. -/
theorem tmMap_lam_cast {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) B) :
    Cwa.tmCast ((mor_preservesSmallPi hinj).Pi_map a B) ((mor hinj).tmMap (smallPi.lam b))
      = M.SP.lam (M.T.tmSub ((mor_preservesUniverse hinj).extElIso a).inv
          ((mor hinj).tmMap b)) :=
  tmCast_of_val_eq _ (tmMap_lamQ hinj b)

/-- **The empty context is interpreted by the empty context of the model.** -/
theorem obj_empty : obj hinj LambdaPiCat.empty = M.emp := rfl

/-- **The interpretation of `λΠ` is a morphism of models**: the comparison morphism of categories
with attributes out of the syntactic model preserves the universe, the products over the small
types, their codes, abstraction, application, and the empty context. -/
noncomputable def modelHom : ModelHom syntacticModel M where
  mor := mor hinj
  pu := mor_preservesUniverse hinj
  psp := mor_preservesSmallPi hinj
  ppc := mor_preservesPiClosed hinj
  lam_map b := tmMap_lam_cast hinj b
  app_map f := tmMap_appQ hinj f
  empTerminal := M.empIsTerminal

/-- **The syntax of `λΠ` is weakly initial**: every model with injective products receives a
morphism of models from the syntactic model. -/
theorem nonempty_modelHom (hinj : M.PiInj) : Nonempty (ModelHom syntacticModel M) :=
  ⟨modelHom hinj⟩

/-- **The syntactic model of `λΠ` is bi-initial among the models with injective products**: into
every such model there is a morphism of models, and between the 1-cells underlying any two of them
there is exactly one 2-cell.  Existence is the interpretation `LambdaPiInitial.modelHom`;
contractibility is `LambdaPiSelf.nonempty_unique_twoCell_modelHom`. -/
theorem biInitial_syntacticModel (hinj : M.PiInj) :
    Nonempty (ModelHom syntacticModel M) ∧
      ∀ H K : ModelHom syntacticModel M,
        Nonempty (Cwa.TwoCell H.mor K.mor) ∧ Subsingleton (Cwa.TwoCell H.mor K.mor) :=
  ⟨nonempty_modelHom hinj, fun H K => LambdaPiSelf.nonempty_unique_twoCell_modelHom hinj H K⟩

end LambdaPiInitial
