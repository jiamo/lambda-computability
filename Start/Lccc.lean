/-
Locally cartesian closed categories, packaged as an explicit class with named Σ / f* / Π.

`Start/StlcCcc.lean` matched the simply typed lambda calculus with *cartesian closed* categories.
The dependently typed calculus `λΠ` of `Start/LambdaPi.lean` needs one level more: a type lives in
a context, so the semantics of a type is an object of a *slice* category, and the two quantifiers
`Σ` and `Π` are the two adjoints of pullback between slices.

Mathlib provides the two halves of this story separately -- `CategoryTheory.ChosenPullbacksAlong`
(the functorial choice of a pullback functor `Over X ⥤ Over Y`, right adjoint to `Over.map`) and
`CategoryTheory.ExponentiableMorphism` (a further right adjoint, the pushforward) -- but no single
class saying "this category is locally cartesian closed", and no naming of the dependent sum and
product.  This file supplies both.

* `LocallyCartesianClosed C` -- every morphism of `C` is exponentiable for the chosen pullbacks;
* `LocallyCartesianClosed.Sigma f`, `Pullback f`, `Pi f` -- the dependent sum, substitution and
  dependent product functors between slices;
* `LocallyCartesianClosed.sigmaPullbackAdj`, `pullbackPiAdj` -- the adjoint chain `Σ_f ⊣ f* ⊣ Π_f`,
  together with the two currying bijections `sigmaHomEquiv` and `piHomEquiv` that are the
  categorical form of the introduction/elimination rules for `Σ` and `Π`.

`Start/LcccType.lean` builds the motivating example, `Type u`, with the pushforward computed as an
honest dependent product, and connects it to the Π-structure of the standard model of
`Start/Cwa.lean`.
-/

import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
import Mathlib.CategoryTheory.LocallyCartesianClosed.Over

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe v u

namespace CategoryTheory

open Category ChosenPullbacksAlong ExponentiableMorphism

variable (C : Type u) [Category.{v} C]

/-- A category with chosen pullbacks is **locally cartesian closed** when every morphism is
exponentiable, i.e. every pullback functor between slices has a right adjoint.  Together with
`ChosenPullbacksAlong.mapPullbackAdj` this gives, for every `f : Y ⟶ X`, the adjoint chain
`Σ_f ⊣ f* ⊣ Π_f` between `Over Y` and `Over X`. -/
class LocallyCartesianClosed [ChosenPullbacks C] where
  /-- The pushforward (dependent product) functor along every morphism. -/
  pushforward : ∀ {X Y : C}, (Y ⟶ X) → (Over Y ⥤ Over X)
  /-- The pushforward is right adjoint to substitution. -/
  pullbackPushforwardAdj : ∀ {X Y : C} (f : Y ⟶ X),
    ChosenPullbacksAlong.pullback f ⊣ pushforward f

namespace LocallyCartesianClosed

variable {C} [ChosenPullbacks C]

/-- Every morphism of a locally cartesian closed category is exponentiable. -/
instance (priority := 100) instExponentiableMorphism [LocallyCartesianClosed C] {X Y : C}
    (f : Y ⟶ X) : ExponentiableMorphism f where
  pushforward := LocallyCartesianClosed.pushforward f
  pullbackPushforwardAdj := LocallyCartesianClosed.pullbackPushforwardAdj f

/-- A category with chosen pullbacks all of whose morphisms are exponentiable is locally
cartesian closed. -/
@[reducible]
def ofExponentiable (h : ∀ {X Y : C} (f : Y ⟶ X), ExponentiableMorphism f) :
    LocallyCartesianClosed C where
  pushforward f := (h f).pushforward
  pullbackPushforwardAdj f := (h f).pullbackPushforwardAdj

variable [LocallyCartesianClosed C] {X Y : C}

/-- The **dependent sum** along `f : Y ⟶ X`: postcomposition with `f`, the left adjoint of
substitution. -/
abbrev Sigma (f : Y ⟶ X) : Over Y ⥤ Over X := Over.map f

/-- **Substitution** along `f : Y ⟶ X`: the chosen pullback functor. -/
abbrev Pullback (f : Y ⟶ X) : Over X ⥤ Over Y := ChosenPullbacksAlong.pullback f

/-- The **dependent product** along `f : Y ⟶ X`: the pushforward, the right adjoint of
substitution. -/
abbrev Pi (f : Y ⟶ X) : Over Y ⥤ Over X := ExponentiableMorphism.pushforward f

/-- `Σ_f ⊣ f*`. -/
def sigmaPullbackAdj (f : Y ⟶ X) : Sigma f ⊣ Pullback f :=
  ChosenPullbacksAlong.mapPullbackAdj f

/-- `f* ⊣ Π_f`. -/
def pullbackPiAdj (f : Y ⟶ X) : Pullback f ⊣ Pi f :=
  ExponentiableMorphism.pullbackPushforwardAdj f

/-- The introduction/elimination bijection for the dependent sum: a map out of `Σ_f A` is a map
out of `A` into the substituted object. -/
def sigmaHomEquiv (f : Y ⟶ X) (A : Over Y) (B : Over X) :
    ((Sigma f).obj A ⟶ B) ≃ (A ⟶ (Pullback f).obj B) :=
  (sigmaPullbackAdj f).homEquiv A B

/-- The introduction/elimination bijection for the dependent product: a map into `Π_f B` is a map
out of the substituted object into `B`.  This is the categorical form of currying, and specialises
to the `lam`/`app` bijection of a Π-type structure. -/
def piHomEquiv (f : Y ⟶ X) (A : Over X) (B : Over Y) :
    ((Pullback f).obj A ⟶ B) ≃ (A ⟶ (Pi f).obj B) :=
  (pullbackPiAdj f).homEquiv A B

/-- Substitution has a left adjoint, hence preserves all limits it can. -/
instance (f : Y ⟶ X) : (Pullback f).IsRightAdjoint := (sigmaPullbackAdj f).isRightAdjoint

/-- Substitution has a right adjoint, hence preserves all colimits. -/
instance (f : Y ⟶ X) : (Pullback f).IsLeftAdjoint := (pullbackPiAdj f).isLeftAdjoint

/-- The dependent product preserves limits, being a right adjoint. -/
instance (f : Y ⟶ X) : (Pi f).IsRightAdjoint := (pullbackPiAdj f).isRightAdjoint

/-- The dependent sum preserves colimits, being a left adjoint. -/
instance (f : Y ⟶ X) : (Sigma f).IsLeftAdjoint := (sigmaPullbackAdj f).isLeftAdjoint

section Naturality

variable (f : Y ⟶ X)

@[simp] theorem piHomEquiv_naturality_left {A A' : Over X} {B : Over Y}
    (g : A' ⟶ A) (h : (Pullback f).obj A ⟶ B) :
    piHomEquiv f A' B ((Pullback f).map g ≫ h) = g ≫ piHomEquiv f A B h :=
  (pullbackPiAdj f).homEquiv_naturality_left _ _

@[simp] theorem piHomEquiv_naturality_right {A : Over X} {B B' : Over Y}
    (h : (Pullback f).obj A ⟶ B) (g : B ⟶ B') :
    piHomEquiv f A B' (h ≫ g) = piHomEquiv f A B h ≫ (Pi f).map g :=
  (pullbackPiAdj f).homEquiv_naturality_right _ _

omit [LocallyCartesianClosed C] in
@[simp] theorem sigmaHomEquiv_naturality_right {A : Over Y} {B B' : Over X}
    (h : (Sigma f).obj A ⟶ B) (g : B ⟶ B') :
    sigmaHomEquiv f A B' (h ≫ g) = sigmaHomEquiv f A B h ≫ (Pullback f).map g :=
  (sigmaPullbackAdj f).homEquiv_naturality_right _ _

end Naturality

end LocallyCartesianClosed

end CategoryTheory
