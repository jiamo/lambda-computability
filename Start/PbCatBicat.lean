/-
**Categories with pullbacks form a 2-category.**

`Start/CwaStrictFunctor.lean` bundles a category with pullbacks as `Cwa.PbCat`, takes
pullback-preserving functors for its morphisms, and proves that strictification is a *functor*
`Cwa.strictification` into the 1-category of models.  The comparison with the models of a
dependent type theory is however a 2-dimensional statement, so the source needs its second
dimension: the natural transformations of the underlying functors.

Since composition of pullback-preserving functors is composition of functors, the composition of
1-cells is strictly associative and unital, so the bicategory built here is
`CategoryTheory.Bicategory.Strict` — as is the 2-category of models.

Main definitions:

* `Cwa.PbCat.homCategory` — the 1-cells between two categories with pullbacks form a category,
  the natural transformations being its morphisms;
* `Cwa.PbCat.instBicategory` — **the 2-category of categories with pullbacks**, pullback-preserving
  functors and natural transformations;
* `Cwa.PbCat.instStrict` — it is strict.
-/

import Start.CwaStrictFunctor
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory

namespace Cwa

namespace PbCat

variable {X Y Z W : PbCat.{u, v}}

/-- **The pullback-preserving functors between two categories with pullbacks form a category**,
the natural transformations of the underlying functors being its morphisms. -/
instance homCategory (X Y : PbCat.{u, v}) : Category.{max u v} (X ⟶ Y) where
  Hom f g := f.fnc ⟶ g.fnc
  id f := 𝟙 f.fnc
  comp α β := α ≫ β
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

@[simp] theorem id_app (f : X ⟶ Y) (A : X.Ctx) :
    NatTrans.app (𝟙 f : f.fnc ⟶ f.fnc) A = 𝟙 (f.fnc.obj A) := rfl

@[simp] theorem comp_app {f g h : X ⟶ Y} (α : f ⟶ g) (β : g ⟶ h) (A : X.Ctx) :
    NatTrans.app ((α ≫ β : f ⟶ h) : f.fnc ⟶ h.fnc) A
      = NatTrans.app (α : f.fnc ⟶ g.fnc) A ≫ NatTrans.app (β : g.fnc ⟶ h.fnc) A := rfl

/-- A 2-cell of `Cwa.PbCat` is determined by its components. -/
@[ext] theorem twoCell_ext {f g : X ⟶ Y} {α β : f ⟶ g}
    (h : ∀ A : X.Ctx, NatTrans.app (α : f.fnc ⟶ g.fnc) A = NatTrans.app (β : f.fnc ⟶ g.fnc) A) :
    α = β :=
  NatTrans.ext (funext h)

@[simp] theorem eqToHom_app {f g : X ⟶ Y} (h : f = g) (A : X.Ctx) :
    NatTrans.app ((eqToHom h : f ⟶ g) : f.fnc ⟶ g.fnc) A = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- **Categories with pullbacks, pullback-preserving functors and natural transformations form a
2-category.** -/
instance instBicategory : Bicategory.{max u v, max u v} PbCat.{u, v} where
  toCategoryStruct := PbCat.instCategory.toCategoryStruct
  homCategory := homCategory
  whiskerLeft f _ _ α := Functor.whiskerLeft f.fnc α
  whiskerRight α h := Functor.whiskerRight α h.fnc
  associator f g h := eqToIso (Category.assoc f g h)
  leftUnitor f := eqToIso (Category.id_comp f)
  rightUnitor f := eqToIso (Category.comp_id f)
  whiskerLeft_id := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  whiskerLeft_comp := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  id_whiskerLeft := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  comp_whiskerLeft := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  id_whiskerRight := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  comp_whiskerRight := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  whiskerRight_id := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  whiskerRight_comp := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  whisker_assoc := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  whisker_exchange := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  pentagon := by intros; refine NatTrans.ext (funext fun A => ?_); simp
  triangle := by intros; refine NatTrans.ext (funext fun A => ?_); simp

@[simp] theorem bicategoryWhiskerLeft_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (α : g ⟶ h) :
    (Bicategory.whiskerLeft f α : (f ≫ g) ⟶ (f ≫ h))
      = Functor.whiskerLeft f.fnc (α : g.fnc ⟶ h.fnc) := rfl

@[simp] theorem bicategoryWhiskerRight_eq {f g : X ⟶ Y} (α : f ⟶ g) (h : Y ⟶ Z) :
    (Bicategory.whiskerRight α h : (f ≫ h) ⟶ (g ≫ h))
      = Functor.whiskerRight (α : f.fnc ⟶ g.fnc) h.fnc := rfl

@[simp] theorem bicategoryAssociator_hom_eq (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (Bicategory.associator f g h).hom = eqToHom (Category.assoc f g h) := rfl

@[simp] theorem bicategoryLeftUnitor_hom_eq (f : X ⟶ Y) :
    (Bicategory.leftUnitor f).hom = eqToHom (Category.id_comp f) := rfl

@[simp] theorem bicategoryRightUnitor_hom_eq (f : X ⟶ Y) :
    (Bicategory.rightUnitor f).hom = eqToHom (Category.comp_id f) := rfl

/-- **The 2-category of categories with pullbacks is strict.** -/
instance instStrict : Bicategory.Strict PbCat.{u, v} where
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

end PbCat

end Cwa
