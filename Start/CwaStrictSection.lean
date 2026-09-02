/-
**The category of contexts is a strict retraction of strictification.**

`Start/CwaStrictFunctor.lean` builds `Cwa.strictification : PbCat ⥤ Cwa.Model`, the functor that
presents a category with pullbacks as a model of a dependent type theory.  Going the other way is
the forgetful passage that reads off the category of contexts of a model, `Cwa.Model.ctx`.  This
module builds that functor and proves that the round trip
`PbCat ⥤ Cwa.Model ⥤ Cat` is *equal*, not merely isomorphic, to the underlying-category functor
of `PbCat`: strictification is a strict section of the category-of-contexts functor.

Two consequences make the comparison usable in the two-categorical setting of
`Start/CwaBicat.lean`: strictification is faithful, and it reflects isomorphisms — if the
strictified models of two categories with pullbacks are isomorphic by a morphism coming from a
functor, that functor was already an isomorphism of categories with pullbacks.  Reflection needs
the observation that the inverse morphism of models has an underlying functor which is strictly
inverse to the given one, hence an equivalence, hence preserves pullbacks.

Main definitions:

* `Cwa.Model.ctx` — the category of contexts of a model, functorially;
* `Cwa.PbCat.toCat` — the underlying category of a category with pullbacks.

Main results:

* `Cwa.strictification_comp_ctx` — **the round trip is the identity on the nose**;
* `Cwa.strictification_faithful` — strictification is faithful;
* `Cwa.strictification_reflects_iso` — **strictification reflects isomorphisms**.
-/

import Start.CwaStrictFunctor
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Limits

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

/-! ### The category of contexts of a model -/

/-- **The category of contexts of a model**, functorially: a morphism of models acts on contexts
by its underlying functor, and does so strictly functorially. -/
def Model.ctx : Cwa.Model.{u, v, w} ⥤ Cat.{v, u} where
  obj M := Cat.of M.Ctx
  map F := Functor.toCatHom F.fnc
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem Model.ctx_obj (M : Cwa.Model.{u, v, w}) : Model.ctx.obj M = Cat.of M.Ctx := rfl

@[simp] theorem Model.ctx_map {M N : Cwa.Model.{u, v, w}} (F : M ⟶ N) :
    (Model.ctx.map F).toFunctor = F.fnc := rfl

/-- The underlying category of a category with pullbacks, functorially. -/
def PbCat.toCat : PbCat.{u, v} ⥤ Cat.{v, u} where
  obj X := Cat.of X.Ctx
  map f := Functor.toCatHom f.fnc
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem PbCat.toCat_obj (X : PbCat.{u, v}) : PbCat.toCat.obj X = Cat.of X.Ctx := rfl

@[simp] theorem PbCat.toCat_map {X Y : PbCat.{u, v}} (f : X ⟶ Y) :
    (PbCat.toCat.map f).toFunctor = f.fnc := rfl

/-! ### Strictification is a strict section -/

/-- **The category of contexts of the strictification of a category with pullbacks is that
category itself**, and the same holds for morphisms: the round trip is the identity functor on
the nose. -/
theorem strictification_comp_ctx :
    strictification.{u, v} ⋙ Model.ctx.{u, v, max u v} = PbCat.toCat.{u, v} := rfl

/-- Strictification does not change the underlying functor of a morphism. -/
@[simp] theorem strictification_map_fnc {X Y : PbCat.{u, v}} (f : X ⟶ Y) :
    (strictification.map f).fnc = f.fnc := rfl

/-- **Strictification is faithful**: a pullback-preserving functor is determined by the morphism
of models it induces. -/
instance strictification_faithful : Functor.Faithful strictification.{u, v} where
  map_injective {_ _ _ _} h := PbCat.Hom.ext (congrArg Cwa.Mor.fnc h)

/-! ### Strictification reflects isomorphisms -/

section Reflect

variable {X Y : PbCat.{u, v}} (f : X ⟶ Y) [IsIso (strictification.map f)]

/-- The functor underlying the inverse of an invertible induced morphism of models. -/
noncomputable def invFnc : Y.Ctx ⥤ X.Ctx := (inv (strictification.map f)).fnc

theorem fnc_comp_invFnc : f.fnc ⋙ invFnc f = 𝟭 X.Ctx :=
  congrArg Cwa.Mor.fnc (IsIso.hom_inv_id (strictification.map f))

theorem invFnc_comp_fnc : invFnc f ⋙ f.fnc = 𝟭 Y.Ctx :=
  congrArg Cwa.Mor.fnc (IsIso.inv_hom_id (strictification.map f))

/-- A functor with a strict two-sided inverse is one half of an equivalence. -/
noncomputable def strictEquiv : X.Ctx ≌ Y.Ctx where
  functor := f.fnc
  inverse := invFnc f
  unitIso := eqToIso (fnc_comp_invFnc f).symm
  counitIso := eqToIso (invFnc_comp_fnc f)
  functor_unitIso_comp := by
      intro Z
      have h₁ : (eqToIso (fnc_comp_invFnc f).symm).hom.app Z
          = eqToHom (congrFun (congrArg Functor.obj (fnc_comp_invFnc f).symm) Z) := by
        simp [eqToIso, eqToHom_app]
      have h₂ : (eqToIso (invFnc_comp_fnc f)).hom.app (f.fnc.obj Z)
          = eqToHom (congrFun (congrArg Functor.obj (invFnc_comp_fnc f)) (f.fnc.obj Z)) := by
        simp [eqToIso, eqToHom_app]
      rw [h₁, h₂, eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- The inverse functor preserves pullbacks, being half of an equivalence. -/
noncomputable instance : PreservesLimitsOfShape WalkingCospan (invFnc f) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (strictEquiv f).inverse)

/-- **Strictification reflects isomorphisms**: if the induced morphism of models is invertible,
the functor it came from was already invertible as a morphism of categories with pullbacks. -/
theorem isIso_of_isIso_strictification_map : IsIso f :=
  ⟨⟨⟨invFnc f, inferInstance⟩, PbCat.Hom.ext (fnc_comp_invFnc f),
    PbCat.Hom.ext (invFnc_comp_fnc f)⟩⟩

end Reflect

/-- **Strictification reflects isomorphisms.** -/
instance strictification_reflects_iso :
    Functor.ReflectsIsomorphisms strictification.{u, v} where
  reflects f _ := isIso_of_isIso_strictification_map f

end Cwa
