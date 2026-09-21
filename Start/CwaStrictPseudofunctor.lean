/-
**Strictification as a pseudofunctor of 2-categories.**

`Start/CwaStrictFunctor.lean` makes strictification a *functor* from categories with pullbacks to
models, `Start/CwaStrictLax.lean` and `Start/CwaStrictLaxWhisker.lean` prove that it carries
natural transformations to lax 2-cells compatibly with vertical composition and with whiskering on
both sides, and `Start/PbCatBicat.lean` and `Start/CwaLaxBicat.lean` make the two sides
2-categories.  What was still missing is the statement those results add up to: strictification is
a morphism of 2-categories in mathlib's sense.

This module assembles it.  Both 2-categories are strict and a lax 2-cell is determined by its
natural transformation (`Cwa.LaxCModel.hom_ext`), so every coherence law of a pseudofunctor comes
down to an equality of natural transformations, and the structural isomorphisms `mapId` and
`mapComp` are the transports along the equalities `Cwa.morOfPreservesPullbacks_id` and
`Cwa.morOfPreservesPullbacks_comp`: strictification is in fact *strict*, a 2-functor.

Main definitions:

* `Cwa.PbCat.toLaxCModel` — the strictified model of a category with pullbacks, as an object of the
  lax 2-category of models;
* `Cwa.strictificationPseudofunctor` — **strictification as a pseudofunctor** from the 2-category
  of categories with pullbacks to the lax 2-category of models.

Main results:

* `Cwa.strictificationPseudofunctor_mapId_hom`, `Cwa.strictificationPseudofunctor_mapComp_hom` —
  its structural isomorphisms are transports along equalities, so the pseudofunctor is strict;
* `Cwa.strictificationPseudofunctor_map₂_nat` — on 2-cells it is the identity on the underlying
  natural transformations, hence **locally fully faithful**
  (`Cwa.strictificationPseudofunctor_map₂_bijective`);
* `Cwa.strictificationPseudofunctor_map_injective` — it is faithful on 1-cells.
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Start.CwaStrictLaxWhisker
import Start.CwaLaxBicat
import Start.PbCatBicat

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace Cwa

/-- The component of a transport along an equality of functors, at an object whose images under
the two functors agree definitionally, is the identity. -/
theorem eqToHom_app_comp_self {C D : Type*} [Category C] [Category D] {F : C ⥤ D} (h : F = F)
    (X : C) {Z : D} (φ : F.obj X ⟶ Z) : (eqToHom h).app X ≫ φ = φ := by
  simp

/-- The strictified model of a category with pullbacks, as an object of the lax 2-category of
models. -/
@[reducible] noncomputable def PbCat.toLaxCModel (X : PbCat.{u, v}) : LaxCModel.{u, v, max u v} :=
  ⟨⟨X.Ctx, Cwa.ofPullbacks X.Ctx, extCoherent_ofPullbacks X.Ctx⟩⟩

@[simp] theorem PbCat.toLaxCModel_Ctx (X : PbCat.{u, v}) :
    (PbCat.toLaxCModel X).model.Ctx = X.Ctx := rfl

/-- The morphism of models induced by a pullback-preserving functor, as a 1-cell of the lax
2-category. -/
noncomputable abbrev strictMap {X Y : PbCat.{u, v}} (f : X ⟶ Y) :
    PbCat.toLaxCModel X ⟶ PbCat.toLaxCModel Y :=
  morOfPreservesPullbacks f.fnc

/-- The structural isomorphism of strictification at an identity: a transport along an equality. -/
noncomputable abbrev strictMapId (X : PbCat.{u, v}) :
    strictMap (𝟙 X) ≅ 𝟙 (PbCat.toLaxCModel X) :=
  LaxCModel.morEqToIso (morOfPreservesPullbacks_id (C := X.Ctx))

/-- The structural isomorphism of strictification at a composite: a transport along an equality. -/
noncomputable abbrev strictMapComp {X Y Z : PbCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    strictMap (f ≫ g) ≅ strictMap f ≫ strictMap g :=
  LaxCModel.morEqToIso (morOfPreservesPullbacks_comp f.fnc g.fnc)

/-- The comparison 2-cell of a composite is the identity on components. -/
@[simp] theorem strictMapComp_hom_nat_app {X Y Z : PbCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : X.Ctx) : (strictMapComp f g).hom.nat.app W = 𝟙 _ :=
  (LaxCModel.morEqToHom_nat_app (M := PbCat.toLaxCModel X) (N := PbCat.toLaxCModel Z)
    (morOfPreservesPullbacks_comp f.fnc g.fnc) W).trans (eqToHom_refl _ _)

/-- The inverse comparison 2-cell of a composite is the identity on components. -/
@[simp] theorem strictMapComp_inv_nat_app {X Y Z : PbCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : X.Ctx) : (strictMapComp f g).inv.nat.app W = 𝟙 _ :=
  (LaxCModel.morEqToHom_nat_app (M := PbCat.toLaxCModel X) (N := PbCat.toLaxCModel Z)
    (morOfPreservesPullbacks_comp f.fnc g.fnc).symm W).trans (eqToHom_refl _ _)

/-- The comparison 2-cell of an identity is the identity on components. -/
@[simp] theorem strictMapId_hom_nat_app (X : PbCat.{u, v}) (W : X.Ctx) :
    (strictMapId X).hom.nat.app W = 𝟙 _ :=
  (LaxCModel.morEqToHom_nat_app (M := PbCat.toLaxCModel X) (N := PbCat.toLaxCModel X)
    (morOfPreservesPullbacks_id (C := X.Ctx)) W).trans (eqToHom_refl _ _)

/-- The inverse comparison 2-cell of an identity is the identity on components. -/
@[simp] theorem strictMapId_inv_nat_app (X : PbCat.{u, v}) (W : X.Ctx) :
    (strictMapId X).inv.nat.app W = 𝟙 _ :=
  (LaxCModel.morEqToHom_nat_app (M := PbCat.toLaxCModel X) (N := PbCat.toLaxCModel X)
    (morOfPreservesPullbacks_id (C := X.Ctx)).symm W).trans (eqToHom_refl _ _)

/-- The lax 2-cell induced by a 2-cell of categories with pullbacks. -/
noncomputable abbrev strictMap₂ {X Y : PbCat.{u, v}} {f g : X ⟶ Y} (τ : f ⟶ g) :
    strictMap f ⟶ strictMap g :=
  laxTwoCellOfNatTrans τ

/-- **Strictification as a pseudofunctor**: a category with pullbacks is a model of a dependent
type theory, a pullback-preserving functor a morphism of models, and a natural transformation a lax
2-cell, compatibly with all the composition operations of the two 2-categories. -/
noncomputable def strictificationPseudofunctor :
    Pseudofunctor PbCat.{u, v} LaxCModel.{u, v, max u v} where
  obj := PbCat.toLaxCModel
  map f := strictMap f
  mapId X := strictMapId X
  mapComp f g := strictMapComp f g
  map₂ τ := strictMap₂ τ
  map₂_id := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    rfl
  map₂_comp := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    rfl
  map₂_whisker_left := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    simp only [LaxCModel.comp_nat, PbCat.bicategoryWhiskerLeft_eq,
      laxTwoCellOfNatTrans_nat, LaxCModel.bicategoryWhiskerLeft_nat]
    repeat erw [NatTrans.comp_app]
    simp [Functor.whiskerLeft_app, strictMapComp_hom_nat_app,
      strictMapComp_inv_nat_app]
  map₂_whisker_right := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    simp only [LaxCModel.comp_nat, PbCat.bicategoryWhiskerRight_eq,
      laxTwoCellOfNatTrans_nat, LaxCModel.bicategoryWhiskerRight_nat]
    repeat erw [NatTrans.comp_app]
    simp [Functor.whiskerRight_app, strictMapComp_hom_nat_app,
      strictMapComp_inv_nat_app]
  map₂_associator := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    simp only [LaxCModel.comp_nat, laxTwoCellOfNatTrans_nat,
      LaxCModel.bicategoryWhiskerLeft_nat, LaxCModel.bicategoryWhiskerRight_nat,
      Bicategory.Strict.associator_eqToIso]
    repeat erw [NatTrans.comp_app]
    simp only [morOfPreservesPullbacks_fnc, PbCat.comp_fnc, Functor.comp_obj, eqToIso_refl,
      Iso.refl_hom, PbCat.id_app, LaxCModel.comp_fnc, strictMapComp_hom_nat_app, eqToIso.hom,
      LaxCModel.eqToHom_nat, strictMapComp_inv_nat_app, Category.comp_id, Category.id_comp]
    erw [Functor.whiskerRight_app, eqToHom_app, Functor.whiskerLeft_app]
    simp
  map₂_left_unitor := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    simp only [LaxCModel.comp_nat, laxTwoCellOfNatTrans_nat,
      LaxCModel.bicategoryWhiskerRight_nat, Bicategory.Strict.leftUnitor_eqToIso]
    repeat erw [NatTrans.comp_app]
    simp only [morOfPreservesPullbacks_fnc, PbCat.comp_fnc, PbCat.id_fnc, Functor.comp_obj,
      Functor.id_obj, eqToIso_refl, Iso.refl_hom, PbCat.id_app, LaxCModel.comp_fnc,
      strictMapComp_hom_nat_app, LaxCModel.id_fnc, eqToIso.hom, LaxCModel.eqToHom_nat,
      Category.id_comp]
    erw [Functor.whiskerRight_app, eqToHom_app]
    simp
  map₂_right_unitor := by
    intros
    refine LaxTwoCell.ext_of_nat ?_
    ext X
    simp only [LaxCModel.comp_nat, laxTwoCellOfNatTrans_nat,
      LaxCModel.bicategoryWhiskerLeft_nat, Bicategory.Strict.rightUnitor_eqToIso]
    repeat erw [NatTrans.comp_app]
    simp only [morOfPreservesPullbacks_fnc, PbCat.comp_fnc, PbCat.id_fnc, Functor.comp_obj,
      Functor.id_obj, eqToIso_refl, Iso.refl_hom, PbCat.id_app, LaxCModel.comp_fnc,
      strictMapComp_hom_nat_app, LaxCModel.id_fnc, eqToIso.hom, LaxCModel.eqToHom_nat,
      Category.id_comp]
    erw [Functor.whiskerLeft_app, eqToHom_app]
    simp

@[simp] theorem strictificationPseudofunctor_obj (X : PbCat.{u, v}) :
    strictificationPseudofunctor.obj X = PbCat.toLaxCModel X := rfl

/-- **On 2-cells, strictification is the identity on the underlying natural transformations.** -/
@[simp] theorem strictificationPseudofunctor_map₂_nat {X Y : PbCat.{u, v}} {f g : X ⟶ Y}
    (τ : f ⟶ g) :
    (strictificationPseudofunctor.map₂ τ : LaxTwoCell (strictificationPseudofunctor.map f)
      (strictificationPseudofunctor.map g)).nat = (τ : f.fnc ⟶ g.fnc) := rfl

/-- The structural isomorphism at an identity is a transport along an equality: the pseudofunctor
is strict. -/
theorem strictificationPseudofunctor_mapId (X : PbCat.{u, v}) :
    strictificationPseudofunctor.mapId X
      = LaxCModel.morEqToIso (morOfPreservesPullbacks_id (C := X.Ctx)) := rfl

/-- The structural isomorphism at a composite is a transport along an equality: the pseudofunctor
is strict. -/
theorem strictificationPseudofunctor_mapComp {X Y Z : PbCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    strictificationPseudofunctor.mapComp f g
      = LaxCModel.morEqToIso (morOfPreservesPullbacks_comp f.fnc g.fnc) := rfl

/-- **Strictification is faithful on 1-cells**: two pullback-preserving functors inducing the same
morphism of models are equal. -/
theorem strictificationPseudofunctor_map_injective (X Y : PbCat.{u, v}) :
    Function.Injective (fun f : X ⟶ Y => strictificationPseudofunctor.map f) := by
  intro f g h
  exact PbCat.Hom.ext (congrArg Mor.fnc h)

/-- **Strictification is locally fully faithful**: between two pullback-preserving functors, the
natural transformations are exactly the lax 2-cells of the induced morphisms of models. -/
theorem strictificationPseudofunctor_map₂_bijective {X Y : PbCat.{u, v}} (f g : X ⟶ Y) :
    Function.Bijective (fun τ : f ⟶ g => strictificationPseudofunctor.map₂ τ) := by
  constructor
  · intro τ υ h
    exact congrArg (fun θ : strictMap f ⟶ strictMap g =>
      (θ : LaxTwoCell (strictMap f) (strictMap g)).nat) h
  · intro θ
    exact ⟨(θ : LaxTwoCell (strictMap f) (strictMap g)).nat, LaxTwoCell.ext_of_nat rfl⟩

end Cwa
