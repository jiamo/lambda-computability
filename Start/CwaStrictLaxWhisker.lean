/-
**Strictification is 2-functorial for the lax 2-cells, horizontally as well as vertically.**

`Start/CwaStrictLax.lean` attaches to a natural transformation of pullback-preserving functors a
lax 2-cell between the induced morphisms of models (`Cwa.laxTwoCellOfNatTrans`) and proves that
the assignment preserves the identity and the *vertical* composition.  That is only the
one-dimensional half of 2-functoriality; the other half is compatibility with *whiskering*, which
could not even be stated before the interchange law of `Start/CwaLaxInterchange.lean` was
available.

Both statements are up to the transports along `Cwa.morOfPreservesPullbacks_comp`, the equality of
morphisms of models expressing that strictification preserves composition on the nose.

Main definitions:

* `Cwa.laxEqToHom` — the lax 2-cell transporting along an equality of morphisms of models.

Main results:

* `Cwa.laxTwoCellOfNatTrans_eq_ofNat` — the lax 2-cell of a natural transformation is *the* lax
  2-cell with that natural transformation (there is only one, by
  `Cwa.LaxTwoCell.ext_of_nat`);
* `Cwa.laxTwoCellOfNatTrans_whiskerLeft`, `Cwa.laxTwoCellOfNatTrans_whiskerRight` —
  **strictification carries whiskering to whiskering**, so, with the results of
  `Start/CwaStrictLax.lean`, it is 2-functorial for the lax 2-cells in both dimensions.
-/

import Start.CwaLaxRigid
import Start.CwaLaxInterchange
import Start.CwaStrictLax
import Start.CwaStrictFunctor

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v u' v' u'' v'' u₁ v₁ w₁ u₂ v₂ w₂

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- The lax 2-cell transporting along an equality of morphisms of models: the `eqToHom` of the
category of lax 2-cells, spelled out so that it can be used without instance search. -/
noncomputable def laxEqToHom {C₀ : Type u₁} [Category.{v₁} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    {T : Cwa.{u₁, v₁, w₁} C₀} {S : Cwa.{u₂, v₂, w₂} D₀} (coh : ExtCoherent S) {F G : Mor T S}
    (h : F = G) : LaxTwoCell F G :=
  @eqToHom (Mor T S) (laxMorCategory coh).toCategoryStruct F G h

@[simp] theorem laxEqToHom_nat {C₀ : Type u₁} [Category.{v₁} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    {T : Cwa.{u₁, v₁, w₁} C₀} {S : Cwa.{u₂, v₂, w₂} D₀} (coh : ExtCoherent S) {F G : Mor T S}
    (h : F = G) : (laxEqToHom coh h).nat = eqToHom (congrArg Mor.fnc h) := by
  subst h
  rfl

section Strictification

variable [HasPullbacks C] [HasPullbacks D] [HasPullbacks E]

@[simp] theorem morOfPreservesPullbacks_fnc (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] : (morOfPreservesPullbacks F).fnc = F := rfl

/-- **The lax 2-cell attached to a natural transformation is the only one with that natural
transformation.** -/
theorem laxTwoCellOfNatTrans_eq_ofNat {F G : C ⥤ D} [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape WalkingCospan G] (τ : F ⟶ G) :
    laxTwoCellOfNatTrans τ
      = LaxTwoCell.ofNat (morOfPreservesPullbacks F) (morOfPreservesPullbacks G) τ :=
  LaxTwoCell.ext_of_nat rfl

/-- **Strictification carries left whiskering to left whiskering**, up to the transports
identifying the morphism of models induced by a composite of functors with the composite of the
induced morphisms. -/
theorem laxTwoCellOfNatTrans_whiskerLeft (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {G H : D ⥤ E} [PreservesLimitsOfShape WalkingCospan G]
    [PreservesLimitsOfShape WalkingCospan H] (τ : G ⟶ H) :
    laxTwoCellOfNatTrans (Functor.whiskerLeft F τ)
      = (laxEqToHom (extCoherent_ofPullbacks E) (morOfPreservesPullbacks_comp F G)).vcomp
          (extCoherent_ofPullbacks E)
          ((LaxTwoCell.whiskerLeft (morOfPreservesPullbacks F)
              (laxTwoCellOfNatTrans τ)).vcomp (extCoherent_ofPullbacks E)
            (laxEqToHom (extCoherent_ofPullbacks E)
              (morOfPreservesPullbacks_comp F H).symm)) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp only [LaxTwoCell.vcomp_nat, laxEqToHom_nat, NatTrans.comp_app,
    LaxTwoCell.whiskerLeft_nat, laxTwoCellOfNatTrans_nat, Functor.whiskerLeft_app,
    morOfPreservesPullbacks_fnc]
  exact ((Category.id_comp _).trans (Category.comp_id (τ.app (F.obj X)))).symm

/-- **Strictification carries right whiskering to right whiskering**, up to the same
transports. -/
theorem laxTwoCellOfNatTrans_whiskerRight {F G : C ⥤ D}
    [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G] (τ : F ⟶ G)
    (H : D ⥤ E) [PreservesLimitsOfShape WalkingCospan H] :
    laxTwoCellOfNatTrans (Functor.whiskerRight τ H)
      = (laxEqToHom (extCoherent_ofPullbacks E) (morOfPreservesPullbacks_comp F H)).vcomp
          (extCoherent_ofPullbacks E)
          ((LaxTwoCell.whiskerRight (laxTwoCellOfNatTrans τ)
              (morOfPreservesPullbacks H)).vcomp (extCoherent_ofPullbacks E)
            (laxEqToHom (extCoherent_ofPullbacks E)
              (morOfPreservesPullbacks_comp G H).symm)) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp only [LaxTwoCell.vcomp_nat, laxEqToHom_nat, NatTrans.comp_app,
    LaxTwoCell.whiskerRight_nat, laxTwoCellOfNatTrans_nat, Functor.whiskerRight_app,
    morOfPreservesPullbacks_fnc]
  exact ((Category.id_comp _).trans (Category.comp_id (H.map (τ.app X)))).symm

end Strictification

end Cwa
