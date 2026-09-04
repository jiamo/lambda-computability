/-
**Strictification is 2-functorial for the lax 2-cells.**

`Start/CwaStrictRigid.lean` shows that the strictification of a category with pullbacks cannot be
made 2-functorial for the strict 2-cells of `Start/CwaTwoCell.lean`: a 2-cell between two
strictified morphisms forces the two functors to agree on objects, and
`Cwa.isEmpty_twoCell_id_coyoneda` exhibits a natural transformation of pullback-preserving
endofunctors of `Type` inducing no 2-cell whatsoever.  Its conclusion was that a pseudofunctor to
the bicategory of models must weaken either the morphisms or the 2-cells.

This module carries out the second weakening.  With the lax 2-cells of
`Start/CwaLaxTwoCell.lean` — where the equality of types is replaced by a map of extended contexts
over the base — the 2-dimensional structure *is* preserved:

* `Cwa.luCmp` — the comparison attached to a natural transformation `τ : F ⟶ G` of
  pullback-preserving functors: on the extended context of a local universe it is the identity on
  the base and `τ` on the total space, and it exists because `τ` is natural;
* `Cwa.laxTwoCellOfNatTrans` — **a natural transformation of pullback-preserving functors induces
  a lax 2-cell between the morphisms of models they induce**;
* `Cwa.laxTwoCellOfNatTrans_id`, `Cwa.laxTwoCellOfNatTrans_comp` — and it does so *functorially*:
  the identity goes to the identity lax 2-cell and a composite to the vertical composite, so
  strictification is 2-functorial for the lax 2-cells;
* `Cwa.nonempty_laxTwoCell_id_coyoneda` — in particular the natural transformation of
  `Start/CwaStrictRigid.lean`, which admits no strict 2-cell at all, does induce a lax one.
-/

import Start.CwaLaxTwoCell
import Start.CwaStrictRigid

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v u' v'

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {D : Type u'} [Category.{v'} D] [HasPullbacks D]
  {F G H : C ⥤ D} [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G] [PreservesLimitsOfShape WalkingCospan H]

/-! ### The comparison attached to a natural transformation -/

/-- **The comparison of extended contexts attached to a natural transformation** `τ : F ⟶ G`: the
extended context of the local universe `A` read through `F` maps to the extended context of the
same local universe read through `G` and substituted along `τ`, by the identity on the base and by
`τ` on the total space.  Naturality of `τ` is exactly the compatibility the pullback asks for. -/
noncomputable def luCmp (τ : F ⟶ G) (Γ : C) (A : LuTy Γ) :
    LuTy.ext (F.obj Γ) (luMap F A) ⟶ LuTy.ext (F.obj Γ) (LuTy.sub (τ.app Γ) (luMap G A)) :=
  (LuTy.isPullback_gen (LuTy.sub (τ.app Γ) (luMap G A))).lift
    (LuTy.gen (luMap F A) ≫ τ.app A.total) (LuTy.disp (luMap F A)) (by
      have hproj := τ.naturality A.proj
      have hcls := τ.naturality A.cls
      have hpb := LuTy.disp_cls (luMap F A)
      simp only [luMap, LuTy.sub] at hproj hcls hpb ⊢
      rw [← hcls, ← Category.assoc, hpb, Category.assoc, ← hproj, ← Category.assoc])

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G] in
@[reassoc] theorem luCmp_gen (τ : F ⟶ G) (Γ : C) (A : LuTy Γ) :
    luCmp τ Γ A ≫ LuTy.gen (LuTy.sub (τ.app Γ) (luMap G A))
      = LuTy.gen (luMap F A) ≫ τ.app A.total :=
  (LuTy.isPullback_gen _).lift_fst _ _ _

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G] in
@[reassoc] theorem luCmp_disp (τ : F ⟶ G) (Γ : C) (A : LuTy Γ) :
    luCmp τ Γ A ≫ LuTy.disp (LuTy.sub (τ.app Γ) (luMap G A)) = LuTy.disp (luMap F A) :=
  (LuTy.isPullback_gen _).lift_snd _ _ _

/-! ### The induced lax 2-cell -/

/-- **A natural transformation of pullback-preserving functors induces a lax 2-cell** between the
morphisms of models they induce.  This is what fails for the strict 2-cells. -/
noncomputable def laxTwoCellOfNatTrans (τ : F ⟶ G) :
    LaxTwoCell (morOfPreservesPullbacks F) (morOfPreservesPullbacks G) where
  nat := τ
  cmp Γ A := luCmp τ Γ A
  cmp_disp Γ A := luCmp_disp τ Γ A
  extend_app Γ A := by
    simp only [morOfPreservesPullbacks, morOfPullbackPreserving]
    refine (LuTy.isPullback_gen (luMap G A)).hom_ext ?_ ?_
    · simp only [Category.assoc, LuTy.extend_gen]
      rw [luCmp_gen, ← Category.assoc, luExtIso_hom_gen, luExtIso_hom_gen]
      exact τ.naturality (LuTy.gen A)
    · simp only [Category.assoc, LuTy.extend_disp]
      rw [luCmp_disp_assoc, ← Category.assoc, luExtIso_hom_disp, luExtIso_hom_disp]
      exact τ.naturality (LuTy.disp A)

@[simp] theorem laxTwoCellOfNatTrans_nat (τ : F ⟶ G) : (laxTwoCellOfNatTrans τ).nat = τ := rfl

/-! ### Functoriality -/

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G] in
/-- **The identity natural transformation has the transport for its comparison.** -/
theorem luCmp_id (Γ : C) (A : LuTy Γ)
    (e : luMap F A = LuTy.sub (NatTrans.app (𝟙 F) Γ) (luMap F A)) :
    luCmp (𝟙 F) Γ A = eqToHom (congrArg (LuTy.ext (F.obj Γ)) e) := by
  refine (LuTy.isPullback_gen _).hom_ext ?_ ?_
  · rw [luCmp_gen, show NatTrans.app (𝟙 F) A.total = 𝟙 (F.obj A.total) from rfl,
      Category.comp_id, eqToHom_lu_gen e,
      Subsingleton.elim (congrArg LuTy.total e) rfl, eqToHom_refl, Category.comp_id]
  · rw [luCmp_disp, eqToHom_lu_disp e]

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G] [PreservesLimitsOfShape WalkingCospan H] in
/-- **The comparison of a composite is the composite of the comparisons**, the second one being
substituted along the first component. -/
theorem luCmp_comp (τ : F ⟶ G) (υ : G ⟶ H) (Γ : C) (A : LuTy Γ)
    (e : LuTy.sub (τ.app Γ) (LuTy.sub (υ.app Γ) (luMap H A))
      = LuTy.sub (NatTrans.app (τ ≫ υ) Γ) (luMap H A)) :
    luCmp (τ ≫ υ) Γ A
      = luCmp τ Γ A ≫ (ofPullbacks D).subOver (τ.app Γ) (luCmp υ Γ A) (luCmp_disp υ Γ A)
          ≫ eqToHom (congrArg (LuTy.ext (F.obj Γ)) e) := by
  refine (LuTy.isPullback_gen _).hom_ext ?_ ?_
  · rw [luCmp_gen, Category.assoc, Category.assoc, eqToHom_lu_gen e,
      Subsingleton.elim (congrArg LuTy.total e) rfl,
      eqToHom_refl, Category.comp_id, ← LuTy.extend_gen, subOver_extend_assoc, luCmp_gen,
      ← Category.assoc (LuTy.extend (τ.app Γ) (luMap G A)), LuTy.extend_gen, ← Category.assoc,
      luCmp_gen, Category.assoc]
    rfl
  · rw [luCmp_disp, Category.assoc, Category.assoc, eqToHom_lu_disp e, subOver_disp, luCmp_disp]

omit [PreservesLimitsOfShape WalkingCospan G] in
/-- **The identity natural transformation induces the identity lax 2-cell.** -/
theorem laxTwoCellOfNatTrans_id :
    laxTwoCellOfNatTrans (𝟙 F)
      = LaxTwoCell.id (extCoherent_ofPullbacks D) (morOfPreservesPullbacks F) :=
  LaxTwoCell.ext_of_nat_eq rfl
    (heq_of_eq (funext fun Γ => funext fun A => luCmp_id Γ A (LuTy.sub_id (luMap F A)).symm))

/-- **A composite of natural transformations induces the vertical composite of the lax 2-cells.**
Together with the previous theorem: strictification is 2-functorial for the lax 2-cells. -/
theorem laxTwoCellOfNatTrans_comp (τ : F ⟶ G) (υ : G ⟶ H) :
    laxTwoCellOfNatTrans (τ ≫ υ)
      = (laxTwoCellOfNatTrans τ).vcomp (extCoherent_ofPullbacks D) (laxTwoCellOfNatTrans υ) :=
  LaxTwoCell.ext_of_nat_eq rfl
    (heq_of_eq (funext fun Γ => funext fun A =>
      luCmp_comp τ υ Γ A (LuTy.sub_comp (υ.app Γ) (τ.app Γ) (luMap H A)).symm))

/-! ### The 2-dimensional structure is recovered -/

/-- **The natural transformation that admits no 2-cell admits a lax one.**  Compare
`Cwa.isEmpty_twoCell_id_coyoneda`: the obstruction to 2-functoriality of the strictification is the
strictness of the 2-cells, and nothing else. -/
theorem nonempty_laxTwoCell_id_coyoneda :
    Nonempty (LaxTwoCell (morOfPreservesPullbacks (𝟭 Type)) (morOfPreservesPullbacks emptyPow)) :=
  ⟨laxTwoCellOfNatTrans coyonedaConst⟩

end Cwa
