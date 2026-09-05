/-
**The models of a dependent type theory form a 2-category with the lax 2-cells.**

`Start/CwaBicat.lean` assembles the coherent models, their morphisms and the *strict* 2-cells into
a `CategoryTheory.Bicategory`.  For the strict 2-cells that is not the 2-category one wants:
`Start/CwaStrictRigid.lean` shows that strictification of a category with pullbacks is not
2-functorial for them, because a natural transformation of pullback-preserving functors need not
induce a strict 2-cell at all.

The lax 2-cells of `Start/CwaLaxTwoCell.lean` repair that, and this module shows that they do so
without losing any 2-categorical structure: the vertical composition is a category
(`Start/CwaLaxCategory.lean`), the whiskerings are functorial (`Start/CwaLaxWhisker.lean`) and they
interchange (`Start/CwaLaxInterchange.lean`), so all the axioms of a bicategory hold — and, exactly
as in the strict case, composition of morphisms of models is strictly associative and unital, so
the resulting bicategory is `CategoryTheory.Bicategory.Strict`.

Main definitions:

* `Cwa.LaxCModel` — a coherent model, as an object of the *lax* 2-category (a one-field wrapper
  around `Cwa.CModel`, so that the hom-categories are the lax 2-cells and not the strict ones);
* `Cwa.LaxCModel.instBicategory` — **the 2-category of models, morphisms and lax 2-cells**.

Main results:

* `Cwa.LaxCModel.instStrict` — the 2-category is strict;
* `Cwa.LaxCModel.hom_ext` — a 2-cell of it is determined by its natural transformation;
* `Cwa.LaxCModel.homEquivNatTrans` — the 2-cells between two 1-cells are exactly the natural
  transformations of the underlying functors on contexts;
* `Cwa.LaxCModel.isIso_of_isIso_nat` — a 2-cell whose natural transformation is invertible is an
  isomorphism of the hom-category.
-/

import Start.CwaLaxInterchange
import Start.CwaBicat

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Cwa

-- As for `CategoryTheory.Cat`, the three universes are independent but the linter only sees them
-- inside a `max`; mathlib disables the check for `Cat` in the same way.
set_option linter.checkUnivs false in
/-- A coherent model of a dependent type theory, read as an **object of the lax 2-category**: the
same data as `Cwa.CModel`, wrapped so that the hom-categories are the lax 2-cells rather than the
strict ones. -/
structure LaxCModel where
  /-- The underlying coherent model. -/
  model : CModel.{u, v, w}

namespace LaxCModel

/-- A coherent model, as an object of the lax 2-category. -/
def of (M : CModel.{u, v, w}) : LaxCModel.{u, v, w} := ⟨M⟩

@[simp] theorem model_of (M : CModel.{u, v, w}) : (of M).model = M := rfl

/-- The 1-cells of the lax 2-category of models: the morphisms of categories with attributes.  It
is not declared as an instance; the 1-cells are found through the bicategory below, so that the
lemmas about 2-cells are stated for the same composition as the goals they have to close. -/
@[instance_reducible]
def laxCategoryStruct : CategoryStruct.{max u v w} LaxCModel.{u, v, w} where
  Hom M N := Mor M.model.str N.model.str
  id M := Mor.id M.model.str
  comp F G := F.comp G

/-- **The 1-cells between two models form a category**, the lax 2-cells being its morphisms.  It is
not declared as an instance: the hom-categories of the 2-category below are found through
`CategoryTheory.Bicategory.homCategory`, and a second instance for the same type would make the
statements of the lemmas about 2-cells depend on which one is picked. -/
@[instance_reducible]
noncomputable def laxHomCategory (M N : LaxCModel.{u, v, w}) :
    Category.{max u v w} (Mor M.model.str N.model.str) :=
  laxMorCategory N.model.coh

/-- The isomorphism of 1-cells transporting along an equality, in the category of lax 2-cells. -/
noncomputable def morEqToIso {M N : LaxCModel.{u, v, w}} {F G : Mor M.model.str N.model.str}
    (h : F = G) : @Iso (Mor M.model.str N.model.str) (laxHomCategory M N) F G :=
  @eqToIso (Mor M.model.str N.model.str) (laxHomCategory M N) F G h

section BicatAxioms

variable {M N P Q : LaxCModel.{u, v, w}}

/-- The lax 2-cell transporting along an equality of morphisms of models.  It is the `eqToHom` of
the category of morphisms, spelled out so that the axioms of the 2-category can be stated without
appealing to instance search for the hom-categories. -/
noncomputable abbrev morEqToHom {F G : Mor M.model.str N.model.str} (h : F = G) :
    LaxTwoCell F G :=
  @eqToHom (Mor M.model.str N.model.str) (laxMorCategory N.model.coh).toCategoryStruct F G h

@[simp] theorem morEqToHom_nat_app {F G : Mor M.model.str N.model.str} (h : F = G)
    (X : M.model.Ctx) :
    (morEqToHom h).nat.app X = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- Whiskering an identity lax 2-cell on the left is an identity. -/
theorem whiskerLeft_id' (F : Mor M.model.str N.model.str) (G : Mor N.model.str P.model.str) :
    LaxTwoCell.whiskerLeft F (LaxTwoCell.id P.model.coh G)
      = LaxTwoCell.id P.model.coh (F.comp G) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering on the left is functorial in the lax 2-cell. -/
theorem whiskerLeft_comp' (F : Mor M.model.str N.model.str)
    {G H K : Mor N.model.str P.model.str} (θ : LaxTwoCell G H) (ψ : LaxTwoCell H K) :
    LaxTwoCell.whiskerLeft F (θ.vcomp P.model.coh ψ)
      = (LaxTwoCell.whiskerLeft F θ).vcomp P.model.coh (LaxTwoCell.whiskerLeft F ψ) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering by the identity morphism, up to the left unitor. -/
theorem id_whiskerLeft' {F G : Mor M.model.str N.model.str} (θ : LaxTwoCell F G) :
    LaxTwoCell.whiskerLeft (Mor.id M.model.str) θ
      = (morEqToHom (Mor.id_comp F)).vcomp N.model.coh
          (θ.vcomp N.model.coh (morEqToHom (Mor.id_comp G).symm)) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering by a composite, up to the associator. -/
theorem comp_whiskerLeft' (F : Mor M.model.str N.model.str) (G : Mor N.model.str P.model.str)
    {H K : Mor P.model.str Q.model.str} (θ : LaxTwoCell H K) :
    LaxTwoCell.whiskerLeft (F.comp G) θ
      = (morEqToHom (Mor.assoc F G H)).vcomp Q.model.coh
          ((LaxTwoCell.whiskerLeft F (LaxTwoCell.whiskerLeft G θ)).vcomp Q.model.coh
            (morEqToHom (Mor.assoc F G K).symm)) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering an identity lax 2-cell on the right is an identity. -/
theorem id_whiskerRight' (F : Mor M.model.str N.model.str) (G : Mor N.model.str P.model.str) :
    LaxTwoCell.whiskerRight (LaxTwoCell.id N.model.coh F) G
      = LaxTwoCell.id P.model.coh (F.comp G) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering on the right is functorial in the lax 2-cell. -/
theorem comp_whiskerRight' {F G H : Mor M.model.str N.model.str} (θ : LaxTwoCell F G)
    (ψ : LaxTwoCell G H) (K : Mor N.model.str P.model.str) :
    LaxTwoCell.whiskerRight (θ.vcomp N.model.coh ψ) K
      = (LaxTwoCell.whiskerRight θ K).vcomp P.model.coh (LaxTwoCell.whiskerRight ψ K) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering by the identity morphism, up to the right unitor. -/
theorem whiskerRight_id' {F G : Mor M.model.str N.model.str} (θ : LaxTwoCell F G) :
    LaxTwoCell.whiskerRight θ (Mor.id N.model.str)
      = (morEqToHom (Mor.comp_id F)).vcomp N.model.coh
          (θ.vcomp N.model.coh (morEqToHom (Mor.comp_id G).symm)) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Whiskering by a composite on the right, up to the associator. -/
theorem whiskerRight_comp' {F G : Mor M.model.str N.model.str} (θ : LaxTwoCell F G)
    (H : Mor N.model.str P.model.str) (K : Mor P.model.str Q.model.str) :
    LaxTwoCell.whiskerRight θ (H.comp K)
      = (morEqToHom (Mor.assoc F H K).symm).vcomp Q.model.coh
          ((LaxTwoCell.whiskerRight (LaxTwoCell.whiskerRight θ H) K).vcomp Q.model.coh
            (morEqToHom (Mor.assoc G H K))) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- Left and right whiskering associate, up to the associator. -/
theorem whisker_assoc' (F : Mor M.model.str N.model.str) {G H : Mor N.model.str P.model.str}
    (θ : LaxTwoCell G H) (K : Mor P.model.str Q.model.str) :
    LaxTwoCell.whiskerRight (LaxTwoCell.whiskerLeft F θ) K
      = (morEqToHom (Mor.assoc F G K)).vcomp Q.model.coh
          ((LaxTwoCell.whiskerLeft F (LaxTwoCell.whiskerRight θ K)).vcomp Q.model.coh
            (morEqToHom (Mor.assoc F H K).symm)) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- **The pentagon identity** for the transports along associativity. -/
theorem pentagon' (F : Mor M.model.str N.model.str) (G : Mor N.model.str P.model.str)
    (H : Mor P.model.str Q.model.str) {R : LaxCModel.{u, v, w}}
    (K : Mor Q.model.str R.model.str) :
    (LaxTwoCell.whiskerRight (morEqToHom (Mor.assoc F G H)) K).vcomp R.model.coh
        ((morEqToHom (Mor.assoc F (G.comp H) K)).vcomp R.model.coh
          (LaxTwoCell.whiskerLeft F (morEqToHom (Mor.assoc G H K))))
      = (morEqToHom (Mor.assoc (F.comp G) H K)).vcomp R.model.coh
          (morEqToHom (Mor.assoc F G (H.comp K))) := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

/-- **The triangle identity** for the transports along the unit laws. -/
theorem triangle' (F : Mor M.model.str N.model.str) (G : Mor N.model.str P.model.str) :
    (morEqToHom (Mor.assoc F (Mor.id N.model.str) G)).vcomp P.model.coh
        (LaxTwoCell.whiskerLeft F (morEqToHom (Mor.id_comp G)))
      = LaxTwoCell.whiskerRight (morEqToHom (Mor.comp_id F)) G := by
  refine LaxTwoCell.ext_of_nat ?_
  ext X
  simp

end BicatAxioms

/-- **The models, their morphisms and the lax 2-cells between them form a 2-category.**  This is
what the strict 2-cells cannot give: with them the strictification of a category with pullbacks is
not 2-functorial, while a natural transformation of pullback-preserving functors does induce a lax
2-cell, functorially (`Cwa.laxTwoCellOfNatTrans`). -/
noncomputable instance instBicategory :
    Bicategory.{max u v w, max u v w} LaxCModel.{u, v, w} where
  toCategoryStruct := laxCategoryStruct
  homCategory := laxHomCategory
  whiskerLeft F _ _ θ := LaxTwoCell.whiskerLeft F θ
  whiskerRight θ H := LaxTwoCell.whiskerRight θ H
  associator F G H := morEqToIso (Mor.assoc F G H)
  leftUnitor F := morEqToIso (Mor.id_comp F)
  rightUnitor F := morEqToIso (Mor.comp_id F)
  whiskerLeft_id := by intros; exact whiskerLeft_id' _ _
  whiskerLeft_comp := by intros; exact whiskerLeft_comp' _ _ _
  id_whiskerLeft := by intros; exact id_whiskerLeft' _
  comp_whiskerLeft := by intros; exact comp_whiskerLeft' _ _ _
  id_whiskerRight := by intros; exact id_whiskerRight' _ _
  comp_whiskerRight := by intros; exact comp_whiskerRight' _ _ _
  whiskerRight_id := by intros; exact whiskerRight_id' _
  whiskerRight_comp := by intros; exact whiskerRight_comp' _ _ _
  whisker_assoc := by intros; exact whisker_assoc' _ _ _
  whisker_exchange := by intros; exact LaxTwoCell.whisker_exchange _ _ _
  pentagon := by intros; exact pentagon' _ _ _ _
  triangle := by intros; exact triangle' _ _

/-- **The lax 2-category of models is strict**: its associators and unitors come from
equalities. -/
instance instStrict : Bicategory.Strict LaxCModel.{u, v, w} where
  id_comp := Mor.id_comp
  comp_id := Mor.comp_id
  assoc := Mor.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

@[simp] theorem id_fnc (M : LaxCModel.{u, v, w}) : (𝟙 M : M ⟶ M).fnc = 𝟭 M.model.Ctx := rfl

@[simp] theorem comp_fnc {M N P : LaxCModel.{u, v, w}} (F : M ⟶ N) (G : N ⟶ P) :
    (F ≫ G).fnc = F.fnc ⋙ G.fnc := rfl

@[simp] theorem id_nat {M N : LaxCModel.{u, v, w}} (F : M ⟶ N) :
    (𝟙 F : LaxTwoCell F F).nat = 𝟙 F.fnc := rfl

@[simp] theorem comp_nat {M N : LaxCModel.{u, v, w}} {F G H : M ⟶ N} (θ : F ⟶ G) (ψ : G ⟶ H) :
    (θ ≫ ψ : LaxTwoCell F H).nat = (θ : LaxTwoCell F G).nat ≫ (ψ : LaxTwoCell G H).nat := rfl

@[simp] theorem id_nat_app {M N : LaxCModel.{u, v, w}} (F : M ⟶ N) (X : M.model.Ctx) :
    (𝟙 F : LaxTwoCell F F).nat.app X = 𝟙 (F.fnc.obj X) := rfl

@[simp] theorem comp_nat_app {M N : LaxCModel.{u, v, w}} {F G H : M ⟶ N} (θ : F ⟶ G) (ψ : G ⟶ H)
    (X : M.model.Ctx) :
    (θ ≫ ψ : LaxTwoCell F H).nat.app X
      = (θ : LaxTwoCell F G).nat.app X ≫ (ψ : LaxTwoCell G H).nat.app X := rfl

@[simp] theorem whiskerLeft_nat_app {M N P : LaxCModel.{u, v, w}} (F : M ⟶ N) {G H : N ⟶ P}
    (θ : G ⟶ H) (X : M.model.Ctx) :
    (LaxTwoCell.whiskerLeft F θ).nat.app X = (θ : LaxTwoCell G H).nat.app (F.fnc.obj X) := rfl

@[simp] theorem whiskerRight_nat_app {M N P : LaxCModel.{u, v, w}} {F G : M ⟶ N} (θ : F ⟶ G)
    (H : N ⟶ P) (X : M.model.Ctx) :
    (LaxTwoCell.whiskerRight θ H).nat.app X = H.fnc.map ((θ : LaxTwoCell F G).nat.app X) := rfl

@[simp] theorem eqToHom_nat {M N : LaxCModel.{u, v, w}} {F G : M ⟶ N} (h : F = G) :
    (eqToHom h : LaxTwoCell F G).nat = eqToHom (congrArg Mor.fnc h) := by
  subst h
  rfl

@[simp] theorem eqToHom_nat_app {M N : LaxCModel.{u, v, w}} {F G : M ⟶ N} (h : F = G)
    (X : M.model.Ctx) : (eqToHom h : LaxTwoCell F G).nat.app X = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp] theorem bicategoryWhiskerLeft_nat {M N P : LaxCModel.{u, v, w}} (F : M ⟶ N) {G H : N ⟶ P}
    (θ : G ⟶ H) :
    (Bicategory.whiskerLeft F θ : LaxTwoCell (F ≫ G) (F ≫ H)).nat
      = Functor.whiskerLeft F.fnc (θ : LaxTwoCell G H).nat := rfl

@[simp] theorem bicategoryWhiskerRight_nat {M N P : LaxCModel.{u, v, w}} {F G : M ⟶ N}
    (θ : F ⟶ G) (H : N ⟶ P) :
    (Bicategory.whiskerRight θ H : LaxTwoCell (F ≫ H) (G ≫ H)).nat
      = Functor.whiskerRight (θ : LaxTwoCell F G).nat H.fnc := rfl

/-- **A lax 2-cell is determined by its natural transformation.** -/
theorem hom_ext {M N : LaxCModel.{u, v, w}} {F G : M ⟶ N} {θ ψ : F ⟶ G}
    (h : (θ : LaxTwoCell F G).nat = (ψ : LaxTwoCell F G).nat) : θ = ψ :=
  LaxTwoCell.ext_of_nat h

/-- **The 2-cells of the lax 2-category are exactly the natural transformations** of the functors
on contexts. -/
noncomputable def homEquivNatTrans {M N : LaxCModel.{u, v, w}} (F G : M ⟶ N) :
    (F ⟶ G) ≃ (F.fnc ⟶ G.fnc) :=
  LaxTwoCell.equivNatTrans F G

/-- **A lax 2-cell whose natural transformation is invertible is invertible.** -/
theorem isIso_of_isIso_nat {M N : LaxCModel.{u, v, w}} {F G : M ⟶ N} (θ : F ⟶ G)
    [IsIso (θ : LaxTwoCell F G).nat] : IsIso θ := by
  refine ⟨LaxTwoCell.ofNat G F (CategoryTheory.inv (θ : LaxTwoCell F G).nat), ?_, ?_⟩
  · refine hom_ext ?_
    change (θ : LaxTwoCell F G).nat ≫ CategoryTheory.inv (θ : LaxTwoCell F G).nat = 𝟙 F.fnc
    simp
  · refine hom_ext ?_
    change CategoryTheory.inv (θ : LaxTwoCell F G).nat ≫ (θ : LaxTwoCell F G).nat = 𝟙 G.fnc
    simp

end LaxCModel

end Cwa
