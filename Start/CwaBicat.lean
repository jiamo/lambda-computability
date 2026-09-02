/-
**The models of a dependent type theory form a 2-category.**

`Start/CwaCat.lean` makes the models of a dependent type theory into a 1-category and
`Start/CwaTwoCell.lean` supplies the 2-cells between two morphisms.  This module assembles the two
into a `CategoryTheory.Bicategory`: composition of morphisms is *strictly* associative and unital
(that was already proved in `Start/CwaCat.lean`), so the associators and unitors are the transports
along those equalities and the bicategory is `CategoryTheory.Bicategory.Strict`.

The objects are the **coherent models** `Cwa.CModel`: a category of contexts, a category with
attributes on it, and the coherence law `Cwa.ExtCoherent` for the action of a substitution on
extended contexts.  The law is needed already for the identity 2-cell and for vertical composition
(see `Start/CwaTwoCell.lean`); it holds in the strictified model of a category with pullbacks
(`Cwa.extCoherent_ofPullbacks`) and in the syntactic model of `λΠ`, so no example is lost.

Main definitions:

* `Cwa.CModel` — a coherent model of a dependent type theory;
* `Cwa.CModel.instCategoryStruct`, `Cwa.CModel.instHomCategory` — the 1-cells and the hom-categories
  of 2-cells;
* `Cwa.CModel.instBicategory` — **the 2-category of models, morphisms and 2-cells**;
* `Cwa.CModel.toModel` — the underlying object of the 1-category of `Start/CwaCat.lean`.

Main results:

* `Cwa.CModel.instStrict` — **the 2-category is strict**;
* `Cwa.CModel.hom_ext` — a 2-cell of the 2-category is determined by its natural transformation;
* `Cwa.CModel.isIso_of_isIso_nat` — a 2-cell whose natural transformation is invertible is an
  isomorphism of the hom-category, i.e. the invertible 2-cells are exactly the ones whose
  components are invertible.
-/

import Start.CwaTwoCell
import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Batteries.Tactic.Lint

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Cwa

-- The three universes (contexts, morphisms, types) are independent and are intended to be given
-- explicitly, exactly as for `CategoryTheory.Cat`; a universe linter sees them only inside a
-- `max` and reports them as inseparable.
-- As for `CategoryTheory.Cat`, the universes are independent but the linter only sees them
-- inside a `max`; mathlib disables the check for `Cat` in the same way.
set_option linter.checkUnivs false in
/-- A **coherent model of a dependent type theory**: a category of contexts, a category with
attributes on it, and the coherence law for the action of a substitution on extended contexts. -/
structure CModel where
  /-- The category of contexts. -/
  Ctx : Type u
  /-- Its categorical structure. -/
  [inst : Category.{v} Ctx]
  /-- The types, terms and context extensions. -/
  str : Cwa.{u, v, w} Ctx
  /-- The coherence law making the substitution of terms functorial. -/
  coh : ExtCoherent str

attribute [instance] CModel.inst

namespace CModel

/-- The underlying model of the 1-category of `Start/CwaCat.lean`. -/
def toModel (M : CModel.{u, v, w}) : Model.{u, v, w} where
  Ctx := M.Ctx
  str := M.str

/-- The 1-cells of the 2-category of models: the morphisms of categories with attributes. -/
instance instCategoryStruct : CategoryStruct.{max u v w} CModel.{u, v, w} where
  Hom M N := Mor M.str N.str
  id M := Mor.id M.str
  comp F G := F.comp G

/-- **The 1-cells between two models form a category**, the 2-cells being its morphisms. -/
instance instHomCategory (M N : CModel.{u, v, w}) : Category.{max u v} (M ⟶ N) :=
  morCategory N.coh

@[simp] theorem id_fnc (M : CModel.{u, v, w}) : (𝟙 M : M ⟶ M).fnc = 𝟭 M.Ctx := rfl

@[simp] theorem comp_fnc {M N P : CModel.{u, v, w}} (F : M ⟶ N) (G : N ⟶ P) :
    (F ≫ G).fnc = F.fnc ⋙ G.fnc := rfl

@[simp] theorem id_nat {M N : CModel.{u, v, w}} (F : M ⟶ N) :
    (𝟙 F : TwoCell F F).nat = 𝟙 F.fnc := rfl

@[simp] theorem comp_nat {M N : CModel.{u, v, w}} {F G H : M ⟶ N} (θ : F ⟶ G) (ψ : G ⟶ H) :
    (θ ≫ ψ : TwoCell F H).nat = (θ : TwoCell F G).nat ≫ (ψ : TwoCell G H).nat := rfl

@[simp] theorem eqToHom_nat {M N : CModel.{u, v, w}} {F G : M ⟶ N} (h : F = G) :
    (eqToHom h : TwoCell F G).nat = eqToHom (congrArg Mor.fnc h) :=
  TwoCell.nat_eqToHom N.coh h

@[simp] theorem id_nat_app {M N : CModel.{u, v, w}} (F : M ⟶ N) (X : M.Ctx) :
    (𝟙 F : TwoCell F F).nat.app X = 𝟙 (F.fnc.obj X) := rfl

@[simp] theorem comp_nat_app {M N : CModel.{u, v, w}} {F G H : M ⟶ N} (θ : F ⟶ G) (ψ : G ⟶ H)
    (X : M.Ctx) :
    (θ ≫ ψ : TwoCell F H).nat.app X
      = (θ : TwoCell F G).nat.app X ≫ (ψ : TwoCell G H).nat.app X := rfl

@[simp] theorem whiskerLeft_nat_app {M N P : CModel.{u, v, w}} (F : M ⟶ N) {G H : N ⟶ P}
    (θ : G ⟶ H) (X : M.Ctx) :
    (TwoCell.whiskerLeft F θ).nat.app X = (θ : TwoCell G H).nat.app (F.fnc.obj X) := rfl

@[simp] theorem whiskerRight_nat_app {M N P : CModel.{u, v, w}} {F G : M ⟶ N} (θ : F ⟶ G)
    (H : N ⟶ P) (X : M.Ctx) :
    (TwoCell.whiskerRight θ H).nat.app X = H.fnc.map ((θ : TwoCell F G).nat.app X) := rfl

@[simp] theorem eqToHom_nat_app {M N : CModel.{u, v, w}} {F G : M ⟶ N} (h : F = G) (X : M.Ctx) :
    (eqToHom h : TwoCell F G).nat.app X = eqToHom (by rw [h]) := by
  subst h
  rfl

section BicatAxioms

variable {M N P Q : CModel.{u, v, w}}

/-- The 2-cell transporting along an equality of morphisms of models.  It is the `eqToHom` of the
category of morphisms, spelled out so that the axioms of the 2-category can be stated without
appealing to instance search for the hom-categories. -/
abbrev morEqToHom {F G : M ⟶ N} (h : F = G) : TwoCell F G :=
  @eqToHom (Mor M.str N.str) (morCategory N.coh).toCategoryStruct F G h

@[simp] theorem morEqToHom_nat_app {F G : M ⟶ N} (h : F = G) (X : M.Ctx) :
    (morEqToHom h).nat.app X = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- Whiskering an identity 2-cell on the left is an identity. -/
theorem whiskerLeft_id' (F : M ⟶ N) (G : N ⟶ P) :
    TwoCell.whiskerLeft F (TwoCell.id P.coh G) = TwoCell.id P.coh (F.comp G) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering on the left is functorial in the 2-cell. -/
theorem whiskerLeft_comp' (F : M ⟶ N) {G H K : N ⟶ P} (θ : TwoCell G H) (ψ : TwoCell H K) :
    TwoCell.whiskerLeft F (θ.vcomp P.coh ψ)
      = (TwoCell.whiskerLeft F θ).vcomp P.coh (TwoCell.whiskerLeft F ψ) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering by the identity morphism, up to the left unitor. -/
theorem id_whiskerLeft' {F G : M ⟶ N} (θ : TwoCell F G) :
    TwoCell.whiskerLeft (Mor.id M.str) θ
      = (morEqToHom (Mor.id_comp F)).vcomp N.coh
          (θ.vcomp N.coh (morEqToHom (Mor.id_comp G).symm)) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering by a composite, up to the associator. -/
theorem comp_whiskerLeft' (F : M ⟶ N) (G : N ⟶ P) {H K : P ⟶ Q} (θ : TwoCell H K) :
    TwoCell.whiskerLeft (F.comp G) θ
      = (morEqToHom (Mor.assoc F G H)).vcomp Q.coh
          ((TwoCell.whiskerLeft F (TwoCell.whiskerLeft G θ)).vcomp Q.coh
            (morEqToHom (Mor.assoc F G K).symm)) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering an identity 2-cell on the right is an identity. -/
theorem id_whiskerRight' (F : M ⟶ N) (G : N ⟶ P) :
    TwoCell.whiskerRight (TwoCell.id N.coh F) G = TwoCell.id P.coh (F.comp G) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering on the right is functorial in the 2-cell. -/
theorem comp_whiskerRight' {F G H : M ⟶ N} (θ : TwoCell F G) (ψ : TwoCell G H) (K : N ⟶ P) :
    TwoCell.whiskerRight (θ.vcomp N.coh ψ) K
      = (TwoCell.whiskerRight θ K).vcomp P.coh (TwoCell.whiskerRight ψ K) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering by the identity morphism, up to the right unitor. -/
theorem whiskerRight_id' {F G : M ⟶ N} (θ : TwoCell F G) :
    TwoCell.whiskerRight θ (Mor.id N.str)
      = (morEqToHom (Mor.comp_id F)).vcomp N.coh
          (θ.vcomp N.coh (morEqToHom (Mor.comp_id G).symm)) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Whiskering by a composite on the right, up to the associator. -/
theorem whiskerRight_comp' {F G : M ⟶ N} (θ : TwoCell F G) (H : N ⟶ P) (K : P ⟶ Q) :
    TwoCell.whiskerRight θ (H.comp K)
      = (morEqToHom (Mor.assoc F H K).symm).vcomp Q.coh
          ((TwoCell.whiskerRight (TwoCell.whiskerRight θ H) K).vcomp Q.coh
            (morEqToHom (Mor.assoc G H K))) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- Left and right whiskering associate, up to the associator. -/
theorem whisker_assoc' (F : M ⟶ N) {G H : N ⟶ P} (θ : TwoCell G H) (K : P ⟶ Q) :
    TwoCell.whiskerRight (TwoCell.whiskerLeft F θ) K
      = (morEqToHom (Mor.assoc F G K)).vcomp Q.coh
          ((TwoCell.whiskerLeft F (TwoCell.whiskerRight θ K)).vcomp Q.coh
            (morEqToHom (Mor.assoc F H K).symm)) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- **The pentagon identity** for the transports along associativity. -/
theorem pentagon' (F : M ⟶ N) (G : N ⟶ P) (H : P ⟶ Q) {R : CModel.{u, v, w}} (K : Q ⟶ R) :
    (TwoCell.whiskerRight (morEqToHom (Mor.assoc F G H)) K).vcomp R.coh
        ((morEqToHom (Mor.assoc F (G.comp H) K)).vcomp R.coh
          (TwoCell.whiskerLeft F (morEqToHom (Mor.assoc G H K))))
      = (morEqToHom (Mor.assoc (F.comp G) H K)).vcomp R.coh
          (morEqToHom (Mor.assoc F G (H.comp K))) := by
  refine TwoCell.ext ?_
  ext X
  simp

/-- **The triangle identity** for the transports along the unit laws. -/
theorem triangle' (F : M ⟶ N) (G : N ⟶ P) :
    (morEqToHom (Mor.assoc F (Mor.id N.str) G)).vcomp P.coh
        (TwoCell.whiskerLeft F (morEqToHom (Mor.id_comp G)))
      = TwoCell.whiskerRight (morEqToHom (Mor.comp_id F)) G := by
  refine TwoCell.ext ?_
  ext X
  simp

end BicatAxioms

/-- **The models, their morphisms and the 2-cells between them form a 2-category.** -/
instance instBicategory : Bicategory.{max u v, max u v w} CModel.{u, v, w} where
  toCategoryStruct := instCategoryStruct
  homCategory := instHomCategory
  whiskerLeft F _ _ θ := TwoCell.whiskerLeft F θ
  whiskerRight θ H := TwoCell.whiskerRight θ H
  associator F G H := eqToIso (Mor.assoc F G H)
  leftUnitor F := eqToIso (Mor.id_comp F)
  rightUnitor F := eqToIso (Mor.comp_id F)
  whiskerLeft_id := by intros; exact whiskerLeft_id' _ _
  whiskerLeft_comp := by intros; exact whiskerLeft_comp' _ _ _
  id_whiskerLeft := by intros; exact id_whiskerLeft' _
  comp_whiskerLeft := by intros; exact comp_whiskerLeft' _ _ _
  id_whiskerRight := by intros; exact id_whiskerRight' _ _
  comp_whiskerRight := by intros; exact comp_whiskerRight' _ _ _
  whiskerRight_id := by intros; exact whiskerRight_id' _
  whiskerRight_comp := by intros; exact whiskerRight_comp' _ _ _
  whisker_assoc := by intros; exact whisker_assoc' _ _ _
  whisker_exchange := by intros; exact TwoCell.whisker_exchange _ _ _
  pentagon := by intros; exact pentagon' _ _ _ _
  triangle := by intros; exact triangle' _ _

/-- **The 2-category of models is strict**: its associators and unitors come from equalities. -/
instance instStrict : Bicategory.Strict CModel.{u, v, w} where
  id_comp := Mor.id_comp
  comp_id := Mor.comp_id
  assoc := Mor.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- **A 2-cell is determined by its natural transformation.** -/
theorem hom_ext {M N : CModel.{u, v, w}} {F G : M ⟶ N} {θ ψ : F ⟶ G}
    (h : (θ : TwoCell F G).nat = (ψ : TwoCell F G).nat) : θ = ψ :=
  TwoCell.ext h

/-- **A 2-cell whose natural transformation is invertible is invertible.** -/
theorem isIso_of_isIso_nat {M N : CModel.{u, v, w}} {F G : M ⟶ N} (θ : F ⟶ G)
    [IsIso (θ : TwoCell F G).nat] : IsIso θ :=
  TwoCell.isIso_of_isIso_nat N.coh θ

end CModel

end Cwa
