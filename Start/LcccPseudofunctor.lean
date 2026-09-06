/-
**Locally cartesian closed categories as models of the dependent product.**

`Start/CwaStrictPseudofunctor.lean` makes strictification a pseudofunctor from the 2-category of
categories with pullbacks to the lax 2-category of models of a dependent type theory.  The
comparison the theory of categories with attributes is after is the one with *locally cartesian
closed* categories: those are exactly the categories with pullbacks whose strictification models
the dependent product (`Cwa.nonempty_naturalPiStruct_ofPullbacks_iff`).

This module makes that comparison 2-dimensional.  Locally cartesian closed categories, the
pullback-preserving functors between them and the natural transformations form a 2-category
`Cwa.LcccCat` — the full sub-2-category of `Cwa.PbCat` they span — and strictification restricts
to a pseudofunctor out of it whose values carry a natural Π-structure.

Main definitions:

* `Cwa.LcccObj` — a locally cartesian closed category with pullbacks and binary products;
* `Cwa.LcccCat` — **the 2-category of locally cartesian closed categories**, obtained as a full
  sub-2-category of the 2-category of categories with pullbacks;
* `Cwa.lcccPseudofunctor` — **strictification, restricted to locally cartesian closed
  categories**: a pseudofunctor into the lax 2-category of models.

Main results:

* `Cwa.lcccNaturalPiStruct` — every value of the pseudofunctor is a model of the dependent
  product;
* `Cwa.nonempty_naturalPiStruct_toLaxCModel_iff` — conversely, the strictification of a category
  with pullbacks and binary products models the dependent product exactly when the category is
  locally cartesian closed, so the objects of the image are, up to that structure, exactly the
  locally cartesian closed categories;
* `Cwa.lcccPseudofunctor_map_injective`, `Cwa.lcccPseudofunctor_map₂_bijective` — the
  pseudofunctor is faithful on 1-cells and locally fully faithful;
* `Cwa.lcccHomEquivalence` — **it is a local equivalence**: its hom-categories are equivalent, so
  it is a biequivalence onto the full sub-2-category of models it spans.

The 2-category is inhabited: `Cwa.LcccObj.type` is the category of sets.
-/

import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Start.CwaStrictLocalEquiv
import Start.CwaLcccOfPi
import Start.CwaPiType

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits Bicategory

namespace Cwa

-- As for `Cwa.PbCat`, the universes are independent but the linter only sees them inside a
-- `max`; mathlib disables the check for `CategoryTheory.Cat` in the same way.
set_option linter.checkUnivs false in
/-- A **locally cartesian closed category**, as an object: a category with pullbacks and binary
products in which every substitution functor between slices has a right adjoint. -/
structure LcccObj where
  /-- The underlying category. -/
  Ctx : Type u
  /-- Its categorical structure. -/
  [inst : Category.{v} Ctx]
  /-- It has pullbacks. -/
  [hasPullbacks : HasPullbacks Ctx]
  /-- It has binary products. -/
  [hasBinaryProducts : HasBinaryProducts Ctx]
  /-- It is locally cartesian closed. -/
  [lccc : LcccPullbacks Ctx]

attribute [instance] LcccObj.inst LcccObj.hasPullbacks LcccObj.hasBinaryProducts LcccObj.lccc

/-- A locally cartesian closed category is in particular a category with pullbacks. -/
def LcccObj.toPbCat (X : LcccObj.{u, v}) : PbCat.{u, v} := ⟨X.Ctx⟩

@[simp] theorem LcccObj.toPbCat_Ctx (X : LcccObj.{u, v}) : X.toPbCat.Ctx = X.Ctx := rfl

/-- **The category of sets is an object of the 2-category below**: it is locally cartesian
closed, so the 2-category is not empty. -/
noncomputable def LcccObj.type : LcccObj.{u + 1, u} := ⟨Type u⟩

set_option linter.checkUnivs false in
/-- **The 2-category of locally cartesian closed categories**: the full sub-2-category of the
2-category of categories with pullbacks spanned by the locally cartesian closed ones, so that its
1-cells are the pullback-preserving functors and its 2-cells the natural transformations. -/
abbrev LcccCat : Type max (u + 1) (v + 1) :=
  InducedBicategory PbCat.{u, v} LcccObj.toPbCat

/-- **Strictification, restricted to the locally cartesian closed categories**: a pseudofunctor
from the 2-category of locally cartesian closed categories to the lax 2-category of models of a
dependent type theory. -/
noncomputable def lcccPseudofunctor :
    Pseudofunctor LcccCat.{u, v} LaxCModel.{u, v, max u v} :=
  Pseudofunctor.comp
    (InducedBicategory.forget (C := PbCat.{u, v})
      (F := LcccObj.toPbCat)).toStrictlyUnitaryPseudofunctor.toPseudofunctor
    strictificationPseudofunctor

@[simp] theorem lcccPseudofunctor_obj (X : LcccCat.{u, v}) :
    lcccPseudofunctor.obj X = PbCat.toLaxCModel (LcccObj.toPbCat X) := rfl

/-- The strictification of a locally cartesian closed category carries a natural Π-structure. -/
noncomputable def LcccObj.naturalPiStruct (X : LcccObj.{u, v}) :
    NaturalPiStruct (PbCat.toLaxCModel X.toPbCat).model.str :=
  Cwa.naturalPiStructOfLccc X.Ctx

/-- **Every model in the image of the pseudofunctor interprets the dependent product**: the
strictification of a locally cartesian closed category carries a natural Π-structure. -/
noncomputable def lcccNaturalPiStruct (X : LcccCat.{u, v}) :
    NaturalPiStruct (lcccPseudofunctor.obj X).model.str :=
  LcccObj.naturalPiStruct X

/-- **Conversely, only the locally cartesian closed categories are models of the dependent
product**: the strictification of a category with pullbacks and binary products carries a natural
Π-structure exactly when the category is locally cartesian closed. -/
theorem nonempty_naturalPiStruct_toLaxCModel_iff (X : PbCat.{u, v}) [HasBinaryProducts X.Ctx] :
    Nonempty (NaturalPiStruct (PbCat.toLaxCModel X).model.str)
      ↔ Nonempty (LcccPullbacks X.Ctx) :=
  Cwa.nonempty_naturalPiStruct_ofPullbacks_iff X.Ctx

/-- **The pseudofunctor is faithful on 1-cells**: two pullback-preserving functors of locally
cartesian closed categories inducing the same morphism of models are equal. -/
theorem lcccPseudofunctor_map_injective (X Y : LcccCat.{u, v}) :
    Function.Injective (fun f : X ⟶ Y => lcccPseudofunctor.map f) := by
  intro f g h
  exact InducedBicategory.hom_ext
    (strictificationPseudofunctor_map_injective _ _ h)

/-- **The pseudofunctor is locally fully faithful**: between two pullback-preserving functors of
locally cartesian closed categories, the natural transformations are exactly the lax 2-cells of
the induced morphisms of models. -/
theorem lcccPseudofunctor_map₂_bijective {X Y : LcccCat.{u, v}} (f g : X ⟶ Y) :
    Function.Bijective (fun η : f ⟶ g => lcccPseudofunctor.map₂ η) := by
  constructor
  · intro η θ h
    exact InducedBicategory.hom₂_ext
      ((strictificationPseudofunctor_map₂_bijective f.hom g.hom).1 h)
  · intro θ
    obtain ⟨τ, hτ⟩ := (strictificationPseudofunctor_map₂_bijective f.hom g.hom).2 θ
    exact ⟨⟨τ⟩, hτ⟩

/-- **The pseudofunctor between two fixed hom-categories.** -/
noncomputable abbrev lcccHomFunctor (X Y : LcccCat.{u, v}) :
    (X ⟶ Y) ⥤ (lcccPseudofunctor.obj X ⟶ lcccPseudofunctor.obj Y) :=
  lcccPseudofunctor.mapFunctor X Y

instance lcccHomFunctor_full (X Y : LcccCat.{u, v}) : (lcccHomFunctor X Y).Full where
  map_surjective {f g} θ := (lcccPseudofunctor_map₂_bijective f g).2 θ

instance lcccHomFunctor_faithful (X Y : LcccCat.{u, v}) : (lcccHomFunctor X Y).Faithful where
  map_injective {f g} {_ _} h := (lcccPseudofunctor_map₂_bijective f g).1 h

/-- **Every morphism of models between the strictifications of two locally cartesian closed
categories is isomorphic to one induced by a pullback-preserving functor.** -/
instance lcccHomFunctor_essSurj (X Y : LcccCat.{u, v}) : (lcccHomFunctor X Y).EssSurj where
  mem_essImage F := by
    obtain ⟨f, ⟨e⟩⟩ :=
      (strictHomFunctor_essSurj (LcccObj.toPbCat X) (LcccObj.toPbCat Y)).mem_essImage F
    exact ⟨InducedBicategory.mkHom f, ⟨e⟩⟩

/-- **The hom-categories are equivalent**: the pullback-preserving functors between two locally
cartesian closed categories, and their natural transformations, are equivalent to the morphisms of
the induced models of the dependent product and their lax 2-cells.  So the pseudofunctor is a
local equivalence: a biequivalence onto the full sub-2-category of models it spans. -/
noncomputable def lcccHomEquivalence (X Y : LcccCat.{u, v}) :
    (X ⟶ Y) ≌ (lcccPseudofunctor.obj X ⟶ lcccPseudofunctor.obj Y) :=
  haveI : (lcccHomFunctor X Y).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  (lcccHomFunctor X Y).asEquivalence

end Cwa
