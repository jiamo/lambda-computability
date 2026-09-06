/-
**The biequivalence between locally cartesian closed categories and their models.**

`Start/LcccPseudofunctor.lean` builds strictification as a pseudofunctor
`Cwa.lcccPseudofunctor : Pseudofunctor LcccCat LaxCModel` out of the 2-category of locally
cartesian closed categories, and proves it locally fully faithful and locally essentially
surjective.  What was still missing for the comparison the theory of categories with attributes is
after is the *third* piece: a pseudofunctor back from the models to the categories, and the
statement that the two are inverse to each other.

This module supplies it.  The point is `Cwa.Mor.preservesLimitsOfShape_fnc`: the functor on
contexts underlying a morphism between two strictified models preserves pullbacks, so it *is* a
morphism of categories with pullbacks.  Reading off that functor is therefore a pseudofunctor
back, and it is strict — it takes identities to identities and composites to composites on the
nose, and a lax 2-cell to its natural transformation.

Main definitions:

* `Cwa.LcccModelCat` — the 2-category of the models of the dependent product presented by locally
  cartesian closed categories: the full sub-2-category of `Cwa.LaxCModel` spanned by their
  strictifications;
* `Cwa.lcccStrictification` — strictification, corestricted to it;
* `Cwa.lcccCtx` — **the pseudofunctor back**: a model in the image goes to its category of
  contexts, a morphism of models to its functor on contexts, a lax 2-cell to its natural
  transformation;
* `Cwa.IsBiequivalence` — a pseudofunctor is a **biequivalence** when it is a local equivalence
  and every object of the target is equivalent to an object in its image.

Main results:

* `Cwa.lcccCtx_map_lcccStrictification_map`, `Cwa.lcccStrictificationMapCtxMapIso` — the two round
  trips: one is the identity on the nose, the other is the identity up to a canonical invertible
  2-cell (it is *not* the identity on the nose, by `Cwa.not_full_strictification`);
* `Cwa.lcccCtx_isBiequivalence`, `Cwa.lcccStrictification_isBiequivalence` — **both
  pseudofunctors are biequivalences**;
* `Cwa.lcccModelCat_biequivalent` — the 2-category of locally cartesian closed categories and the
  2-category of the models of the dependent product they present are biequivalent.
-/

import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Start.LcccPseudofunctor

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits Bicategory

namespace Cwa

/-! ### Biequivalences -/

/-- A pseudofunctor is a **biequivalence** when it is a local equivalence — an equivalence of
categories between every pair of hom-categories — and every object of the target is equivalent,
in the bicategorical sense, to an object in its image. -/
structure IsBiequivalence {B : Type*} [Bicategory B] {C : Type*} [Bicategory C]
    (F : Pseudofunctor B C) : Prop where
  /-- The pseudofunctor is a local equivalence. -/
  isEquivalence_mapFunctor : ∀ X Y : B, (F.mapFunctor X Y).IsEquivalence
  /-- Every object of the target is equivalent to an object in the image. -/
  exists_equivalence : ∀ Z : C, ∃ X : B, Nonempty (Bicategory.Equivalence (F.obj X) Z)

/-! ### The 2-category of the models presented by locally cartesian closed categories -/

set_option linter.checkUnivs false in
/-- **The models of the dependent product presented by locally cartesian closed categories**: the
full sub-2-category of the lax 2-category of models spanned by the strictifications of locally
cartesian closed categories, so that its 1-cells are all morphisms of models and its 2-cells all
lax 2-cells. -/
abbrev LcccModelCat : Type max (u + 1) (v + 1) :=
  InducedBicategory LaxCModel.{u, v, max u v}
    (fun X : LcccObj.{u, v} => PbCat.toLaxCModel X.toPbCat)

/-! ### Strictification, corestricted to the models it presents -/

/-- **Strictification, corestricted to the models it presents**: a pseudofunctor from the
2-category of locally cartesian closed categories to the full sub-2-category of models they span.
All its data is that of `Cwa.lcccPseudofunctor`, read in the induced bicategory. -/
noncomputable def lcccStrictification :
    Pseudofunctor LcccCat.{u, v} LcccModelCat.{u, v} where
  obj X := X
  map f := InducedBicategory.mkHom (lcccPseudofunctor.map f)
  map₂ η := InducedBicategory.mkHom₂ (lcccPseudofunctor.map₂ η)
  mapId X := InducedBicategory.isoMk (lcccPseudofunctor.mapId X)
  mapComp f g := InducedBicategory.isoMk (lcccPseudofunctor.mapComp f g)
  map₂_id := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_id _)
  map₂_comp := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_comp _ _)
  map₂_whisker_left := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_whisker_left _ _)
  map₂_whisker_right := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_whisker_right _ _)
  map₂_associator := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_associator _ _ _)
  map₂_left_unitor := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_left_unitor _)
  map₂_right_unitor := by
    intros
    exact InducedBicategory.hom₂_ext (lcccPseudofunctor.map₂_right_unitor _)

@[simp] theorem lcccStrictification_obj (X : LcccCat.{u, v}) :
    lcccStrictification.obj X = X := rfl

@[simp] theorem lcccStrictification_map {X Y : LcccCat.{u, v}} (f : X ⟶ Y) :
    (lcccStrictification.map f).hom = strictMap f.hom := rfl

@[simp] theorem lcccStrictification_map₂ {X Y : LcccCat.{u, v}} {f g : X ⟶ Y} (η : f ⟶ g) :
    (lcccStrictification.map₂ η).hom = strictMap₂ η.hom := rfl

/-! ### The pseudofunctor back -/

/-- **The functor on contexts of a morphism of strictified models**, as a morphism of categories
with pullbacks: it preserves pullbacks by `Cwa.Mor.preservesLimitsOfShape_fnc`. -/
noncomputable def ctxFnc {X Y : LcccObj.{u, v}}
    (F : PbCat.toLaxCModel X.toPbCat ⟶ PbCat.toLaxCModel Y.toPbCat) :
    X.toPbCat ⟶ Y.toPbCat :=
  PbCat.Hom.mk F.fnc (Mor.preservesLimitsOfShape_fnc (G := F))

@[simp] theorem ctxFnc_fnc {X Y : LcccObj.{u, v}}
    (F : PbCat.toLaxCModel X.toPbCat ⟶ PbCat.toLaxCModel Y.toPbCat) :
    (ctxFnc F).fnc = F.fnc := rfl

/-- The locally cartesian closed category underlying a model in the image. -/
abbrev ctxObj (X : LcccModelCat.{u, v}) : LcccCat.{u, v} := X

/-- **The functor on contexts of a morphism of models in the image**, as a 1-cell of the
2-category of locally cartesian closed categories. -/
noncomputable def ctxMap {X Y : LcccModelCat.{u, v}} (F : X ⟶ Y) : ctxObj X ⟶ ctxObj Y :=
  InducedBicategory.mkHom (ctxFnc F.hom)

@[simp] theorem ctxMap_hom_fnc {X Y : LcccModelCat.{u, v}} (F : X ⟶ Y) :
    (ctxMap F).hom.fnc = F.hom.fnc := rfl

/-- **Identities go to identities**, on the nose. -/
theorem ctxMap_id (X : LcccModelCat.{u, v}) : ctxMap (𝟙 X) = 𝟙 (ctxObj X) := rfl

/-- **Composites go to composites**, on the nose. -/
theorem ctxMap_comp {X Y Z : LcccModelCat.{u, v}} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ctxMap (F ≫ G) = ctxMap F ≫ ctxMap G := rfl

/-- **The natural transformation of a lax 2-cell**, as a 2-cell of the 2-category of locally
cartesian closed categories. -/
noncomputable def ctxMap₂ {X Y : LcccModelCat.{u, v}} {F G : X ⟶ Y} (η : F ⟶ G) :
    ctxMap F ⟶ ctxMap G :=
  InducedBicategory.mkHom₂ (η.hom : LaxTwoCell _ _).nat

@[simp] theorem ctxMap₂_hom {X Y : LcccModelCat.{u, v}} {F G : X ⟶ Y} (η : F ⟶ G) :
    (ctxMap₂ η).hom = (η.hom : LaxTwoCell _ _).nat := rfl

/-- **The pseudofunctor back**: a model presented by a locally cartesian closed category goes to
that category, a morphism of models to its functor on contexts, and a lax 2-cell to its natural
transformation.  It is strict — identities and composites are preserved on the nose. -/
noncomputable def lcccCtxStrict :
    StrictPseudofunctor LcccModelCat.{u, v} LcccCat.{u, v} :=
  StrictPseudofunctor.mk''
    { obj := fun X => ctxObj X
      map := fun F => ctxMap F
      map₂ := fun η => ctxMap₂ η
      map₂_id := by
        intros
        exact InducedBicategory.hom₂_ext (by ext X; rfl)
      map₂_comp := by
        intros
        exact InducedBicategory.hom₂_ext (by ext X; rfl)
      map_id := by
        intros
        rfl
      map_comp := by
        intros
        rfl
      map₂_whisker_left := by
        intro a b c f g g' η
        change ctxMap₂ (f ◁ η)
          = 𝟙 (ctxMap f ≫ ctxMap g) ≫ ctxMap f ◁ ctxMap₂ η ≫ 𝟙 (ctxMap f ≫ ctxMap g')
        exact ((Category.id_comp _).trans (Category.comp_id _)).symm
      map₂_whisker_right := by
        intro a b c f f' η g
        change ctxMap₂ (η ▷ g)
          = 𝟙 (ctxMap f ≫ ctxMap g) ≫ ctxMap₂ η ▷ ctxMap g ≫ 𝟙 (ctxMap f' ≫ ctxMap g)
        exact ((Category.id_comp _).trans (Category.comp_id _)).symm }

/-- **The pseudofunctor back**, from the models presented by locally cartesian closed categories
to the categories themselves. -/
noncomputable abbrev lcccCtx : Pseudofunctor LcccModelCat.{u, v} LcccCat.{u, v} :=
  lcccCtxStrict.toPseudofunctor

@[simp] theorem lcccCtx_obj (X : LcccModelCat.{u, v}) : lcccCtx.obj X = ctxObj X := rfl

@[simp] theorem lcccCtx_map {X Y : LcccModelCat.{u, v}} (F : X ⟶ Y) :
    lcccCtx.map F = ctxMap F := rfl

@[simp] theorem lcccCtx_map₂ {X Y : LcccModelCat.{u, v}} {F G : X ⟶ Y} (η : F ⟶ G) :
    lcccCtx.map₂ η = ctxMap₂ η := rfl

/-! ### The two round trips -/

/-- **One round trip is the identity on the nose**: reading off the functor on contexts of the
morphism of models induced by a pullback-preserving functor gives that functor back. -/
theorem lcccCtx_map_lcccStrictification_map {X Y : LcccCat.{u, v}} (f : X ⟶ Y) :
    lcccCtx.map (lcccStrictification.map f) = f :=
  InducedBicategory.hom_ext (PbCat.Hom.ext rfl)

/-- On 2-cells the same round trip is the identity too. -/
theorem lcccCtx_map₂_lcccStrictification_map₂ {X Y : LcccCat.{u, v}} {f g : X ⟶ Y} (η : f ⟶ g) :
    (lcccCtx.map₂ (lcccStrictification.map₂ η)).hom = η.hom := rfl

/-- **The other round trip is the identity up to a canonical invertible 2-cell**: a morphism of
models between two strictified categories has the same functor on contexts as the morphism induced
by that functor, and the identity natural transformation is an invertible lax 2-cell between the
two.  It is not the identity on the nose: `Cwa.not_full_strictification`. -/
noncomputable def lcccStrictificationMapCtxMapIso {X Y : LcccModelCat.{u, v}} (F : X ⟶ Y) :
    lcccStrictification.map (lcccCtx.map F) ≅ F := by
  refine InducedBicategory.isoMk ?_
  letI θ : (lcccStrictification.map (lcccCtx.map F)).hom ⟶ F.hom :=
    LaxTwoCell.ofNat _ _ (𝟙 F.hom.fnc)
  haveI : IsIso (θ : LaxTwoCell _ _).nat := by
    change IsIso (𝟙 F.hom.fnc)
    infer_instance
  haveI : IsIso θ := LaxCModel.isIso_of_isIso_nat θ
  exact asIso θ

/-! ### Both pseudofunctors are biequivalences -/

instance lcccCtx_mapFunctor_full (X Y : LcccModelCat.{u, v}) :
    (lcccCtx.mapFunctor X Y).Full where
  map_surjective {F G} τ :=
    ⟨InducedBicategory.mkHom₂ (LaxTwoCell.ofNat F.hom G.hom τ.hom),
      InducedBicategory.hom₂_ext rfl⟩

instance lcccCtx_mapFunctor_faithful (X Y : LcccModelCat.{u, v}) :
    (lcccCtx.mapFunctor X Y).Faithful where
  map_injective h :=
    InducedBicategory.hom₂_ext
      (LaxCModel.hom_ext (congrArg InducedBicategory.Hom₂.hom h))

instance lcccCtx_mapFunctor_essSurj (X Y : LcccModelCat.{u, v}) :
    (lcccCtx.mapFunctor X Y).EssSurj where
  mem_essImage f :=
    ⟨lcccStrictification.map f, ⟨eqToIso (lcccCtx_map_lcccStrictification_map f)⟩⟩

/-- **The pseudofunctor back is a local equivalence.** -/
noncomputable instance lcccCtx_mapFunctor_isEquivalence (X Y : LcccModelCat.{u, v}) :
    (lcccCtx.mapFunctor X Y).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

instance lcccStrictification_mapFunctor_faithful (X Y : LcccCat.{u, v}) :
    (lcccStrictification.mapFunctor X Y).Faithful where
  map_injective {f g} {_ _} h := by
    have h' := congrArg InducedBicategory.Hom₂.hom h
    exact InducedBicategory.hom₂_ext
      ((strictificationPseudofunctor_map₂_bijective f.hom g.hom).1 h')

instance lcccStrictification_mapFunctor_full (X Y : LcccCat.{u, v}) :
    (lcccStrictification.mapFunctor X Y).Full where
  map_surjective {f g} θ := by
    obtain ⟨τ, hτ⟩ := (strictificationPseudofunctor_map₂_bijective f.hom g.hom).2 θ.hom
    exact ⟨InducedBicategory.mkHom₂ τ, InducedBicategory.hom₂_ext hτ⟩

instance lcccStrictification_mapFunctor_essSurj (X Y : LcccCat.{u, v}) :
    (lcccStrictification.mapFunctor X Y).EssSurj where
  mem_essImage F := ⟨lcccCtx.map F, ⟨lcccStrictificationMapCtxMapIso F⟩⟩

/-- **Strictification, corestricted to the models it presents, is a local equivalence.** -/
noncomputable instance lcccStrictification_mapFunctor_isEquivalence (X Y : LcccCat.{u, v}) :
    (lcccStrictification.mapFunctor X Y).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **The pseudofunctor back is a biequivalence.** -/
theorem lcccCtx_isBiequivalence : IsBiequivalence lcccCtx.{u, v} where
  isEquivalence_mapFunctor X Y := lcccCtx_mapFunctor_isEquivalence X Y
  exists_equivalence Z := ⟨Z, ⟨Bicategory.Equivalence.id Z⟩⟩

/-- **Strictification, corestricted to the models it presents, is a biequivalence.** -/
theorem lcccStrictification_isBiequivalence : IsBiequivalence lcccStrictification.{u, v} where
  isEquivalence_mapFunctor X Y := lcccStrictification_mapFunctor_isEquivalence X Y
  exists_equivalence Z := ⟨Z, ⟨Bicategory.Equivalence.id Z⟩⟩

/-- **The comparison is a biequivalence in both directions**: the 2-category of locally cartesian
closed categories and the 2-category of the models of the dependent product they present are
biequivalent, by strictification and by taking contexts, with the two round trips of
`Cwa.lcccCtx_map_lcccStrictification_map` and `Cwa.lcccStrictificationMapCtxMapIso`. -/
theorem lcccModelCat_biequivalent :
    IsBiequivalence lcccStrictification.{u, v} ∧ IsBiequivalence lcccCtx.{u, v} :=
  ⟨lcccStrictification_isBiequivalence, lcccCtx_isBiequivalence⟩

end Cwa
