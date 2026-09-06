/-
**Strictification is a local equivalence.**

`Start/CwaStrictPseudofunctor.lean` makes strictification a pseudofunctor from the 2-category of
categories with pullbacks to the lax 2-category of models, and proves it locally *fully faithful*:
the natural transformations between two pullback-preserving functors are exactly the lax 2-cells
between the induced morphisms of models.  What was left open is the third clause a biequivalence
needs, local *essential surjectivity*: whether every morphism of models between two strictified
categories is isomorphic to an induced one.

It is.  A morphism of models out of a strictified category is free to choose the local universe
presenting a type, so it need not be induced *on the nose* — that is `Cwa.not_full_strictification`
— but its functor on contexts always preserves pullbacks (`Cwa.Mor.map_isPullback`), and with the
lax 2-cells a 2-cell is nothing but a natural transformation of the functors on contexts
(`Cwa.LaxTwoCell.ofNat`), so the identity of that functor is an invertible 2-cell from the induced
morphism to the given one.  The failure of fullness is therefore invisible up to isomorphism.

Main results:

* `Cwa.strictHomFunctor` — strictification between two fixed hom-categories;
* `Cwa.strictHomFunctor_essSurj` — **every morphism of models between strictified categories is
  isomorphic to one induced by a pullback-preserving functor**;
* `Cwa.strictHomEquivalence` — **the hom-categories are equivalent**: strictification is a local
  equivalence, hence a biequivalence onto the full sub-2-category of models it spans.
-/

import Start.CwaStrictPseudofunctor
import Start.CwaStrictFull

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace Cwa

/-- **Strictification between two fixed hom-categories**: it takes a pullback-preserving functor to
the induced morphism of models and a natural transformation to the induced lax 2-cell. -/
noncomputable abbrev strictHomFunctor (X Y : PbCat.{u, v}) :
    (X ⟶ Y) ⥤ (PbCat.toLaxCModel X ⟶ PbCat.toLaxCModel Y) :=
  strictificationPseudofunctor.mapFunctor X Y

instance strictHomFunctor_full (X Y : PbCat.{u, v}) : (strictHomFunctor X Y).Full where
  map_surjective {f g} θ := (strictificationPseudofunctor_map₂_bijective f g).2 θ

instance strictHomFunctor_faithful (X Y : PbCat.{u, v}) : (strictHomFunctor X Y).Faithful where
  map_injective {f g} {_ _} h := (strictificationPseudofunctor_map₂_bijective f g).1 h


/-- **Every morphism of models between two strictified categories is isomorphic to an induced
one.**  Its functor on contexts preserves pullbacks, so it induces a morphism of models with the
same functor, and the identity natural transformation is an invertible lax 2-cell between the
two. -/
instance strictHomFunctor_essSurj (X Y : PbCat.{u, v}) : (strictHomFunctor X Y).EssSurj where
  mem_essImage F := by
    obtain ⟨f, hf⟩ := exists_pbCatHom_fnc (X := X) (Y := Y) F
    refine ⟨f, ⟨?_⟩⟩
    letI θ : (strictHomFunctor X Y).obj f ⟶ F :=
      LaxTwoCell.ofNat (morOfPreservesPullbacks f.fnc) F (eqToHom hf)
    haveI : IsIso (θ : LaxTwoCell (morOfPreservesPullbacks f.fnc) F).nat := by
      change IsIso (eqToHom hf)
      infer_instance
    haveI : IsIso θ := LaxCModel.isIso_of_isIso_nat θ
    exact asIso θ

/-- **The hom-categories are equivalent**: the pullback-preserving functors between two categories
with pullbacks, and their natural transformations, are equivalent to the morphisms of the
strictified models and their lax 2-cells.  Strictification is a local equivalence, so it is a
biequivalence onto the full sub-2-category of models it spans. -/
noncomputable def strictHomEquivalence (X Y : PbCat.{u, v}) :
    (X ⟶ Y) ≌ (PbCat.toLaxCModel X ⟶ PbCat.toLaxCModel Y) :=
  haveI : (strictHomFunctor X Y).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  (strictHomFunctor X Y).asEquivalence

end Cwa
