/-
**Strictification is rigid in the 2-dimensional direction.**

`Start/CwaStrictFunctor.lean` shows that presenting a category with pullbacks as a model of a
dependent type theory is functorial: `Cwa.strictification : PbCat ⥤ Cwa.Model`.  Categories with
pullbacks are however a *2*-category — the 2-cells are the natural transformations of
pullback-preserving functors — and models of a dependent type theory carry the 2-cells of
`Start/CwaTwoCell.lean`.  One would like the strictification to be a 2-functor, or at least a
pseudofunctor, between the two.  This module shows that it is not, and exactly why.

The obstruction is that a morphism of categories with attributes acts on types *strictly*, and a
type of the strictified model is a local universe — a whole span `total ⟶ base` of the ambient
category, not just a fibre.  A 2-cell must carry the local universe assigned by one morphism to
the local universe assigned by the other, and substitution along the component of the 2-cell
touches the classifying map only.  Applying this to the type presented by an identity morphism
forces the two functors to agree *on objects*, and then pins the component of the 2-cell down to
the transport along that equality.

So the hom-categories of `Cwa.Model` restricted to strictified morphisms are discrete
(`Cwa.subsingleton_twoCell_strict`), while the hom-categories of categories with pullbacks are
not: `Cwa.coyonedaConst` is a natural transformation between two pullback-preserving endofunctors
of `Type` for which `Cwa.isEmpty_twoCell_id_coyoneda` shows there is no 2-cell at all.  A
2-functorial strictification into models with these 2-cells therefore does not exist; a
pseudofunctor to the bicategory of models must weaken either the morphisms or the 2-cells.

Main results:

* `Cwa.twoCell_strict_obj_eq` — a 2-cell between strictified morphisms forces the two functors to
  agree on objects;
* `Cwa.twoCell_strict_nat_app` — its component is the transport along that equality;
* `Cwa.subsingleton_twoCell_strict` — hence there is at most one such 2-cell, and
  `Cwa.twoCell_strict_self_nat` — a 2-cell from a strictified morphism to itself is the identity;
* `Cwa.isEmpty_twoCell_id_coyoneda` — **the 2-dimensional structure is genuinely lost**: a natural
  transformation between pullback-preserving functors need not be induced by any 2-cell.
-/

import Start.CwaTwoCell
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Limits

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v u' v'

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {D : Type u'} [Category.{v'} D] [HasPullbacks D]

omit [HasPullbacks C] in
/-- An equality of local universes identifies the classifying maps, up to the transport along the
induced equality of bases. -/
theorem LuTy.cls_congr {Γ : C} {A B : LuTy Γ} (h : A = B) :
    A.cls ≫ eqToHom (congrArg LuTy.base h) = B.cls := by
  subst h
  simp

variable {F G : C ⥤ D} [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G]

/-- **A 2-cell between strictified morphisms forces the two functors to agree on objects.**  The
type presented by the identity of `X` has `X` for its base, and a 2-cell must carry its local
universe, unchanged, to the local universe of the other morphism. -/
theorem twoCell_strict_obj_eq
    (θ : TwoCell (morOfPreservesPullbacks F) (morOfPreservesPullbacks G)) (X : C) :
    G.obj X = F.obj X :=
  congrArg LuTy.base (θ.tySub_app (Γ := X) (LuTy.ofHom (𝟙 X)))

/-- **The component of a 2-cell between strictified morphisms is the transport along the equality
of objects it forces**: it is inverse to that transport, hence carries no information. -/
theorem twoCell_strict_nat_app
    (θ : TwoCell (morOfPreservesPullbacks F) (morOfPreservesPullbacks G)) (X : C) :
    θ.nat.app X ≫ eqToHom (twoCell_strict_obj_eq θ X) = 𝟙 (F.obj X) := by
  have h := LuTy.cls_congr (θ.tySub_app (Γ := X) (LuTy.ofHom (𝟙 X)))
  simpa only [morOfPreservesPullbacks, morOfPullbackPreserving, LuTy.ofHom, LuTy.sub, luMap,
    F.map_id, G.map_id, Category.comp_id] using h

/-- **There is at most one 2-cell between two strictified morphisms.** -/
instance subsingleton_twoCell_strict :
    Subsingleton (TwoCell (morOfPreservesPullbacks F) (morOfPreservesPullbacks G)) :=
  ⟨fun θ ψ => TwoCell.ext (NatTrans.ext (funext fun X => by
    have h₁ := twoCell_strict_nat_app θ X
    have h₂ := twoCell_strict_nat_app ψ X
    exact (cancel_mono (eqToHom (twoCell_strict_obj_eq θ X))).mp (h₁.trans h₂.symm)))⟩

/-- **A 2-cell from a strictified morphism to itself is the identity.** -/
theorem twoCell_strict_self_nat
    (θ : TwoCell (morOfPreservesPullbacks F) (morOfPreservesPullbacks F)) : θ.nat = 𝟙 F := by
  refine NatTrans.ext (funext fun X => ?_)
  have h := twoCell_strict_nat_app θ X
  exact (Category.comp_id (θ.nat.app X)).symm.trans h

/-! ### The 2-dimensional structure is genuinely lost -/

/-- The functor `X ↦ (Empty ⟶ X)`, representable, hence preserving all limits and in particular
pullbacks.  Every one of its values is a singleton. -/
abbrev emptyPow : Type ⥤ Type := coyoneda.obj (Opposite.op Empty)

/-- The unique natural transformation from the identity functor to `Cwa.emptyPow`.  Both functors
preserve pullbacks, so this is a 2-cell of categories with pullbacks. -/
def coyonedaConst : 𝟭 Type ⟶ emptyPow where
  app X := TypeCat.ofHom fun _ => (TypeCat.ofHom fun e => e.elim : Empty ⟶ X)
  naturality _ _ _ := by
    ext _
    apply TypeCat.homEquiv.injective
    funext e
    exact e.elim

/-- The two functors do not agree on objects: `Empty ⟶ Empty` has an element, the identity, and
`Empty` has none. -/
theorem emptyPow_obj_ne : emptyPow.obj Empty ≠ (𝟭 Type).obj Empty := by
  intro h
  exact (cast h (𝟙 Empty)).elim

/-- **The strictification is not 2-functorial**: `Cwa.coyonedaConst` is a natural transformation
between pullback-preserving endofunctors of `Type`, but there is no 2-cell whatsoever between the
morphisms of models they induce. -/
theorem isEmpty_twoCell_id_coyoneda :
    IsEmpty (TwoCell (morOfPreservesPullbacks (𝟭 Type)) (morOfPreservesPullbacks emptyPow)) :=
  ⟨fun θ => emptyPow_obj_ne (twoCell_strict_obj_eq θ Empty)⟩

end Cwa
