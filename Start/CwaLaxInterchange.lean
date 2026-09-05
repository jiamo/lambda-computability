/-
**The interchange law for lax 2-cells.**

`Start/CwaLaxWhisker.lean` builds the two whiskerings of a lax 2-cell by a morphism of models and
proves each of them functorial, but records as its boundary that the *interchange* law relating
them cannot be proved — indeed cannot even be attacked — from the data of a lax 2-cell, since the
comparison of one 2-cell is not asked to be natural in the component of the other.

`Start/CwaLaxRigid.lean` dissolves that boundary: the comparison is not extra data, it is uniquely
determined by the natural transformation of the functors on contexts.  Consequently *any* equation
between lax 2-cells is an equation between natural transformations, and the interchange law is the
interchange law for natural transformations.

Main results:

* `Cwa.LaxTwoCell.whisker_exchange` — **the interchange law**, for two arbitrary lax 2-cells;
* `Cwa.LaxTwoCell.whisker_exchange_strict_left`, `Cwa.LaxTwoCell.whisker_exchange_strict_right` —
  its mixed cases, where one of the two 2-cells is a strict one included in the lax ones;
* `Cwa.LaxTwoCell.whiskerLeft_ofNat`, `Cwa.LaxTwoCell.whiskerRight_ofNat` — whiskering a lax
  2-cell is whiskering its natural transformation.
-/

import Start.CwaLaxRigid
import Start.CwaLaxWhisker

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w' u'' v'' w''

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D} {R : Cwa.{u'', v'', w''} E}

namespace LaxTwoCell

/-- **The interchange law for lax 2-cells**: whiskering a lax 2-cell of `S ⟶ R` on the left by the
source of a lax 2-cell of `T ⟶ S` and then whiskering the latter on the right by the target is the
same as doing the two in the other order.  Both sides are lax 2-cells with the same natural
transformation, and a lax 2-cell is determined by its natural transformation
(`Cwa.LaxTwoCell.ext_of_nat`). -/
theorem whisker_exchange (coh : ExtCoherent R) {F G : Mor T S} {K L : Mor S R}
    (θ : LaxTwoCell F G) (ψ : LaxTwoCell K L) :
    (whiskerLeft F ψ).vcomp coh (whiskerRight θ L)
      = (whiskerRight θ K).vcomp coh (whiskerLeft G ψ) := by
  refine ext_of_nat ?_
  simp only [vcomp_nat, whiskerLeft_nat, whiskerRight_nat]
  exact Functor.whiskerLeft_comp_whiskerRight θ.nat ψ.nat

/-- The interchange law when the 2-cell of `T ⟶ S` is a *strict* one, included in the lax ones. -/
theorem whisker_exchange_strict_left (coh : ExtCoherent R) {F G : Mor T S} {K L : Mor S R}
    (θ : TwoCell F G) (ψ : LaxTwoCell K L) :
    (whiskerLeft F ψ).vcomp coh (whiskerRight θ.toLax L)
      = (whiskerRight θ.toLax K).vcomp coh (whiskerLeft G ψ) :=
  whisker_exchange coh θ.toLax ψ

/-- The interchange law when the 2-cell of `S ⟶ R` is a *strict* one, included in the lax ones. -/
theorem whisker_exchange_strict_right (coh : ExtCoherent R) {F G : Mor T S} {K L : Mor S R}
    (θ : LaxTwoCell F G) (ψ : TwoCell K L) :
    (whiskerLeft F ψ.toLax).vcomp coh (whiskerRight θ L)
      = (whiskerRight θ K).vcomp coh (whiskerLeft G ψ.toLax) :=
  whisker_exchange coh θ ψ.toLax

/-- Whiskering on the left the lax 2-cell of a natural transformation. -/
theorem whiskerLeft_ofNat (F : Mor T S) {K L : Mor S R} (n : K.fnc ⟶ L.fnc) :
    whiskerLeft F (ofNat K L n) = ofNat (F.comp K) (F.comp L) (Functor.whiskerLeft F.fnc n) :=
  ext_of_nat rfl

/-- Whiskering on the right the lax 2-cell of a natural transformation. -/
theorem whiskerRight_ofNat {F G : Mor T S} (n : F.fnc ⟶ G.fnc) (K : Mor S R) :
    whiskerRight (ofNat F G n) K = ofNat (F.comp K) (G.comp K) (Functor.whiskerRight n K.fnc) :=
  ext_of_nat rfl

end LaxTwoCell

end Cwa
