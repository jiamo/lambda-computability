/-
**When a full model is equivalent to the strictification of its own contexts.**

`Start/CwaStrictifyFull.lean` builds the comparison `Cwa.fullStrictify : Cwa.ofPullbacks C ⟶ T`
out of the strictification of the contexts of a full model `T`, and leaves open whether it is an
equivalence in the lax 2-category of models.  This module settles the shape of the answer: since
every natural transformation of the functors on contexts underlies a lax 2-cell
(`Cwa.LaxTwoCell.ofNat`) and a lax 2-cell is determined by it (`Cwa.LaxTwoCell.ext_of_nat`), an
isomorphism of 1-cells is nothing but an isomorphism of the functors on contexts.  So the *only*
thing missing for an equivalence is a morphism of models back — a classifying morphism
`M : T ⟶ Cwa.ofPullbacks C`, which sends a type over `Γ` to a local universe whose base and
generic family are independent of `Γ`.

Main results:

* `Cwa.laxIsoOfNatIso` — an isomorphism of the functors on contexts is an isomorphism of the
  1-cells, in the category of morphisms and lax 2-cells;
* `Cwa.fullStrictify_comp_iso_id`, `Cwa.comp_fullStrictify_iso_id` — with a classifying morphism
  that is the identity on contexts, both composites with `Cwa.fullStrictify` are isomorphic to the
  identity 1-cell: **a full coherent model admitting a classifying morphism is equivalent, in the
  lax 2-category, to the strictification of its category of contexts**.

`Start/CwaFamiliesNoStrictify.lean` shows the hypothesis is not vacuous as a hypothesis: the
standard model of families is full and democratic and admits no such morphism, so it is *not*
equivalent to the strictification of its contexts.
-/

import Start.CwaLaxRigid
import Start.CwaStrictifyFull

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D}

/-- **An isomorphism of the functors on contexts is an isomorphism of the 1-cells.**  A lax 2-cell
is exactly a natural transformation of those functors, so nothing else is needed. -/
noncomputable def laxIsoOfNatIso (coh : ExtCoherent S) {F G : Mor T S} (n : F.fnc ≅ G.fnc) :
    @Iso _ (laxMorCategory coh) F G :=
  letI := laxMorCategory (T := T) coh
  { hom := LaxTwoCell.ofNat F G n.hom
    inv := LaxTwoCell.ofNat G F n.inv
    hom_inv_id := LaxTwoCell.ext_of_nat (by
      change (LaxTwoCell.vcomp coh (LaxTwoCell.ofNat F G n.hom)
        (LaxTwoCell.ofNat G F n.inv)).nat = (LaxTwoCell.id coh F).nat
      simp)
    inv_hom_id := LaxTwoCell.ext_of_nat (by
      change (LaxTwoCell.vcomp coh (LaxTwoCell.ofNat G F n.inv)
        (LaxTwoCell.ofNat F G n.hom)).nat = (LaxTwoCell.id coh G).nat
      simp) }

section

variable [HasPullbacks C]

/-- **A classifying morphism makes the comparison an equivalence, one way round**: composing a
morphism to the strictification that is the identity on contexts with `Cwa.fullStrictify` gives a
1-cell isomorphic to the identity of the model. -/
noncomputable def fullStrictify_comp_iso_id (co : ExtCoherent T) (h : IsFull T)
    (M : Mor T (Cwa.ofPullbacks C)) (hM : M.fnc = 𝟭 C) :
    @Iso _ (laxMorCategory co) (M.comp (fullStrictify co h)) (Mor.id T) :=
  laxIsoOfNatIso co (eqToIso (by
    change M.fnc ⋙ 𝟭 C = 𝟭 C
    rw [Functor.comp_id, hM]))

/-- **And the other way round**: composing `Cwa.fullStrictify` with such a morphism gives a 1-cell
isomorphic to the identity of the strictification.  With the previous result: a full coherent model
admitting a classifying morphism is equivalent, in the lax 2-category of models, to the
strictification of its category of contexts. -/
noncomputable def comp_fullStrictify_iso_id (co : ExtCoherent T) (h : IsFull T)
    (M : Mor T (Cwa.ofPullbacks C)) (hM : M.fnc = 𝟭 C) :
    @Iso _ (laxMorCategory (extCoherent_ofPullbacks C))
      ((fullStrictify co h).comp M) (Mor.id (Cwa.ofPullbacks C)) :=
  laxIsoOfNatIso (extCoherent_ofPullbacks C) (eqToIso (by
    change 𝟭 C ⋙ M.fnc = 𝟭 C
    rw [Functor.id_comp, hM]))

end

end Cwa
