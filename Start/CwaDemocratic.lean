/-
**Full and democratic models.**

`Start/LcccBiequivalence.lean` compares the 2-category of locally cartesian closed categories with
the 2-category of the models they present.  Those models are described there by *how they are
built* — as strictifications — and not by a property they have.  This module begins the intrinsic
description, with the two standard properties of a category with attributes.

* `Cwa.IsFull T` — every morphism of contexts is a display map up to isomorphism over its
  codomain: the types over `Γ` present every object of the slice over `Γ`;
* `Cwa.IsDemocratic T` — every context is, up to isomorphism, an extension of a terminal one, so
  that a context *is* a closed type.

Main results:

* `Cwa.IsFull.isPullback` — in a full model, every cospan has a pullback square, namely the
  extension square of the type presenting one of its legs;
* `Cwa.hasPullbacks_of_isFull` — **the category of contexts of a full model has pullbacks**;
* `Cwa.isFull_ofPullbacks`, `Cwa.isDemocratic_ofPullbacks` — the strictification of a category
  with pullbacks is full, and democratic as soon as the category has a terminal object.  So the
  models compared with the locally cartesian closed categories in `Start/LcccBiequivalence.lean`
  do have both properties.
-/

import Start.CwaLocalUniverse

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C]

/-- A model is **full** when every morphism of contexts is a display map up to isomorphism over
its codomain: for every `f : X ⟶ Z` there is a type over `Z` whose display map is `f`, up to an
isomorphism of `X` with the extended context. -/
structure IsFull (T : Cwa.{u, v, w} C) where
  /-- The type presenting a morphism. -/
  ty : {X Z : C} → (X ⟶ Z) → T.Ty Z
  /-- The domain of the morphism is the extended context. -/
  iso : {X Z : C} → (f : X ⟶ Z) → X ≅ T.ext Z (ty f)
  /-- The presentation lies over the codomain. -/
  iso_disp : ∀ {X Z : C} (f : X ⟶ Z), (iso f).hom ≫ T.disp (ty f) = f

/-- A model is **democratic** when there is a terminal context and every context is, up to
isomorphism, an extension of it: a context is then the same thing as a closed type. -/
structure IsDemocratic (T : Cwa.{u, v, w} C) where
  /-- The empty context. -/
  empty : C
  /-- It is terminal. -/
  isTerminal : IsTerminal empty
  /-- The closed type presenting a context. -/
  ty : C → T.Ty empty
  /-- Every context is the extension of the empty one by that type. -/
  iso : (Γ : C) → Γ ≅ T.ext empty (ty Γ)

namespace IsFull

variable {T : Cwa.{u, v, w} C}

/-- **In a full model every cospan has a pullback square**: the extension square of the type
presenting one of the two legs, transported along the isomorphism presenting it. -/
theorem isPullback (h : IsFull T) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (T.extend g (h.ty f) ≫ (h.iso f).inv) (T.disp (T.tySub g (h.ty f))) f g := by
  refine (T.isPullback g (h.ty f)).of_iso (Iso.refl _) (h.iso f).symm (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa using (((h.iso f).inv_comp_eq).2 (h.iso_disp f).symm).symm
  · simp

/-- Hence every cospan has a pullback. -/
theorem hasPullback (h : IsFull T) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  (h.isPullback f g).hasPullback

end IsFull

/-- **The category of contexts of a full model has pullbacks.** -/
theorem hasPullbacks_of_isFull {T : Cwa.{u, v, w} C} (h : IsFull T) : HasPullbacks C :=
  haveI : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), HasPullback f g :=
    fun f g => h.hasPullback f g
  hasPullbacks_of_hasLimit_cospan C

/-! ### The strictification is full, and democratic -/

variable (C) in
/-- **The strictification of a category with pullbacks is full**: a morphism is presented by the
local universe it defines. -/
noncomputable def isFull_ofPullbacks [HasPullbacks C] : IsFull (Cwa.ofPullbacks C) where
  ty f := LuTy.ofHom f
  iso f := LuTy.isoExtOfHom f
  iso_disp f := LuTy.isoExtOfHom_disp f

variable (C) in
/-- **The strictification of a category with pullbacks and a terminal object is democratic**: a
context is presented by the closed type its map to the terminal context defines. -/
noncomputable def isDemocratic_ofPullbacks [HasPullbacks C] [HasTerminal C] :
    IsDemocratic (Cwa.ofPullbacks C) where
  empty := ⊤_ C
  isTerminal := terminalIsTerminal
  ty Γ := LuTy.ofHom (terminal.from Γ)
  iso Γ := LuTy.isoExtOfHom (terminal.from Γ)

end Cwa
