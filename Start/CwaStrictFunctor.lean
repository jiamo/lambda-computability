/-
**Strictification is a functor.**

`Start/CwaLocalUniverse.lean` turns a category with pullbacks into a model of dependent type
theory, `Cwa.ofPullbacks`, by presenting a type as a local universe; `Start/CwaMor.lean` turns a
pullback-preserving functor into a morphism of the resulting models,
`Cwa.morOfPullbackPreserving`.  Neither module checks that the two constructions fit together:
that the identity functor gives the identity morphism and a composite of functors the composite
morphism.  That is what is proved here, and it is the 1-categorical skeleton of the pseudofunctor
from locally cartesian closed categories to models of `λΠ`.

The comparison isomorphism `Cwa.luExtIso` of an extended context is the only non-formal part: it
is the canonical map between two pullbacks, so it is pinned down by the two legs of the pullback
square, which gives `Cwa.luExtIso_id` and `Cwa.luExtIso_comp`.  Everything else about the induced
morphism — the functor on contexts, the action on types — is already strictly functorial, because
a local universe is transported componentwise.

Main definitions:

* `Cwa.PbCat` — a category with pullbacks, bundled, with pullback-preserving functors as its
  morphisms (`Cwa.PbCat.instCategory`);
* `Cwa.strictification` — **the strictification functor** from categories with pullbacks to models
  of a dependent type theory.

Main results:

* `Cwa.luExtIso_id`, `Cwa.luExtIso_comp` — the comparison isomorphisms of the identity functor and
  of a composite;
* `Cwa.morOfPreservesPullbacks_id`, `Cwa.morOfPreservesPullbacks_comp` — **the induced morphism of
  models is functorial in the functor**.
-/

import Start.CwaCat

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v u' v' u'' v''

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] [HasPullbacks C] [HasPullbacks D] [HasPullbacks E]

/-! ### The comparison isomorphism of the identity and of a composite -/

/-- The identity functor compares an extended context with itself by the identity. -/
theorem luExtIso_id {Γ : C} (A : LuTy Γ) :
    (luExtIso (𝟭 C) A).hom = 𝟙 (LuTy.ext Γ A) := by
  refine (LuTy.isPullback_gen A).hom_ext ?_ ?_
  · exact (luExtIso_hom_gen (𝟭 C) A).trans (Category.id_comp (LuTy.gen A)).symm
  · exact (luExtIso_hom_disp (𝟭 C) A).trans (Category.id_comp (LuTy.disp A)).symm

/-- The comparison of a composite is the composite of the comparisons. -/
theorem luExtIso_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape WalkingCospan G] {Γ : C} (A : LuTy Γ) :
    (luExtIso (F ⋙ G) A).hom = G.map (luExtIso F A).hom ≫ (luExtIso G (luMap F A)).hom := by
  refine (LuTy.isPullback_gen (luMap G (luMap F A))).hom_ext ?_ ?_
  · rw [Category.assoc, luExtIso_hom_gen G (luMap F A), ← G.map_comp, luExtIso_hom_gen F A]
    exact luExtIso_hom_gen (F ⋙ G) A
  · rw [Category.assoc, luExtIso_hom_disp G (luMap F A), ← G.map_comp, luExtIso_hom_disp F A]
    exact luExtIso_hom_disp (F ⋙ G) A

/-! ### Functoriality of the induced morphism of models -/

/-- **The identity functor induces the identity morphism of models.** -/
theorem morOfPreservesPullbacks_id :
    morOfPreservesPullbacks (𝟭 C) = Mor.id (Cwa.ofPullbacks C) := by
  refine Mor.ext rfl (fun _ => HEq.rfl) (fun A => heq_of_eq (Iso.ext ?_))
  exact luExtIso_id A

/-- **A composite of functors induces the composite morphism of models.** -/
theorem morOfPreservesPullbacks_comp (F : C ⥤ D) (G : D ⥤ E)
    [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G] :
    morOfPreservesPullbacks (F ⋙ G)
      = (morOfPreservesPullbacks F).comp (morOfPreservesPullbacks G) := by
  refine Mor.ext rfl (fun _ => HEq.rfl) (fun A => heq_of_eq (Iso.ext ?_))
  exact luExtIso_comp F G A

/-! ### The strictification functor -/

-- As for `CategoryTheory.Cat`, the universes are independent but the linter only sees them
-- inside a `max`; mathlib disables the check for `Cat` in the same way.
set_option linter.checkUnivs false in
/-- A **category with pullbacks**, bundled. -/
structure PbCat where
  /-- The underlying category. -/
  Ctx : Type u
  /-- Its categorical structure. -/
  [inst : Category.{v} Ctx]
  /-- It has pullbacks. -/
  [hasPullbacks : HasPullbacks Ctx]

attribute [instance] PbCat.inst PbCat.hasPullbacks

/-- A morphism of categories with pullbacks: a functor preserving pullbacks. -/
structure PbCat.Hom (X Y : PbCat.{u, v}) where
  /-- The underlying functor. -/
  fnc : X.Ctx ⥤ Y.Ctx
  /-- It preserves pullbacks. -/
  preserves : PreservesLimitsOfShape WalkingCospan fnc

attribute [instance] PbCat.Hom.preserves

@[ext] theorem PbCat.Hom.ext {X Y : PbCat.{u, v}} {f g : X.Hom Y} (h : f.fnc = g.fnc) : f = g := by
  cases f; cases g; cases h; rfl

/-- **Categories with pullbacks and pullback-preserving functors form a category.** -/
instance PbCat.instCategory : Category.{max u v} PbCat.{u, v} where
  Hom X Y := X.Hom Y
  id X := ⟨𝟭 X.Ctx, inferInstance⟩
  comp f g := ⟨f.fnc ⋙ g.fnc, inferInstance⟩
  id_comp _ := PbCat.Hom.ext rfl
  comp_id _ := PbCat.Hom.ext rfl
  assoc _ _ _ := PbCat.Hom.ext rfl

@[simp] theorem PbCat.id_fnc (X : PbCat.{u, v}) : PbCat.Hom.fnc (𝟙 X) = 𝟭 X.Ctx := rfl

@[simp] theorem PbCat.comp_fnc {X Y Z : PbCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fnc = f.fnc ⋙ g.fnc := rfl

/-- **Strictification as a functor**: a category with pullbacks is a model of a dependent type
theory, and a pullback-preserving functor a morphism of models, functorially. -/
noncomputable def strictification : PbCat.{u, v} ⥤ Cwa.Model.{u, v, max u v} where
  obj X := ⟨X.Ctx, Cwa.ofPullbacks X.Ctx⟩
  map f := morOfPreservesPullbacks f.fnc
  map_id _ := morOfPreservesPullbacks_id
  map_comp f g := morOfPreservesPullbacks_comp f.fnc g.fnc

end Cwa
