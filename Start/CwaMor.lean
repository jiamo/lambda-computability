/-
**Morphisms of categories with attributes.**

`Start/Cwa.lean` defines the models of a dependent type theory, one at a time; nothing there
relates two of them.  A comparison between models — an interpretation of one in another — is a
*morphism of categories with attributes*: a functor between the categories of contexts, an action
on types that commutes strictly with substitution, and an identification of the extended contexts
compatible with the display maps and with the action of substitution on them.

This module defines that notion and develops what it gives for free: a morphism acts on terms
(`Cwa.Mor.tmMap`), and that action commutes with substitution (`Cwa.Mor.tmMap_tmSub`), which is the
statement that the comparison is a map of models and not merely of the underlying data.  Morphisms
compose and there is an identity morphism, so the models of a dependent type theory form a
category.

The interesting example is the strictification of `Start/CwaLocalUniverse.lean`: a type there is
presented by a morphism of the ambient category, and a functor preserving pullbacks transports such
a presentation.  Hence `Cwa.morOfPullbackPreserving`: **the strictified model is functorial in
pullback-preserving functors**.  Note that strictness is not an issue here — substitution of local
universes acts on the classifying map alone, and a functor commutes with composition on the nose.

Main definitions:

* `Cwa.Mor` — a morphism of categories with attributes;
* `Cwa.Mor.tmMap` — its action on terms;
* `Cwa.Mor.id`, `Cwa.Mor.comp` — the identity and the composite;
* `Cwa.morOfPullbackPreserving`, `Cwa.morOfPreservesPullbacks` — the morphism of strictified
  models induced by a pullback-preserving functor.

Main results:

* `Cwa.Mor.tmMap_tmSub` — **the action on terms commutes with substitution**;
* `Cwa.Mor.tmMap_id`, `Cwa.Mor.tmMap_comp` — the action on terms is functorial.
-/

import Start.CwaLocalUniverse

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w' u'' v'' w''

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- The underlying morphism of a term transported along an equality of types. -/
theorem tmCast_val {T : Cwa.{u, v, w} C} {Γ : C} {A A' : T.Ty Γ} (h : A = A')
    (a : T.Tm Γ A) : (tmCast h a).1 = a.1 ≫ eqToHom (congrArg (T.ext Γ) h) := by
  cases h
  simp

/-- A **morphism of categories with attributes**: a functor on contexts, an action on types
commuting strictly with substitution, and an identification of the extended contexts which lies
over the base context and is compatible with substitution. -/
structure Mor (T : Cwa.{u, v, w} C) (S : Cwa.{u', v', w'} D) where
  /-- The functor on contexts. -/
  fnc : C ⥤ D
  /-- The action on types. -/
  tyMap : {Γ : C} → T.Ty Γ → S.Ty (fnc.obj Γ)
  /-- Types are carried to types strictly compatibly with substitution. -/
  tyMap_sub : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ),
      tyMap (T.tySub σ A) = S.tySub (fnc.map σ) (tyMap A)
  /-- The comparison identifying the image of an extended context. -/
  extIso : {Γ : C} → (A : T.Ty Γ) → fnc.obj (T.ext Γ A) ≅ S.ext (fnc.obj Γ) (tyMap A)
  /-- The comparison lies over the base context. -/
  extIso_disp : ∀ {Γ : C} (A : T.Ty Γ),
      (extIso A).hom ≫ S.disp (tyMap A) = fnc.map (T.disp A)
  /-- The comparison is compatible with the action of a substitution on extended contexts. -/
  extIso_extend : ∀ {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ),
      fnc.map (T.extend σ A) ≫ (extIso A).hom
        = (extIso (T.tySub σ A)).hom ≫ eqToHom (congrArg (S.ext (fnc.obj Δ)) (tyMap_sub σ A))
            ≫ S.extend (fnc.map σ) (tyMap A)

namespace Mor

variable {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D}

/-- The action of a morphism on terms: a section of a display map is carried to a section of the
image display map. -/
def tmMap (F : Mor T S) {Γ : C} {A : T.Ty Γ} (a : T.Tm Γ A) :
    S.Tm (F.fnc.obj Γ) (F.tyMap A) := by
  refine ⟨F.fnc.map a.1 ≫ (F.extIso A).hom, ?_⟩
  rw [Category.assoc, F.extIso_disp, ← F.fnc.map_comp, a.2, F.fnc.map_id]

@[simp] theorem tmMap_val (F : Mor T S) {Γ : C} {A : T.Ty Γ} (a : T.Tm Γ A) :
    (F.tmMap a).1 = F.fnc.map a.1 ≫ (F.extIso A).hom := rfl

/-- **The action on terms commutes with substitution.**  Both sides are sections of the display
map of the substituted type, hence maps into a pullback, so it is enough to compare them with the
two legs of that pullback square. -/
theorem tmMap_tmSub (F : Mor T S) {Γ Δ : C} (σ : Δ ⟶ Γ) {A : T.Ty Γ} (a : T.Tm Γ A) :
    tmCast (F.tyMap_sub σ A) (F.tmMap (T.tmSub σ a)) = S.tmSub (F.fnc.map σ) (F.tmMap a) := by
  refine Tm.ext' ?_
  refine (S.isPullback (F.fnc.map σ) (F.tyMap A)).hom_ext ?_ ?_
  · rw [tmCast_val, tmMap_val, Category.assoc, Category.assoc, ← F.extIso_extend σ A,
      ← Category.assoc, ← F.fnc.map_comp]
    have hlift : (T.tmSub σ a).1 ≫ T.extend σ A = σ ≫ a.1 :=
      (T.isPullback σ A).lift_fst _ _ _
    rw [hlift, F.fnc.map_comp, Category.assoc]
    exact ((S.isPullback (F.fnc.map σ) (F.tyMap A)).lift_fst _ _ _).symm
  · rw [(tmCast (F.tyMap_sub σ A) (F.tmMap (T.tmSub σ a))).2,
      (S.tmSub (F.fnc.map σ) (F.tmMap a)).2]

/-- The comparison transported along an equality of types. -/
@[reassoc] theorem extIso_eqToHom (F : Mor T S) {Γ : C} {A B : T.Ty Γ} (e : A = B) :
    F.fnc.map (eqToHom (congrArg (T.ext Γ) e)) ≫ (F.extIso B).hom
      = (F.extIso A).hom ≫ eqToHom (congrArg (S.ext (F.fnc.obj Γ)) (congrArg F.tyMap e)) := by
  cases e
  simp

/-- The identity morphism. -/
@[reducible] def id (T : Cwa.{u, v, w} C) : Mor T T where
  fnc := 𝟭 C
  tyMap A := A
  tyMap_sub _ _ := rfl
  extIso A := Iso.refl _
  extIso_disp _ := by simp
  extIso_extend _ _ := by simp

/-- The composite of two morphisms. -/
@[reducible] def comp {U : Cwa.{u'', v'', w''} E} (F : Mor T S) (G : Mor S U) : Mor T U where
  fnc := F.fnc ⋙ G.fnc
  tyMap A := G.tyMap (F.tyMap A)
  tyMap_sub σ A := by rw [F.tyMap_sub, G.tyMap_sub]; rfl
  extIso A := G.fnc.mapIso (F.extIso A) ≪≫ G.extIso (F.tyMap A)
  extIso_disp A := by
    simp only [Functor.mapIso_hom, Iso.trans_hom, Category.assoc, G.extIso_disp,
      ← G.fnc.map_comp, F.extIso_disp]
    rfl
  extIso_extend σ A := by
    have hF := F.extIso_extend σ A
    have hG := G.extIso_extend (F.fnc.map σ) (F.tyMap A)
    simp only [Functor.mapIso_hom, Iso.trans_hom, Functor.comp_map, Functor.comp_obj]
    rw [← Category.assoc, ← G.fnc.map_comp, hF, G.fnc.map_comp, G.fnc.map_comp,
      Category.assoc, Category.assoc, hG]
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    rw [extIso_eqToHom_assoc G (F.tyMap_sub σ A)]
    simp

@[simp] theorem tmMap_id (T : Cwa.{u, v, w} C) {Γ : C} {A : T.Ty Γ} (a : T.Tm Γ A) :
    (Mor.id T).tmMap a = a := by
  refine Tm.ext' ?_
  simp [tmMap, Mor.id]

theorem tmMap_comp {U : Cwa.{u'', v'', w''} E} (F : Mor T S) (G : Mor S U) {Γ : C}
    {A : T.Ty Γ} (a : T.Tm Γ A) : (F.comp G).tmMap a = G.tmMap (F.tmMap a) := by
  refine Tm.ext' ?_
  simp [tmMap, comp]

end Mor

/-! ### The strictified model is functorial -/

variable (F : C ⥤ D)

/-- The local universe presenting the image of a type. -/
@[reducible, simps] def luMap {Γ : C} (A : LuTy Γ) : LuTy (F.obj Γ) :=
  ⟨F.obj A.base, F.obj A.total, F.map A.proj, F.map A.cls⟩

theorem luMap_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    luMap F (LuTy.sub σ A) = LuTy.sub (F.map σ) (luMap F A) := by
  simp [luMap, LuTy.sub]

variable [HasPullbacks C] [HasPullbacks D]

/-- Transporting an extended context along an equality of types carries the generic element to the
generic element. -/
theorem eqToHom_lu_gen {X : C} {A B : LuTy X} (e : A = B) :
    eqToHom (congrArg (LuTy.ext X) e) ≫ LuTy.gen B
      = LuTy.gen A ≫ eqToHom (congrArg LuTy.total e) := by
  cases e
  simp

/-- Transporting an extended context along an equality of types lies over the base context. -/
@[reassoc] theorem eqToHom_lu_disp {X : C} {A B : LuTy X} (e : A = B) :
    eqToHom (congrArg (LuTy.ext X) e) ≫ LuTy.disp B = LuTy.disp A := by
  cases e
  simp

variable [∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F]

/-- The image of an extended context is the extended context of the image, because the extension
square is a pullback and `F` preserves it. -/
noncomputable def luExtIso {Γ : C} (A : LuTy Γ) :
    F.obj (LuTy.ext Γ A) ≅ LuTy.ext (F.obj Γ) (luMap F A) :=
  ((LuTy.isPullback_gen A).map F).isoIsPullback _ _ (LuTy.isPullback_gen (luMap F A))

@[simp] theorem luExtIso_hom_disp {Γ : C} (A : LuTy Γ) :
    (luExtIso F A).hom ≫ LuTy.disp (luMap F A) = F.map (LuTy.disp A) :=
  ((LuTy.isPullback_gen A).map F).isoIsPullback_hom_snd _ _ (LuTy.isPullback_gen (luMap F A))

@[simp] theorem luExtIso_hom_gen {Γ : C} (A : LuTy Γ) :
    (luExtIso F A).hom ≫ LuTy.gen (luMap F A) = F.map (LuTy.gen A) :=
  ((LuTy.isPullback_gen A).map F).isoIsPullback_hom_fst _ _ (LuTy.isPullback_gen (luMap F A))

/-- The comparison is compatible with the action of a substitution on extended contexts: both
sides are maps into a pullback, so it is enough to compare them with the two legs. -/
theorem luExtIso_extend {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    F.map (LuTy.extend σ A) ≫ (luExtIso F A).hom
      = (luExtIso F (LuTy.sub σ A)).hom
          ≫ eqToHom (congrArg (LuTy.ext (F.obj Δ)) (luMap_sub F σ A))
          ≫ LuTy.extend (F.map σ) (luMap F A) := by
  refine (LuTy.isPullback_gen (luMap F A)).hom_ext ?_ ?_
  · simp only [Category.assoc, LuTy.extend_gen, luExtIso_hom_gen]
    conv_rhs => rw [eqToHom_lu_gen (luMap_sub F σ A), ← Category.assoc, luExtIso_hom_gen]
    rw [← F.map_comp, LuTy.extend_gen]
    simp
  · simp only [Category.assoc, LuTy.extend_disp, luExtIso_hom_disp, ← F.map_comp]
    rw [eqToHom_lu_disp_assoc, ← Category.assoc, luExtIso_hom_disp, ← F.map_comp]
    exact luMap_sub F σ A

/-- **A pullback-preserving functor is a morphism of the strictified models.** -/
noncomputable def morOfPullbackPreserving : Mor (Cwa.ofPullbacks C) (Cwa.ofPullbacks D) where
  fnc := F
  tyMap A := luMap F A
  tyMap_sub σ A := luMap_sub F σ A
  extIso A := luExtIso F A
  extIso_disp A := luExtIso_hom_disp F A
  extIso_extend σ A := luExtIso_extend F σ A

/-- The hypothesis above is the usual one: a functor preserving all pullbacks gives a morphism of
the strictified models. -/
noncomputable def morOfPreservesPullbacks (G : C ⥤ D) [PreservesLimitsOfShape WalkingCospan G] :
    Mor (Cwa.ofPullbacks C) (Cwa.ofPullbacks D) :=
  morOfPullbackPreserving G

end Cwa
