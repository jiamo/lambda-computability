/-
**How far strictification is from an equivalence: fullness.**

`Start/CwaStrictFunctor.lean` builds `Cwa.strictification : PbCat ⥤ Cwa.Model`, and
`Start/CwaStrictSection.lean` proves it faithful and conservative (it reflects isomorphisms).
The remaining question for the comparison between models of a dependent type theory and
categories with pullbacks — the 1-categorical shadow of the biequivalence with locally cartesian
closed categories — is whether that functor is **full**: is every morphism of models between two
strictified categories induced by a pullback-preserving functor?

This module answers it, in two halves.

*The functor part is always induced.*  A morphism of models `G` out of a strictified category
carries the extension squares of local universes to extension squares, up to the comparison
isomorphisms of `Cwa.Mor.extIso`, and *every* pullback square of a category with pullbacks is
isomorphic to one of those (a morphism `p : Y ⟶ Γ` is presented by the local universe
`LuTy.ofHom p`).  Hence `Cwa.Mor.map_isPullback`: the functor on contexts underlying a morphism of
strictified models preserves pullbacks, with no hypothesis at all, so it *is* a morphism of
`PbCat` (`Cwa.exists_pbCatHom_fnc`).

*The action on types need not be the induced one.*  What a morphism of models is free to choose is
the *presentation* of a type: the local universe it assigns is only pinned down up to isomorphism
over the base, by `Cwa.tyMapCompareIso`, and nothing forces it to be the transported one on the
nose.  A two-object indiscrete category makes this concrete: every hom-set has exactly one element,
so swapping the total space of a local universe for the other object of the category is a morphism
of models over the identity functor which is not the induced one.  Therefore
`Cwa.not_full_strictification`: strictification is **not** full.

So the honest 1-categorical statement is the conjunction: strictification is faithful, reflects
isomorphisms, is full on the underlying functors, and is full up to a canonical isomorphism of
presentations — but not full on the nose.  Any equivalence with locally cartesian closed
categories must therefore be stated up to isomorphism of types, exactly as the failure of
2-functoriality in `Start/CwaStrictRigid.lean` already indicated for the 2-cells.

Main definitions:

* `Cwa.Chaotic` — the indiscrete category on two objects, used for the counterexample;
* `Cwa.chaoticSwapMor` — a morphism of the strictified model of `Chaotic` to itself over the
  identity functor which is not induced by any functor.

Main results:

* `Cwa.Mor.map_isPullback` — **the functor underlying a morphism of strictified models preserves
  pullbacks**;
* `Cwa.Mor.preservesLimitsOfShape_fnc`, `Cwa.exists_pbCatHom_fnc` — hence it is a morphism of
  categories with pullbacks;
* `Cwa.tyMapCompareIso`, `Cwa.tyMapCompareIso_hom_disp` — the type it assigns is canonically
  isomorphic, over the base, to the transported one;
* `Cwa.not_full_strictification` — **strictification is not full**.
-/

import Start.CwaStrictSection

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v u' v'

open CategoryTheory Limits

namespace Cwa

/-! ### The functor underlying a morphism of strictified models preserves pullbacks -/

section Preserves

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasPullbacks C] [HasPullbacks D]
  (G : Mor (Cwa.ofPullbacks C) (Cwa.ofPullbacks D))

/-- The comparison isomorphism of a substituted extended context, with the identification of the
substituted type folded into it. -/
noncomputable def subExtIso {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    G.fnc.obj (LuTy.ext Δ (LuTy.sub σ A))
      ≅ LuTy.ext (G.fnc.obj Δ) (LuTy.sub (G.fnc.map σ) (G.tyMap A)) :=
  G.extIso (LuTy.sub σ A)
    ≪≫ eqToIso (congrArg (LuTy.ext (G.fnc.obj Δ)) (G.tyMap_sub σ A))

theorem subExtIso_hom_extend {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    (subExtIso G σ A).hom ≫ LuTy.extend (G.fnc.map σ) (G.tyMap A)
      = G.fnc.map (LuTy.extend σ A) ≫ (G.extIso A).hom := by
  simpa [subExtIso, Category.assoc] using (G.extIso_extend σ A).symm

theorem subExtIso_hom_disp {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    (subExtIso G σ A).hom ≫ LuTy.disp (LuTy.sub (G.fnc.map σ) (G.tyMap A))
      = G.fnc.map (LuTy.disp (LuTy.sub σ A)) := by
  rw [subExtIso, Iso.trans_hom, Category.assoc, eqToIso.hom,
    eqToHom_lu_disp (G.tyMap_sub σ A)]
  exact G.extIso_disp (LuTy.sub σ A)

/-- **The image of an extension square is a pullback**: the comparison isomorphisms identify it
with the extension square of the image type, which is a pullback in the target model. -/
theorem isPullback_map_extend {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) :
    IsPullback (G.fnc.map (LuTy.extend σ A)) (G.fnc.map (LuTy.disp (LuTy.sub σ A)))
      (G.fnc.map (LuTy.disp A)) (G.fnc.map σ) := by
  refine (LuTy.isPullback_extend (G.fnc.map σ) (G.tyMap A)).of_iso'
    (subExtIso G σ A) (G.extIso A) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact subExtIso_hom_extend G σ A
  · simpa using subExtIso_hom_disp G σ A
  · simpa using G.extIso_disp A
  · simp

/-- **The functor underlying a morphism of strictified models preserves pullbacks.**  Every
pullback square is isomorphic to the extension square of the local universe presenting one of its
legs, and those are carried to pullbacks. -/
theorem Mor.map_isPullback {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) :
    IsPullback (G.fnc.map fst) (G.fnc.map snd) (G.fnc.map f) (G.fnc.map g) := by
  -- the local universe presenting `f`, and the identification of `X` with its extended context
  set A : LuTy Z := LuTy.ofHom f with hA
  set ι : X ≅ LuTy.ext Z A := LuTy.isoExtOfHom f with hι
  have hιdisp : ι.hom ≫ LuTy.disp A = f := LuTy.isoExtOfHom_disp f
  -- the given square, with `X` replaced by the extended context
  have h' : IsPullback (fst ≫ ι.hom) snd (LuTy.disp A) g :=
    h.of_iso (Iso.refl _) ι (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa using hιdisp.symm) (by simp)
  -- the comparison with the extension square of `A` along `g`
  set κ : LuTy.ext Y (LuTy.sub g A) ≅ P :=
    (LuTy.isPullback_extend g A).isoIsPullback _ _ h' with hκ
  have hκfst : κ.inv ≫ LuTy.extend g A = fst ≫ ι.hom :=
    (LuTy.isPullback_extend g A).isoIsPullback_inv_fst _ _ h'
  have hκsnd : κ.inv ≫ LuTy.disp (LuTy.sub g A) = snd :=
    (LuTy.isPullback_extend g A).isoIsPullback_inv_snd _ _ h'
  refine (isPullback_map_extend G g A).of_iso' (G.fnc.mapIso κ.symm) (G.fnc.mapIso ι)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Functor.mapIso_hom, Iso.symm_hom, ← G.fnc.map_comp]
    exact congrArg G.fnc.map hκfst
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← G.fnc.map_comp]
    exact congrArg G.fnc.map hκsnd
  · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id, ← G.fnc.map_comp]
    exact congrArg G.fnc.map hιdisp
  · simp

/-- The functor underlying a morphism of strictified models preserves the pullback of any
cospan. -/
theorem Mor.preservesLimitCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) G.fnc :=
  preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f g).isLimit
    ((PullbackCone.isLimitMapConeEquiv _ G.fnc).symm
      (Mor.map_isPullback G (IsPullback.of_hasPullback f g)).isLimit)

/-- **The functor underlying a morphism of strictified models preserves pullbacks**, in the form
of a `PreservesLimitsOfShape` statement. -/
theorem Mor.preservesLimitsOfShape_fnc :
    PreservesLimitsOfShape WalkingCospan G.fnc :=
  ⟨fun {K} => by
    have := Mor.preservesLimitCospan G (K.map WalkingCospan.Hom.inl)
      (K.map WalkingCospan.Hom.inr)
    exact preservesLimit_of_iso_diagram G.fnc (diagramIsoCospan K).symm⟩

end Preserves

/-! ### Fullness on the underlying functors, and only up to isomorphism on types -/

section Compare

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasPullbacks C] [HasPullbacks D]
  (G : Mor (Cwa.ofPullbacks C) (Cwa.ofPullbacks D))

/-- **The type assigned by a morphism of strictified models presents the same slice object as the
transported one**: the two extended contexts are canonically isomorphic. -/
noncomputable def tyMapCompareIso {Γ : C} (A : LuTy Γ) :
    LuTy.ext (G.fnc.obj Γ) (G.tyMap A)
      ≅ LuTy.ext (G.fnc.obj Γ) (luMap G.fnc A) :=
  haveI := Mor.preservesLimitsOfShape_fnc G
  (G.extIso A).symm ≪≫ luExtIso G.fnc A

/-- The comparison of the two presentations lies over the base context: the two display maps are
isomorphic in the slice. -/
theorem tyMapCompareIso_hom_disp {Γ : C} (A : LuTy Γ) :
    haveI := Mor.preservesLimitsOfShape_fnc G
    (tyMapCompareIso G A).hom ≫ LuTy.disp (luMap G.fnc A) = LuTy.disp (G.tyMap A) := by
  have := Mor.preservesLimitsOfShape_fnc G
  rw [tyMapCompareIso, Iso.trans_hom, Category.assoc, luExtIso_hom_disp, Iso.symm_hom,
    Iso.inv_comp_eq]
  exact (G.extIso_disp A).symm

end Compare

/-- **Strictification is full on the underlying functors**: the functor on contexts of a morphism
of strictified models is a morphism of categories with pullbacks. -/
theorem exists_pbCatHom_fnc {X Y : PbCat.{u, v}}
    (G : strictification.obj X ⟶ strictification.obj Y) :
    ∃ f : X ⟶ Y, f.fnc = G.fnc := by
  have hX : HasPullbacks (strictification.obj X).Ctx := X.hasPullbacks
  have hY : HasPullbacks (strictification.obj Y).Ctx := Y.hasPullbacks
  refine ⟨⟨G.fnc, ?_⟩, rfl⟩
  exact Mor.preservesLimitsOfShape_fnc G

/-! ### Strictification is not full -/

/-- The **indiscrete category on two objects**: between any two objects there is exactly one
morphism. -/
structure Chaotic where
  /-- Which of the two objects this is. -/
  val : Bool

instance Chaotic.instCategory : Category.{0} Chaotic where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

instance Chaotic.instSubsingletonHom (X Y : Chaotic) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The unique morphism between two objects of the indiscrete category. -/
def Chaotic.hom (X Y : Chaotic) : X ⟶ Y := ⟨⟩

/-- Any two objects of the indiscrete category are isomorphic. -/
def Chaotic.iso (X Y : Chaotic) : X ≅ Y where
  hom := Chaotic.hom X Y
  inv := Chaotic.hom Y X
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Every diagram in the indiscrete category has a limit: any object is one, since all the
morphisms needed are unique. -/
instance Chaotic.instHasLimitsOfShape (J : Type) [SmallCategory J] :
    HasLimitsOfShape J Chaotic where
  has_limit F :=
    ⟨⟨{ cone := { pt := ⟨false⟩, π := { app := fun j => Chaotic.hom _ (F.obj j) } }
        isLimit :=
          { lift := fun s => Chaotic.hom _ _
            fac := fun _ _ => Subsingleton.elim _ _
            uniq := fun _ _ _ => Subsingleton.elim _ _ } }⟩⟩

instance Chaotic.instHasPullbacks : HasPullbacks Chaotic :=
  inferInstanceAs (HasLimitsOfShape WalkingCospan Chaotic)

/-- Swapping the two objects of the indiscrete category. -/
def Chaotic.swap (X : Chaotic) : Chaotic := ⟨!X.val⟩

theorem Chaotic.swap_ne (X : Chaotic) : Chaotic.swap X ≠ X := by
  intro h
  have : (!X.val) = X.val := congrArg Chaotic.val h
  revert this
  cases X.val <;> simp

/-- **A morphism of the strictified model of the indiscrete category to itself which is not
induced by any functor**: it is the identity on contexts, but it presents every type by the *other*
object of the category.  All the laws hold because every hom-set is a singleton. -/
noncomputable def chaoticSwapMor : Mor (Cwa.ofPullbacks Chaotic) (Cwa.ofPullbacks Chaotic) where
  fnc := 𝟭 Chaotic
  tyMap {_} A := ⟨A.base, Chaotic.swap A.total, Chaotic.hom _ _, A.cls⟩
  tyMap_sub _ _ := rfl
  extIso _ := Chaotic.iso _ _
  extIso_disp _ := Subsingleton.elim _ _
  extIso_extend _ _ := Subsingleton.elim _ _

/-- **Strictification is not full.**  The swapping morphism of models above has the identity as its
functor on contexts, so a preimage would have to induce the transported presentation of types,
which assigns the *same* total space, not the swapped one. -/
theorem not_full_strictification : ¬ Functor.Full strictification.{0, 0} := by
  intro hfull
  obtain ⟨f, hf⟩ :=
    hfull.map_surjective (X := (⟨Chaotic⟩ : PbCat.{0, 0})) (Y := (⟨Chaotic⟩ : PbCat.{0, 0}))
      chaoticSwapMor
  -- the underlying functor of a preimage is the identity
  have hfnc : f.fnc = 𝟭 Chaotic := congrArg Mor.fnc hf
  -- compare the total spaces of the local universes assigned to one type
  have hty := congrArg
    (fun m : Mor (Cwa.ofPullbacks Chaotic) (Cwa.ofPullbacks Chaotic) =>
      (m.tyMap (Γ := (⟨false⟩ : Chaotic))
        ⟨⟨false⟩, ⟨false⟩, Chaotic.hom _ _, Chaotic.hom _ _⟩).total) hf
  simp only [strictification, morOfPreservesPullbacks, morOfPullbackPreserving, luMap,
    chaoticSwapMor, Chaotic.swap] at hty
  rw [hfnc] at hty
  simp at hty

end Cwa
