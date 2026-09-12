/-
**The exact completion of the assemblies is a regular category.**

`Start/AsmExRegCover.lean` identifies the regular epimorphisms of the completion with its
*covers*: the morphisms with a computable section up to the relation.  This module uses that
description to prove the two conditions that, on top of finite limits, make a category regular
in the sense of `CategoryTheory.Regular`:

* the kernel pair of a morphism has a coequalizer — the image of the morphism, whose first
  factor is a regular epimorphism and whose second factor is a monomorphism;
* regular epimorphisms are stable under base change.

The second one is where the realizability content is.  The base of an object, with equality, is
projective for the covers: from a realizer of a point `x` of the base of `X` one computes, using
the section of the cover `g` and the tracker of `f`, a point of `Y` over `f x`.  That is a
morphism `emb X.base ⟶ Y` which, paired with the canonical cover of `X`, lifts through the
pullback; the pulled-back leg therefore has the canonical cover of `X` factoring through it, and
a right factor of a cover is a cover.

Main results:

* `Realizability.ExReg.cover_of_isPullback` — **a cover pulled back along any morphism is a
  cover**;
* `Realizability.ExReg.hasCoequalizer_of_isKernelPair` — **kernel pairs have coequalizers**;
* `Realizability.ExReg.instRegular` — **the completion is a regular category.**
-/

import Start.AsmExRegCover
import Mathlib.CategoryTheory.RegularCategory.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A]

/-! ### The base of an object is projective for the covers -/

/-- Given a cover `q` with section `(gs, s)` and any pre-morphism `pf` into the same target, the
pre-morphism from the base of the source of `pf` that picks, for a point `x`, the point
`gs (pf x)` computed from a realizer of `x`. -/
noncomputable def liftPre {X Y S : ERel.{u, v} A} (pf : Pre X S) (q : Pre Y S)
    (gs : S.base.carrier → Y.base.carrier) (s : A) (hs : IsSection q gs s) :
    Pre (eqERel X.base) Y where
  toFun x := gs (pf.toFun x)
  tracked := by
    obtain ⟨rf, hrf⟩ := pf.trackedBase
    obtain ⟨rY, hrY⟩ := Y.refl'
    refine ⟨PCA.comp rY (PCA.comp (PCA.comp (PCA.fstComb A) s) rf), fun a x y h => ?_⟩
    obtain ⟨ha, rfl⟩ := h
    obtain ⟨b, hb, hbx⟩ := hrf a x ha
    obtain ⟨w, hw, a₁, c₁, ha₁, _, rfl⟩ := hs b (pf.toFun x) hbx
    obtain ⟨v, hv, hvx⟩ := hrY a₁ (gs (pf.toFun x)) ha₁
    exact ⟨v, mem_comp (mem_comp hb (mem_comp hw (mem_fstComb a₁ c₁))) hv, hvx⟩

/-- The lift of the canonical cover of `X` through a cover `q`, composed with `q`, is the
canonical cover of `X` composed with `pf`: the section of `q` provides the homotopy. -/
theorem liftPre_comp {X Y S : ERel.{u, v} A} (pf : Pre X S) (q : Pre Y S)
    (gs : S.base.carrier → Y.base.carrier) (s : A) (hs : IsSection q gs s) :
    homOf ((liftPre pf q gs s hs).comp q) = homOf ((quotPre X).comp pf) := by
  obtain ⟨rf, hrf⟩ := pf.trackedBase
  refine homOf_eq_iff.2 ⟨PCA.comp (PCA.comp (PCA.sndComb A) s) rf, fun a x ha => ?_⟩
  obtain ⟨b, hb, hbx⟩ := hrf a x ha
  obtain ⟨w, hw, a₁, c₁, _, hc₁, rfl⟩ := hs b (pf.toFun x) hbx
  exact ⟨c₁, mem_comp hb (mem_comp hw (mem_sndComb a₁ c₁)), hc₁⟩

/-! ### Base change -/

/-- **A cover pulled back along any morphism is a cover.** -/
theorem cover_of_isPullback {X Y Y' S : ERel.{u, v} A} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (hP : IsPullback f' g' g f) (hg : Cover g) : Cover g' := by
  obtain ⟨q, rfl, gsec⟩ := hg
  obtain ⟨gs, s, hs⟩ := gsec
  obtain ⟨pf, rfl⟩ := homOf_surjective f
  have hcomm : homOf (liftPre pf q gs s hs) ≫ homOf q = quot X ≫ homOf pf :=
    liftPre_comp pf q gs s hs
  have hfac : hP.lift (homOf (liftPre pf q gs s hs)) (quot X) hcomm ≫ g' = quot X :=
    hP.lift_snd _ _ hcomm
  exact Cover.of_comp_right (h := hP.lift (homOf (liftPre pf q gs s hs)) (quot X) hcomm)
    (by rw [hfac]; exact cover_quot X)

/-- Regular epimorphisms of the completion are stable under base change. -/
theorem regularEpi_isStableUnderBaseChange :
    (MorphismProperty.regularEpi (ERel.{u, v} A)).IsStableUnderBaseChange := by
  refine ⟨fun {X Y Y' S f g f' g'} hP hg => ?_⟩
  have hgc : Cover g := cover_of_isRegularEpi hg
  exact isRegularEpi_of_cover (cover_of_isPullback hP hgc)

/-! ### Coequalizers of kernel pairs -/

/-- **The kernel pair of a morphism has a coequalizer**: the first factor of the image
factorization of the morphism, which is a regular epimorphism with the same kernel pair. -/
theorem hasCoequalizer_of_isKernelPair {X Y Z : ERel.{u, v} A} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X}
    (h : IsKernelPair f g₁ g₂) : HasCoequalizer g₁ g₂ := by
  obtain ⟨p, rfl⟩ := homOf_surjective f
  rw [← imgFac_comp_imgIncl p] at h
  have hk : IsKernelPair (imgFac p) g₁ g₂ := h.cancel_right_of_mono
  exact ⟨⟨⟨_, hk.toCoequalizer (regularEpi_imgFac p)⟩⟩⟩

/-- **Kernel pairs are effective**: the kernel pair of a morphism is the kernel pair of its own
coequalizer, the first factor of the image factorization of the morphism. -/
theorem isKernelPair_and_isColimit_of_isKernelPair {X Y Z : ERel.{u, v} A} {f : X ⟶ Y}
    {g₁ g₂ : Z ⟶ X} (h : IsKernelPair f g₁ g₂) :
    ∃ (Q : ERel.{u, v} A) (π : X ⟶ Q) (hk : IsKernelPair π g₁ g₂),
      Nonempty (IsColimit (Cofork.ofπ π hk.w)) := by
  obtain ⟨p, rfl⟩ := homOf_surjective f
  rw [← imgFac_comp_imgIncl p] at h
  have hk : IsKernelPair (imgFac p) g₁ g₂ := h.cancel_right_of_mono
  exact ⟨imgObj p, imgFac p, hk, ⟨hk.toCoequalizer (regularEpi_imgFac p)⟩⟩

/-! ### Regularity -/

/-- **The exact completion of the assemblies is a regular category.** -/
instance instRegular : Regular (ERel.{u, v} A) where
  hasCoequalizer_of_isKernelPair := hasCoequalizer_of_isKernelPair
  regularEpiIsStableUnderBaseChange := regularEpi_isStableUnderBaseChange

end ExReg

end Realizability
