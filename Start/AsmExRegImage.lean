/-
**Image factorizations in the exact completion of the assemblies.**

Every morphism of the completion factors as an epimorphism, which is the identity on points,
followed by a monomorphism.  The middle object is the base of the source with the relation
*pulled back* along the map: a proof that `x` and `y` have the same image carries, besides a
proof of `f x ~ f y` in the target, a realizer of `x` and one of `y` — which is what keeps the
endpoints of a proof computable, exactly as for the equalizer of `Start/AsmExRegEq.lean`.

The two halves of the factorization are cheap for the same reason `Realizability.ExReg.epi_quot`
is: the image has the *same base assembly*, with the same realizers, as the source, so a homotopy
out of one is a homotopy out of the other.

Main results:

* `Realizability.ExReg.imgObj` — the image of a pre-morphism;
* `Realizability.ExReg.imgFac_comp_imgIncl` — **the factorization**;
* `Realizability.ExReg.epi_imgFac`, `.mono_imgIncl` — its first factor is an epimorphism and its
  second a monomorphism.

Whether the first factor is a *regular* epimorphism, and whether such factorizations are stable
under pullback — that is, the regularity of the completion — is not proved here.
-/

import Start.AsmExRegQuot

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A] {E F G : ERel.{u, v} A}

/-- The **image** of a pre-morphism: the base of the source, with the relation pulled back along
the map, a proof carrying in addition a realizer of each of its endpoints. -/
def imgObj (f : Pre E F) : ERel.{u, v} A where
  base := E.base
  Prf w x y := ∃ a b c, E.base.realizes a x ∧ E.base.realizes b y ∧
    F.Prf c (f.toFun x) (f.toFun y) ∧ w = PCA.pairEl a (PCA.pairEl b c)
  ends := by
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.fstComb A) (PCA.comp (PCA.fstComb A) (PCA.sndComb A))
    refine ⟨q, fun w x y h => ?_⟩
    obtain ⟨a, b, c, ha, hb, _, rfl⟩ := h
    exact ⟨PCA.pairEl a b,
      hq _ _ _ (mem_fstComb _ _) (mem_comp (mem_sndComb a (PCA.pairEl b c)) (mem_fstComb b c)),
      a, b, ha, hb, rfl⟩
  refl' := by
    obtain ⟨rE, hrE⟩ := E.refl'
    obtain ⟨cf, hcf⟩ := f.tracked
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.i A) (PCA.comp cf rE)
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.i A) q₂
    refine ⟨q, fun a x ha => ?_⟩
    obtain ⟨u, hu, hux⟩ := hrE a x ha
    obtain ⟨c, hc, hcx⟩ := hcf u x x hux
    have hi : a ∈ PCA.app (PCA.i A) a := by rw [PCA.i_app]; exact Part.mem_some _
    exact ⟨PCA.pairEl a (PCA.pairEl a c),
      hq _ _ _ hi (hq₂ _ _ _ hi (mem_comp hu hc)), a, a, c, ha, ha, hcx, rfl⟩
  symm' := by
    obtain ⟨sF, hsF⟩ := F.symm'
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.fstComb A)
      (PCA.comp sF (PCA.comp (PCA.sndComb A) (PCA.sndComb A)))
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.comp (PCA.fstComb A) (PCA.sndComb A)) q₂
    refine ⟨q, fun w x y h => ?_⟩
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := h
    obtain ⟨c', hc', hcx⟩ := hsF c (f.toFun x) (f.toFun y) hc
    have hsnd : PCA.pairEl b c ∈ PCA.app (PCA.sndComb A) (PCA.pairEl a (PCA.pairEl b c)) :=
      mem_sndComb _ _
    exact ⟨PCA.pairEl b (PCA.pairEl a c'),
      hq _ _ _ (mem_comp hsnd (mem_fstComb b c))
        (hq₂ _ _ _ (mem_fstComb _ _) (mem_comp (mem_comp hsnd (mem_sndComb b c)) hc')),
      b, a, c', hb, ha, hcx, rfl⟩
  trans' := by
    obtain ⟨tF, htF⟩ := F.trans'
    obtain ⟨q₂, hq₂⟩ := exists_binPair (PCA.kI A) tF
    obtain ⟨q, hq⟩ := exists_binPair (PCA.k : A) q₂
    refine ⟨q, fun w w' x y z hw hw' => ?_⟩
    obtain ⟨a, b, c, ha, _, hc, rfl⟩ := hw
    obtain ⟨a', b', c', _, hb', hc', rfl⟩ := hw'
    obtain ⟨v, hv, hvx⟩ := htF c c' (f.toFun x) (f.toFun y) (f.toFun z) hc hc'
    refine ⟨PCA.pairEl a (PCA.pairEl b' v),
      hq a (PCA.pairEl b c) a' (PCA.pairEl b' c') a (PCA.pairEl b' v) ?_
        (hq₂ b c b' c' b' v ?_ hv), a, b', v, ha, hb', hvx, rfl⟩
    · rw [k_papp]; exact Part.mem_some _
    · rw [PCA.kI_app]; exact Part.mem_some _

@[simp] theorem imgObj_base (f : Pre E F) : (imgObj f).base = E.base := rfl

/-- The first factor: the identity on points. -/
noncomputable def imgFacPre (f : Pre E F) : Pre E (imgObj f) where
  toFun := _root_.id
  tracked := by
    obtain ⟨tE, htE⟩ := E.ends
    obtain ⟨cf, hcf⟩ := f.tracked
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.comp (PCA.sndComb A) tE) cf
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.comp (PCA.fstComb A) tE) q₂
    refine ⟨q, fun w x y h => ?_⟩
    obtain ⟨v, hv, a, b, ha, hb, rfl⟩ := htE w x y h
    obtain ⟨c, hc, hcx⟩ := hcf w x y h
    exact ⟨PCA.pairEl a (PCA.pairEl b c),
      hq _ _ _ (mem_comp hv (mem_fstComb a b))
        (hq₂ _ _ _ (mem_comp hv (mem_sndComb a b)) hc),
      a, b, c, ha, hb, hcx, rfl⟩

/-- The second factor: the map itself. -/
def imgInclPre (f : Pre E F) : Pre (imgObj f) F where
  toFun := f.toFun
  tracked := ⟨PCA.comp (PCA.sndComb A) (PCA.sndComb A), fun w x y h => by
    obtain ⟨a, b, c, _, _, hc, rfl⟩ := h
    exact ⟨c, mem_comp (mem_sndComb a (PCA.pairEl b c)) (mem_sndComb b c), hc⟩⟩

theorem imgFacPre_comp_imgInclPre (f : Pre E F) :
    (imgFacPre f).comp (imgInclPre f) = f := Pre.ext rfl

/-- The first factor of the image factorization. -/
noncomputable def imgFac (f : Pre E F) : E ⟶ imgObj f := homOf (imgFacPre f)

/-- The second factor of the image factorization. -/
noncomputable def imgIncl (f : Pre E F) : imgObj f ⟶ F := homOf (imgInclPre f)

/-- **The image factorization.** -/
theorem imgFac_comp_imgIncl (f : Pre E F) : imgFac f ≫ imgIncl f = homOf f :=
  congrArg homOf (imgFacPre_comp_imgInclPre f)

/-- The first factor is an epimorphism: the image has the same base, with the same realizers, as
the source, so a homotopy out of one is a homotopy out of the other. -/
instance epi_imgFac (f : Pre E F) : Epi (imgFac f) where
  left_cancellation {G} u v h := by
    obtain ⟨p, rfl⟩ := homOf_surjective u
    obtain ⟨q, rfl⟩ := homOf_surjective v
    obtain ⟨t, ht⟩ := homOf_eq_iff.1 h
    exact homOf_eq_iff.2 ⟨t, fun a x ha => ht a x ha⟩

/-- The second factor is a monomorphism: two maps into the image that agree after it are
homotopic, the missing realizers being supplied by their own trackers. -/
instance mono_imgIncl (f : Pre E F) : Mono (imgIncl f) where
  right_cancellation {G} u v h := by
    obtain ⟨p, rfl⟩ := homOf_surjective u
    obtain ⟨q, rfl⟩ := homOf_surjective v
    obtain ⟨t, ht⟩ := homOf_eq_iff.1 h
    obtain ⟨rp, hrp⟩ := p.trackedBase
    obtain ⟨rq, hrq⟩ := q.trackedBase
    obtain ⟨w₂, hw₂⟩ := exists_pairOf rq t
    obtain ⟨w, hw⟩ := exists_pairOf rp w₂
    refine homOf_eq_iff.2 ⟨w, fun a z ha => ?_⟩
    obtain ⟨b₁, hb₁, hb₁z⟩ := hrp a z ha
    obtain ⟨b₂, hb₂, hb₂z⟩ := hrq a z ha
    obtain ⟨c, hc, hcz⟩ := ht a z ha
    exact ⟨PCA.pairEl b₁ (PCA.pairEl b₂ c),
      hw _ _ _ hb₁ (hw₂ _ _ _ hb₂ hc), b₁, b₂, c, hb₁z, hb₂z, hcz, rfl⟩

end ExReg

end Realizability
