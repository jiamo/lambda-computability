/-
**The covers of the exact completion of the assemblies are exactly its regular epimorphisms.**

`Start/AsmExRegImage.lean` factors every morphism of the completion as an epimorphism followed by
a monomorphism, and `Start/AsmExRegQuot.lean` shows the canonical map from the base of a
pseudo-equivalence relation to be a *regular* epimorphism.  This module identifies the regular
epimorphisms of the completion in computational terms.

A pre-morphism `p : E ⟶ F` is a **cover** when it has a section up to the relation, computably:
a function `g` on points and an element of the algebra which, from a realizer of `y`, computes
both a realizer of `g y` and a proof that `p (g y)` is related to `y`.  This is the realizability
reading of surjectivity: not that every point of the target is hit, but that a preimage is
*computed* from a realizer of the point, uniformly.

Main definitions and results:

* `Realizability.ExReg.CoverPre`, `Realizability.ExReg.Cover` — covers of pre-morphisms and of
  morphisms;
* `Realizability.ExReg.cover_quot`, `Realizability.ExReg.Cover.comp`,
  `Realizability.ExReg.Cover.of_comp_right`, `Realizability.ExReg.cover_of_isIso` — the covers
  contain the canonical quotient maps and the isomorphisms, and are closed under composition and
  under right factors;
* `Realizability.ExReg.regularEpi_imgFac` — **the first factor of the image factorization is a
  regular epimorphism**, because composing it with the cover of the source gives the cover of the
  image;
* `Realizability.ExReg.isIso_imgIncl_of_cover` — a cover has an invertible second factor;
* `Realizability.ExReg.cover_iff_isRegularEpi` — **a morphism of the completion is a regular
  epimorphism if and only if it is a cover.**
-/

import Start.AsmExRegImage

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A] {E F G : ERel.{u, v} A}

/-! ### Covers -/

/-- The section data of a cover, spelled out: a function `g` on points and an element `s` of the
algebra which, from a realizer of `y`, computes a realizer of `g y` together with a proof that
`p (g y)` is related to `y`. -/
def IsSection (p : Pre E F) (g : F.base.carrier → E.base.carrier) (s : A) : Prop :=
  ∀ (b : A) (y : F.base.carrier), F.base.realizes b y → ∃ v ∈ PCA.app s b, ∃ a c : A,
    E.base.realizes a (g y) ∧ F.Prf c (p.toFun (g y)) y ∧ v = PCA.pairEl a c

/-- A pre-morphism is a **cover** when it has a section up to the relation, computably: a
function `g` on points, and an element of the algebra which turns a realizer of `y` into the pair
of a realizer of `g y` and a proof that `p (g y)` is related to `y`. -/
def CoverPre (p : Pre E F) : Prop := ∃ (g : F.base.carrier → E.base.carrier) (s : A),
  IsSection p g s

/-- Being a cover only depends on the homotopy class. -/
theorem CoverPre.of_homotopic {p q : Pre E F} (hp : CoverPre p) (h : Homotopic p q) :
    CoverPre q := by
  obtain ⟨g, s, hs⟩ := hp
  obtain ⟨th, hth⟩ := h
  obtain ⟨sF, hsF⟩ := F.symm'
  obtain ⟨tF, htF⟩ := F.trans'
  obtain ⟨q₂, hq₂⟩ := exists_pairApply tF
    (PCA.comp (PCA.comp sF th) (PCA.comp (PCA.fstComb A) s)) (PCA.comp (PCA.sndComb A) s)
  obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.comp (PCA.fstComb A) s) q₂
  refine ⟨g, qq, fun b y hb => ?_⟩
  obtain ⟨w, hw, a, c, ha, hc, rfl⟩ := hs b y hb
  have hA : a ∈ PCA.app (PCA.comp (PCA.fstComb A) s) b := mem_comp hw (mem_fstComb a c)
  have hC : c ∈ PCA.app (PCA.comp (PCA.sndComb A) s) b := mem_comp hw (mem_sndComb a c)
  obtain ⟨u, hu, hup⟩ := hth a (g y) ha
  obtain ⟨u', hu', hu'p⟩ := hsF u (p.toFun (g y)) (q.toFun (g y)) hup
  obtain ⟨v, hv, hvp⟩ := htF u' c (q.toFun (g y)) (p.toFun (g y)) y hu'p hc
  exact ⟨PCA.pairEl a v, hqq b a v hA (hq₂ b u' c v (mem_comp hA (mem_comp hu hu')) hC hv),
    a, v, ha, hvp, rfl⟩

/-- A **cover** of the completion: a morphism presented by a pre-morphism with a computable
section up to the relation. -/
def Cover (h : E ⟶ F) : Prop := ∃ p : Pre E F, homOf p = h ∧ CoverPre p

theorem cover_homOf_iff {p : Pre E F} : Cover (homOf p) ↔ CoverPre p := by
  constructor
  · rintro ⟨q, hq, hcq⟩
    exact hcq.of_homotopic (homOf_eq_iff.1 hq)
  · exact fun h => ⟨p, rfl, h⟩

/-- **The canonical cover of an object by its base is a cover**: the section is the identity, and
a realizer of a point is turned into a proof by reflexivity. -/
theorem coverPre_quotPre (E : ERel.{u, v} A) : CoverPre (quotPre E) := by
  obtain ⟨r, hr⟩ := E.refl'
  obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.i A) r
  refine ⟨_root_.id, qq, fun b y hb => ?_⟩
  obtain ⟨v, hv, hvy⟩ := hr b y hb
  exact ⟨PCA.pairEl b v, hqq b b v (by rw [PCA.i_app]; exact Part.mem_some _) hv, b, v, hb,
    hvy, rfl⟩

theorem cover_quot (E : ERel.{u, v} A) : Cover (quot E) := cover_homOf_iff.2 (coverPre_quotPre E)

/-- Covers are closed under composition. -/
theorem CoverPre.comp {p : Pre E F} {q : Pre F G} (hp : CoverPre p) (hq : CoverPre q) :
    CoverPre (p.comp q) := by
  obtain ⟨gp, sp, hsp⟩ := hp
  obtain ⟨gq, sq, hsq⟩ := hq
  obtain ⟨cq, hcq⟩ := q.tracked
  obtain ⟨tG, htG⟩ := G.trans'
  obtain ⟨q₂, hq₂⟩ := exists_pairApply tG
    (PCA.comp cq (PCA.comp (PCA.sndComb A) (PCA.comp sp (PCA.comp (PCA.fstComb A) sq))))
    (PCA.comp (PCA.sndComb A) sq)
  obtain ⟨qq, hqq⟩ := exists_pairOf
    (PCA.comp (PCA.fstComb A) (PCA.comp sp (PCA.comp (PCA.fstComb A) sq))) q₂
  refine ⟨fun z => gp (gq z), qq, fun b z hb => ?_⟩
  obtain ⟨w, hw, b', c', hb', hc', rfl⟩ := hsq b z hb
  have hB' : b' ∈ PCA.app (PCA.comp (PCA.fstComb A) sq) b := mem_comp hw (mem_fstComb b' c')
  have hC' : c' ∈ PCA.app (PCA.comp (PCA.sndComb A) sq) b := mem_comp hw (mem_sndComb b' c')
  obtain ⟨w₂, hw₂, a, c, ha, hc, rfl⟩ := hsp b' (gq z) hb'
  have hW₂ : PCA.pairEl a c ∈ PCA.app (PCA.comp sp (PCA.comp (PCA.fstComb A) sq)) b :=
    mem_comp hB' hw₂
  have hA : a ∈ PCA.app (PCA.comp (PCA.fstComb A)
      (PCA.comp sp (PCA.comp (PCA.fstComb A) sq))) b := mem_comp hW₂ (mem_fstComb a c)
  have hC : c ∈ PCA.app (PCA.comp (PCA.sndComb A)
      (PCA.comp sp (PCA.comp (PCA.fstComb A) sq))) b := mem_comp hW₂ (mem_sndComb a c)
  obtain ⟨d, hd, hdp⟩ := hcq c (p.toFun (gp (gq z))) (gq z) hc
  obtain ⟨e, he, hep⟩ := htG d c' (q.toFun (p.toFun (gp (gq z)))) (q.toFun (gq z)) z hdp hc'
  exact ⟨PCA.pairEl a e, hqq b a e hA (hq₂ b d c' e (mem_comp hC hd) hC' he), a, e, ha, hep, rfl⟩

theorem Cover.comp {h : E ⟶ F} {k : F ⟶ G} (hh : Cover h) (hk : Cover k) : Cover (h ≫ k) := by
  obtain ⟨p, rfl, hp⟩ := hh
  obtain ⟨q, rfl, hq⟩ := hk
  rw [homOf_comp]
  exact cover_homOf_iff.2 (hp.comp hq)

/-- If a composite is a cover then so is its right factor. -/
theorem CoverPre.of_comp_right {p : Pre E F} {q : Pre F G} (h : CoverPre (p.comp q)) :
    CoverPre q := by
  obtain ⟨g, s, hs⟩ := h
  obtain ⟨rp, hrp⟩ := p.trackedBase
  obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.comp rp (PCA.comp (PCA.fstComb A) s))
    (PCA.comp (PCA.sndComb A) s)
  refine ⟨fun z => p.toFun (g z), qq, fun b z hb => ?_⟩
  obtain ⟨w, hw, a, c, ha, hc, rfl⟩ := hs b z hb
  have hA : a ∈ PCA.app (PCA.comp (PCA.fstComb A) s) b := mem_comp hw (mem_fstComb a c)
  have hC : c ∈ PCA.app (PCA.comp (PCA.sndComb A) s) b := mem_comp hw (mem_sndComb a c)
  obtain ⟨a', ha', ha'p⟩ := hrp a (g z) ha
  exact ⟨PCA.pairEl a' c, hqq b a' c (mem_comp hA ha') hC, a', c, ha'p, hc, rfl⟩

theorem Cover.of_comp_right {h : E ⟶ F} {k : F ⟶ G} (hc : Cover (h ≫ k)) : Cover k := by
  obtain ⟨p, rfl⟩ := homOf_surjective h
  obtain ⟨q, rfl⟩ := homOf_surjective k
  rw [homOf_comp] at hc
  exact cover_homOf_iff.2 (cover_homOf_iff.1 hc).of_comp_right

/-- An isomorphism is a cover: its inverse is a section on the nose. -/
theorem cover_of_isIso (h : E ⟶ F) [IsIso h] : Cover h := by
  obtain ⟨p, rfl⟩ := homOf_surjective h
  obtain ⟨q, hq⟩ := homOf_surjective (inv (homOf p))
  refine cover_homOf_iff.2 ?_
  have hcomp : Homotopic (q.comp p) (Pre.id F) := by
    refine homOf_eq_iff.1 ?_
    have h₁ : homOf (q.comp p) = 𝟙 F := by rw [← homOf_comp, hq]; simp
    exact h₁.trans (id_eq F)
  obtain ⟨rq, hrq⟩ := q.trackedBase
  obtain ⟨t, ht⟩ := hcomp
  obtain ⟨qq, hqq⟩ := exists_pairOf rq t
  refine ⟨q.toFun, qq, fun b y hb => ?_⟩
  obtain ⟨a, ha, hay⟩ := hrq b y hb
  obtain ⟨c, hc, hcy⟩ := ht b y hb
  exact ⟨PCA.pairEl a c, hqq b a c ha hc, a, c, hay, hcy, rfl⟩

/-! ### The image factorization of a cover -/

/-- The first factor of the image factorization is a cover: it is the identity on points. -/
theorem coverPre_imgFacPre (p : Pre E F) : CoverPre (imgFacPre p) := by
  obtain ⟨rE, hrE⟩ := E.refl'
  obtain ⟨cf, hcf⟩ := p.tracked
  obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.i A) (PCA.comp cf rE)
  obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.i A) q₂
  obtain ⟨q₃, hq₃⟩ := exists_pairOf (PCA.i A) qq
  refine ⟨_root_.id, q₃, fun b x hb => ?_⟩
  obtain ⟨u, hu, hux⟩ := hrE b x hb
  obtain ⟨c, hc, hcx⟩ := hcf u x x hux
  have hi : b ∈ PCA.app (PCA.i A) b := by rw [PCA.i_app]; exact Part.mem_some _
  refine ⟨PCA.pairEl b (PCA.pairEl b (PCA.pairEl b c)),
    hq₃ b b _ hi (hqq b b _ hi (hq₂ b b c hi (mem_comp hu hc))), b, PCA.pairEl b (PCA.pairEl b c),
    hb, ⟨b, b, c, hb, hb, hcx, rfl⟩, rfl⟩

/-- The section of a cover, as a pre-morphism back from the target to the image. -/
noncomputable def invImgPre (p : Pre E F) (g : F.base.carrier → E.base.carrier) (s : A)
    (hs : IsSection p g s) : Pre F (imgObj p) where
  toFun := g
  tracked := by
    obtain ⟨tF1, htF1⟩ := F.exists_fstTracker
    obtain ⟨tF2, htF2⟩ := F.exists_sndTracker
    obtain ⟨sF, hsF⟩ := F.symm'
    obtain ⟨tF, htF⟩ := F.trans'
    obtain ⟨q₁, hq₁⟩ := exists_pairApply tF
      (PCA.comp (PCA.comp (PCA.sndComb A) s) tF1) (PCA.i A)
    obtain ⟨q₂, hq₂⟩ := exists_pairApply tF q₁
      (PCA.comp sF (PCA.comp (PCA.comp (PCA.sndComb A) s) tF2))
    obtain ⟨qi, hqi⟩ := exists_pairOf (PCA.comp (PCA.comp (PCA.fstComb A) s) tF2) q₂
    obtain ⟨qo, hqo⟩ := exists_pairOf (PCA.comp (PCA.comp (PCA.fstComb A) s) tF1) qi
    refine ⟨qo, fun w y y' hw => ?_⟩
    obtain ⟨b₁, hb₁, hb₁y⟩ := htF1 w y y' hw
    obtain ⟨b₂, hb₂, hb₂y⟩ := htF2 w y y' hw
    obtain ⟨w₁, hw₁, a₁, c₁, ha₁, hc₁, rfl⟩ := hs b₁ y hb₁y
    obtain ⟨w₂, hw₂, a₂, c₂, ha₂, hc₂, rfl⟩ := hs b₂ y' hb₂y
    have hA₁ : a₁ ∈ PCA.app (PCA.comp (PCA.comp (PCA.fstComb A) s) tF1) w :=
      mem_comp hb₁ (mem_comp hw₁ (mem_fstComb a₁ c₁))
    have hC₁ : c₁ ∈ PCA.app (PCA.comp (PCA.comp (PCA.sndComb A) s) tF1) w :=
      mem_comp hb₁ (mem_comp hw₁ (mem_sndComb a₁ c₁))
    have hA₂ : a₂ ∈ PCA.app (PCA.comp (PCA.comp (PCA.fstComb A) s) tF2) w :=
      mem_comp hb₂ (mem_comp hw₂ (mem_fstComb a₂ c₂))
    have hC₂ : c₂ ∈ PCA.app (PCA.comp (PCA.comp (PCA.sndComb A) s) tF2) w :=
      mem_comp hb₂ (mem_comp hw₂ (mem_sndComb a₂ c₂))
    obtain ⟨d, hd, hdp⟩ := htF c₁ w (p.toFun (g y)) y y' hc₁ hw
    obtain ⟨c₂', hc₂', hc₂'p⟩ := hsF c₂ (p.toFun (g y')) y' hc₂
    obtain ⟨e, he, hep⟩ := htF d c₂' (p.toFun (g y)) y' (p.toFun (g y')) hdp hc₂'p
    have hD : d ∈ PCA.app q₁ w := hq₁ w c₁ w d hC₁ (by rw [PCA.i_app]; exact Part.mem_some _) hd
    have hE : e ∈ PCA.app q₂ w := hq₂ w d c₂' e hD (mem_comp hC₂ hc₂') he
    exact ⟨PCA.pairEl a₁ (PCA.pairEl a₂ e), hqo w a₁ _ hA₁ (hqi w a₂ e hA₂ hE),
      a₁, a₂, e, ha₁, ha₂, hep, rfl⟩

@[simp] theorem invImgPre_toFun (p : Pre E F) (g : F.base.carrier → E.base.carrier) (s : A)
    (hs : IsSection p g s) : (invImgPre p g s hs).toFun = g := rfl

/-- **The second factor of the image factorization of a cover is an isomorphism.** -/
theorem isIso_imgIncl_of_cover {p : Pre E F} (hp : CoverPre p) : IsIso (imgIncl p) := by
  obtain ⟨g, s, hs⟩ := hp
  refine ⟨homOf (invImgPre p g s hs), ?_, ?_⟩
  · -- `imgIncl p ≫ inv = 𝟙`
    rw [imgIncl, homOf_comp, id_eq]
    refine homOf_eq_iff.2 ?_
    obtain ⟨rp, hrp⟩ := p.trackedBase
    obtain ⟨qi, hqi⟩ := exists_pairOf (PCA.i A) (PCA.comp (PCA.comp (PCA.sndComb A) s) rp)
    obtain ⟨qo, hqo⟩ := exists_pairOf (PCA.comp (PCA.comp (PCA.fstComb A) s) rp) qi
    refine ⟨qo, fun a x ha => ?_⟩
    obtain ⟨b, hb, hbx⟩ := hrp a x ha
    obtain ⟨w, hw, a₁, c₁, ha₁, hc₁, rfl⟩ := hs b (p.toFun x) hbx
    have hA₁ : a₁ ∈ PCA.app (PCA.comp (PCA.comp (PCA.fstComb A) s) rp) a :=
      mem_comp hb (mem_comp hw (mem_fstComb a₁ c₁))
    have hC₁ : c₁ ∈ PCA.app (PCA.comp (PCA.comp (PCA.sndComb A) s) rp) a :=
      mem_comp hb (mem_comp hw (mem_sndComb a₁ c₁))
    exact ⟨PCA.pairEl a₁ (PCA.pairEl a c₁),
      hqo a a₁ _ hA₁ (hqi a a c₁ (by rw [PCA.i_app]; exact Part.mem_some _) hC₁),
      a₁, a, c₁, ha₁, ha, hc₁, rfl⟩
  · -- `inv ≫ imgIncl p = 𝟙`
    rw [imgIncl, homOf_comp, id_eq]
    refine homOf_eq_iff.2 ⟨PCA.comp (PCA.sndComb A) s, fun b y hb => ?_⟩
    obtain ⟨w, hw, a₁, c₁, _, hc₁, rfl⟩ := hs b y hb
    exact ⟨c₁, mem_comp hw (mem_sndComb a₁ c₁), hc₁⟩

/-! ### Regular epimorphisms -/

/-- If a composite is a regular epimorphism and its first factor is an epimorphism, then its
second factor is a regular epimorphism: the coequalizer diagram transports. -/
noncomputable def regularEpiOfEpiComp {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Epi f] (h : RegularEpi (f ≫ g)) : RegularEpi g where
  W := h.W
  left := h.left ≫ f
  right := h.right ≫ f
  w := by rw [Category.assoc, Category.assoc, h.w]
  isColimit := by
    have hc : ∀ s : Cofork (h.left ≫ f) (h.right ≫ f),
        h.left ≫ (f ≫ Cofork.π s) = h.right ≫ (f ≫ Cofork.π s) := by
      intro s
      have hs := s.condition
      simp only [Category.assoc] at hs ⊢
      exact hs
    have key : ∀ s : Cofork (h.left ≫ f) (h.right ≫ f),
        (f ≫ g) ≫ h.isColimit.desc (Cofork.ofπ (f ≫ Cofork.π s) (hc s)) = f ≫ Cofork.π s := by
      intro s
      simpa using Cofork.IsColimit.π_desc (t := Cofork.ofπ (f ≫ Cofork.π s) (hc s)) h.isColimit
    refine Cofork.IsColimit.mk _
      (fun s => h.isColimit.desc (Cofork.ofπ (f ≫ Cofork.π s) (hc s))) (fun s => ?_)
      (fun s m hm => ?_)
    · simp only [Cofork.π_ofπ]
      refine (cancel_epi f).1 ?_
      rw [← Category.assoc]
      exact key s
    · simp only [Cofork.π_ofπ] at hm
      refine Cofork.IsColimit.hom_ext h.isColimit ?_
      simp only [Cofork.π_ofπ]
      rw [Category.assoc, hm, key s]

/-- The canonical cover of the image is the canonical cover of the source, followed by the first
factor of the image factorization. -/
theorem quot_comp_imgFac (p : Pre E F) : quot E ≫ imgFac p = quot (imgObj p) :=
  congrArg homOf (Pre.ext rfl)

/-- **The first factor of the image factorization is a regular epimorphism.** -/
noncomputable def regularEpi_imgFac (p : Pre E F) : RegularEpi (imgFac p) :=
  regularEpiOfEpiComp (quot E) (imgFac p) (by rw [quot_comp_imgFac]; exact regularEpi_quot _)

/-- **A cover is a regular epimorphism**: its image factorization has an invertible second
factor, and its first factor is regular. -/
theorem isRegularEpi_of_cover {h : E ⟶ F} (hc : Cover h) : IsRegularEpi h := by
  obtain ⟨p, rfl, hp⟩ := hc
  have : IsIso (imgIncl p) := isIso_imgIncl_of_cover hp
  refine isRegularEpi_of_regularEpi (RegularEpi.ofArrowIso ?_ (regularEpi_imgFac p))
  exact Arrow.isoMk (Iso.refl _) (asIso (imgIncl p)) (by simp [imgFac_comp_imgIncl p])

/-- **A regular epimorphism is a cover**: it is a strong epimorphism, so the monomorphism of its
image factorization is invertible. -/
theorem cover_of_isRegularEpi {h : E ⟶ F} (hr : IsRegularEpi h) : Cover h := by
  obtain ⟨p, rfl⟩ := homOf_surjective h
  have := hr
  have hse : StrongEpi (imgFac p ≫ imgIncl p) := by
    rw [imgFac_comp_imgIncl p]
    infer_instance
  have : StrongEpi (imgIncl p) := strongEpi_of_strongEpi (imgFac p) (imgIncl p)
  have : IsIso (imgIncl p) := isIso_of_mono_of_strongEpi _
  rw [← imgFac_comp_imgIncl p]
  exact (cover_homOf_iff.2 (coverPre_imgFacPre p)).comp (cover_of_isIso _)

/-- **The regular epimorphisms of the completion are exactly its covers.** -/
theorem cover_iff_isRegularEpi {h : E ⟶ F} : Cover h ↔ IsRegularEpi h :=
  ⟨isRegularEpi_of_cover, cover_of_isRegularEpi⟩

end ExReg

end Realizability
