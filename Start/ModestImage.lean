/-
**Images and regularity for the modest assemblies.**

`Start/AssemblyImage.lean` and `Start/AssemblyRegular.lean` make `Asm(A)` a regular category: every
morphism factors as a strong epimorphism followed by a monomorphism, the strong epimorphisms are
the morphisms that lift realizers, and they are stable under pullback.  All of that restricts to
the full subcategory of the modest assemblies, because **the image of a modest assembly is
modest**: a realizer of a point of the image realizes a preimage of it, and modesty of the domain
determines that preimage, hence the point.

The subcategory is full, so a commuting square in it is a commuting square in `Asm(A)` and the
diagonal filler built there is again a morphism of modest assemblies; the same remark identifies
the monomorphisms with the injections.  Pullbacks are computed as in `Asm(A)`, the sub-assembly of
the product on which the two morphisms agree being modest.

Main results:

* `Realizability.Assembly.Modest.image` — **the image of a modest assembly is modest**;
* `Realizability.Modest.instHasImages` — **the modest assemblies have images**, computed as in
  `Asm(A)`;
* `Realizability.Modest.strongEpi_iff_liftsRealizers` — the strong epimorphisms of the
  subcategory are again the morphisms that lift realizers;
* `Realizability.Modest.strongEpi_of_isPullback` — **the modest assemblies are a regular
  category**.
-/

import Start.AssemblyRegular
import Start.ModestColimits

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Realizability

variable {A : Type u} [PCA A]

namespace Assembly

/-- **The image of a modest assembly is modest**: a realizer of a point of the image realizes one
of its preimages, and modesty of the domain determines that preimage. -/
theorem Modest.image {X Y : Assembly.{u, u} A} (hX : X.Modest) (f : X ⟶ Y) :
    (imageAsm f).Modest := by
  rintro a y y' ⟨x₁, h₁, ha₁⟩ ⟨x₂, h₂, ha₂⟩
  exact Subtype.ext (by rw [← h₁, ← h₂, hX a x₁ x₂ ha₁ ha₂])

/-- The pullback of two morphisms of modest assemblies is modest. -/
theorem Modest.pb {X Y Z : Assembly.{u, u} A} (hX : X.Modest) (hZ : Z.Modest) (f : X ⟶ Y)
    (g : Z ⟶ Y) : (pbAsm f g).Modest :=
  Modest.sub (Modest.prod hX hZ) _

end Assembly

namespace Modest

open Assembly

variable {X Y : ModestCat A}

/-! ### Monomorphisms and epimorphisms of modest assemblies -/

/-- A monomorphism of modest assemblies is injective: it separates the global elements. -/
theorem injective_of_mono (f : X ⟶ Y) [Mono f] : Function.Injective f.hom.toFun := by
  intro x x' hx
  have h : (ObjectProperty.homMk (pointMap X.obj x) : unitModest A ⟶ X) ≫ f
      = ObjectProperty.homMk (pointMap X.obj x') ≫ f :=
    ObjectProperty.hom_ext _ (hom_ext fun _ => hx)
  exact congrArg (fun k : unitModest A ⟶ X => k.hom.toFun PUnit.unit) ((cancel_mono f).1 h)

/-! ### The image factorization -/

/-- The image of a morphism of modest assemblies. -/
def imageModest (f : X ⟶ Y) : ModestCat A :=
  ⟨imageAsm f.hom, Assembly.Modest.image X.2 f.hom⟩

/-- The first factor of the image factorization in the subcategory. -/
noncomputable def imageFactorModest (f : X ⟶ Y) : X ⟶ imageModest f :=
  ObjectProperty.homMk (imageFactor f.hom)

/-- The second factor of the image factorization in the subcategory. -/
noncomputable def imageInclModest (f : X ⟶ Y) : imageModest f ⟶ Y :=
  ObjectProperty.homMk (imageIncl f.hom)

theorem imageFactorModest_comp (f : X ⟶ Y) :
    imageFactorModest f ≫ imageInclModest f = f :=
  ObjectProperty.hom_ext _ (imageFactor_comp_imageIncl f.hom)

instance mono_imageInclModest (f : X ⟶ Y) : Mono (imageInclModest f) where
  right_cancellation _ _ h := ObjectProperty.hom_ext _ (hom_ext fun z =>
    Subtype.ext (congrArg (fun k => k.hom.toFun z) h))

instance epi_imageFactorModest (f : X ⟶ Y) : Epi (imageFactorModest f) where
  left_cancellation _ _ h := ObjectProperty.hom_ext _ (hom_ext fun y => by
    obtain ⟨x, rfl⟩ := surjective_imageFactor f.hom y
    exact congrArg (fun k => k.hom.toFun x) h)

instance hasLiftingProperty_imageFactorModest (f : X ⟶ Y) {P Q : ModestCat A} (z : P ⟶ Q)
    [Mono z] : HasLiftingProperty (imageFactorModest f) z where
  sq_hasLift {u v} sq :=
    ⟨⟨⟨ObjectProperty.homMk (imageDiagonal f.hom u.hom v.hom z.hom (injective_of_mono z)
          (congrArg (fun k : X ⟶ Q => k.hom) sq.w)),
      ObjectProperty.hom_ext _ (imageFactor_comp_imageDiagonal f.hom u.hom v.hom z.hom
        (injective_of_mono z) (congrArg (fun k : X ⟶ Q => k.hom) sq.w)),
      ObjectProperty.hom_ext _ (imageDiagonal_comp f.hom u.hom v.hom z.hom
        (injective_of_mono z) (congrArg (fun k : X ⟶ Q => k.hom) sq.w))⟩⟩⟩

/-- The first factor of the image factorization of modest assemblies is a strong epimorphism. -/
instance strongEpi_imageFactorModest (f : X ⟶ Y) : StrongEpi (imageFactorModest f) where
  epi := inferInstance
  llp {_ _} z _ := hasLiftingProperty_imageFactorModest f z

/-- The image factorization of a morphism of modest assemblies. -/
noncomputable def imageFactorisationModest (f : X ⟶ Y) : StrongEpiMonoFactorisation f where
  I := imageModest f
  m := imageInclModest f
  e := imageFactorModest f
  fac := imageFactorModest_comp f

/-- **The modest assemblies have strong epi-mono factorizations.** -/
instance instHasStrongEpiMonoFactorisations :
    HasStrongEpiMonoFactorisations (ModestCat A) :=
  ⟨fun f => ⟨imageFactorisationModest f⟩⟩

/-- **The modest assemblies have images.** -/
instance instHasImages : HasImages (ModestCat A) := inferInstance

/-! ### The modest assemblies are regular -/

/-- A morphism of modest assemblies that lifts realizers is a strong epimorphism: the second
factor of its image factorization is invertible. -/
theorem strongEpi_of_liftsRealizers {f : X ⟶ Y} (h : LiftsRealizers f.hom) : StrongEpi f := by
  have hiso : IsIso (imageInclModest f) :=
    ⟨ObjectProperty.homMk (imageInclInv h),
      ObjectProperty.hom_ext _ (hom_ext fun _ => Subtype.ext rfl),
      ObjectProperty.hom_ext _ (hom_ext fun _ => rfl)⟩
  have hcomp : StrongEpi (imageFactorModest f ≫ imageInclModest f) := inferInstance
  rwa [imageFactorModest_comp] at hcomp

/-- A strong epimorphism of modest assemblies lifts realizers. -/
theorem liftsRealizers_of_strongEpi (f : X ⟶ Y) [StrongEpi f] : LiftsRealizers f.hom := by
  have sq : CommSq (imageFactorModest f) f (imageInclModest f) (𝟙 Y) :=
    ⟨by rw [Category.comp_id, imageFactorModest_comp]⟩
  obtain ⟨r, hr⟩ := sq.lift.hom.tracked
  refine ⟨r, fun a y ha => ?_⟩
  obtain ⟨v, hv, x, hx, hvx⟩ := hr a y ha
  refine ⟨v, hv, x, ?_, hvx⟩
  rw [hx]
  exact congrArg (fun k : Y ⟶ Y => k.hom.toFun y) sq.fac_right

/-- **The strong epimorphisms of the modest assemblies are again the morphisms that lift
realizers.** -/
theorem strongEpi_iff_liftsRealizers (f : X ⟶ Y) : StrongEpi f ↔ LiftsRealizers f.hom :=
  ⟨fun _ => liftsRealizers_of_strongEpi f, strongEpi_of_liftsRealizers⟩

variable {Z : ModestCat A}

/-- The explicit pullback of two morphisms of modest assemblies. -/
def pbModest (f : X ⟶ Y) (g : Z ⟶ Y) : ModestCat A :=
  ⟨pbAsm f.hom g.hom, Assembly.Modest.pb X.2 Z.2 f.hom g.hom⟩

/-- The first projection of the explicit pullback of modest assemblies. -/
noncomputable def pbFstModest (f : X ⟶ Y) (g : Z ⟶ Y) : pbModest f g ⟶ X :=
  ObjectProperty.homMk (pbFst f.hom g.hom)

/-- The second projection of the explicit pullback of modest assemblies. -/
noncomputable def pbSndModest (f : X ⟶ Y) (g : Z ⟶ Y) : pbModest f g ⟶ Z :=
  ObjectProperty.homMk (pbSnd f.hom g.hom)

theorem pbModest_condition (f : X ⟶ Y) (g : Z ⟶ Y) :
    pbFstModest f g ≫ f = pbSndModest f g ≫ g :=
  ObjectProperty.hom_ext _ (pb_condition f.hom g.hom)

/-- The explicit pullback of modest assemblies really is a pullback in the subcategory. -/
noncomputable def pbModestIsLimit (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLimit (PullbackCone.mk (pbFstModest f g) (pbSndModest f g) (pbModest_condition f g)) :=
  PullbackCone.IsLimit.mk _
    (fun s => ObjectProperty.homMk (subLift (prodLift s.fst.hom s.snd.hom)
      fun z => congrArg (fun k : s.pt ⟶ Y => k.hom.toFun z) s.condition))
    (fun _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))
    (fun _ => ObjectProperty.hom_ext _ (hom_ext fun _ => rfl))
    (fun s _ h₁ h₂ => ObjectProperty.hom_ext _ (hom_ext fun z => Subtype.ext (Prod.ext
      (congrArg (fun k : s.pt ⟶ X => k.hom.toFun z) h₁)
      (congrArg (fun k : s.pt ⟶ Z => k.hom.toFun z) h₂))))

theorem isPullback_pbModest (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsPullback (pbFstModest f g) (pbSndModest f g) f g :=
  ⟨⟨pbModest_condition f g⟩, ⟨pbModestIsLimit f g⟩⟩

instance strongEpi_pbSndModest (f : X ⟶ Y) (g : Z ⟶ Y) [StrongEpi f] :
    StrongEpi (pbSndModest f g) :=
  strongEpi_of_liftsRealizers (liftsRealizers_pbSnd g.hom (liftsRealizers_of_strongEpi f))

/-- **Strong epimorphisms of modest assemblies are stable under pullback**: with the finite limits
and the image factorizations, the modest assemblies are a regular category. -/
theorem strongEpi_of_isPullback {P : ModestCat A} {fst : P ⟶ X} {snd : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y} (h : IsPullback fst snd f g) [StrongEpi f] : StrongEpi snd := by
  have he : (h.isoIsPullback _ _ (isPullback_pbModest f g)).hom ≫ pbSndModest f g = snd :=
    h.isoIsPullback_hom_snd _ _ (isPullback_pbModest f g)
  rw [← he]
  infer_instance

end Modest

end Realizability
