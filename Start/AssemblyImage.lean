/-
**Images in the category of assemblies.**

A morphism of assemblies is a monomorphism exactly when it is injective and an epimorphism
exactly when it is surjective — the second direction uses the assembly of propositions of
`Start/AssemblySubobject.lean`, which has no computational content, so the characteristic map of
the set-theoretic image is always a morphism.

Every morphism `f : X ⟶ Y` factors through its **image**: the set-theoretic image of `f`, with
`a` realizing `y` when `a` realizes *some* element of the fibre of `y`.  Note that this is not the
sub-assembly of `Y` on the image: an element of the image is realized by the realizers of its
preimages, not by all the realizers it happens to have in `Y`.  With that structure the first
factor is the identity on realizers, and it is a **strong** epimorphism: in a commuting square
against a monomorphism the diagonal filler is computed by the tracker of the top map, because a
realizer of a point of the image is a realizer of one of its preimages.  So the assemblies have
strong epi-mono factorizations, hence images in mathlib's sense.

Main results:

* `Realizability.Assembly.mono_iff_injective`, `.epi_iff_surjective` — the monomorphisms are the
  injections and the epimorphisms are the surjections;
* `Realizability.Assembly.imageAsm`, `.imageFactor`, `.imageIncl` — the image factorization;
* `Realizability.Assembly.strongEpi_imageFactor` — **the first factor is a strong epimorphism**;
* `Realizability.Assembly.instHasStrongEpiMonoFactorisations`,
  `Realizability.Assembly.instHasImages` — **the assemblies have images**.
-/

import Start.AssemblySubobject
import Mathlib.CategoryTheory.Limits.Shapes.Images

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A] {X Y : Assembly.{u, v} A}

/-! ### Monomorphisms and epimorphisms -/

theorem mono_of_injective {f : X ⟶ Y} (hf : Function.Injective f.toFun) : Mono f where
  right_cancellation _ _ h := hom_ext fun z => hf (congrArg (fun k => k.toFun z) h)

theorem injective_of_mono (f : X ⟶ Y) [Mono f] : Function.Injective f.toFun := by
  intro x x' hx
  have h : pointMap X x ≫ f = pointMap X x' ≫ f := hom_ext fun _ => hx
  exact congrArg (fun k : unitAsm A ⟶ X => k.toFun PUnit.unit) ((cancel_mono f).1 h)

/-- **A morphism of assemblies is a monomorphism exactly when it is injective.** -/
theorem mono_iff_injective (f : X ⟶ Y) : Mono f ↔ Function.Injective f.toFun :=
  ⟨fun _ => injective_of_mono f, mono_of_injective⟩

theorem epi_of_surjective {f : X ⟶ Y} (hf : Function.Surjective f.toFun) : Epi f where
  left_cancellation _ _ h := hom_ext fun y => by
    obtain ⟨x, rfl⟩ := hf y
    exact congrArg (fun k => k.toFun x) h

theorem surjective_of_epi (f : X ⟶ Y) [Epi f] : Function.Surjective f.toFun := by
  have h : charMap Y (fun y => ∃ x, f.toFun x = y) = charMap Y fun _ => True := by
    refine (cancel_epi f).1 (hom_ext fun x => ?_)
    simp only [comp_toFun, Function.comp_apply, charMap_toFun]
    exact congrArg ULift.up (propext ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩)
  intro y
  have hy : (∃ x, f.toFun x = y) = True :=
    congrArg (fun k : Y ⟶ propAsm A => (k.toFun y).down) h
  exact (iff_of_eq hy).mpr trivial

/-- **A morphism of assemblies is an epimorphism exactly when it is surjective.** -/
theorem epi_iff_surjective (f : X ⟶ Y) : Epi f ↔ Function.Surjective f.toFun :=
  ⟨fun _ => surjective_of_epi f, epi_of_surjective⟩

/-! ### The image of a morphism -/

/-- The **image** of a morphism of assemblies: the set-theoretic image, where `a` realizes a point
when it realizes one of its preimages. -/
def imageAsm (f : X ⟶ Y) : Assembly.{u, v} A where
  carrier := { y : Y.carrier // ∃ x, f.toFun x = y }
  realizes a y := ∃ x, f.toFun x = y.1 ∧ X.realizes a x
  exists_realizer y := by
    obtain ⟨x, hx⟩ := y.2
    obtain ⟨a, ha⟩ := X.exists_realizer x
    exact ⟨a, x, hx, ha⟩

/-- The first factor of the image factorization, the identity on realizers. -/
noncomputable def imageFactor (f : X ⟶ Y) : X ⟶ imageAsm f where
  toFun x := ⟨f.toFun x, x, rfl⟩
  tracked := ⟨PCA.i A, fun a x hx =>
    ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, x, rfl, hx⟩⟩

@[simp] theorem imageFactor_toFun (f : X ⟶ Y) (x : X.carrier) :
    (imageFactor f).toFun x = ⟨f.toFun x, x, rfl⟩ := rfl

/-- The second factor of the image factorization, tracked by any tracker of `f`. -/
noncomputable def imageIncl (f : X ⟶ Y) : imageAsm f ⟶ Y where
  toFun y := y.1
  tracked := by
    obtain ⟨r, hr⟩ := f.tracked
    refine ⟨r, fun a y ha => ?_⟩
    obtain ⟨x, hx, hax⟩ := ha
    obtain ⟨w, hw, hwx⟩ := hr a x hax
    refine ⟨w, hw, ?_⟩
    change Y.realizes w y.1
    rw [← hx]
    exact hwx

@[simp] theorem imageIncl_toFun (f : X ⟶ Y) (y : (imageAsm f).carrier) :
    (imageIncl f).toFun y = y.1 := rfl

theorem imageFactor_comp_imageIncl (f : X ⟶ Y) : imageFactor f ≫ imageIncl f = f :=
  hom_ext fun _ => rfl

theorem surjective_imageFactor (f : X ⟶ Y) : Function.Surjective (imageFactor f).toFun := by
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

instance epi_imageFactor (f : X ⟶ Y) : Epi (imageFactor f) :=
  epi_of_surjective (surjective_imageFactor f)

instance mono_imageIncl (f : X ⟶ Y) : Mono (imageIncl f) :=
  mono_of_injective fun _ _ h => Subtype.ext h

/-! ### The image factorization is a strong epi-mono factorization -/

section Diagonal

variable {P Q : Assembly.{u, v} A} (f : X ⟶ Y) (u : X ⟶ P) (v : imageAsm f ⟶ Q) (z : P ⟶ Q)

/-- In a square from the first factor of an image factorization to a monomorphism, the top map
sends any preimage of a point of the image to a lift of the value of the bottom map there. -/
theorem imageDiagonal_key (hsq : u ≫ z = imageFactor f ≫ v) (w : X.carrier)
    (y : (imageAsm f).carrier) (hw : f.toFun w = y.1) : z.toFun (u.toFun w) = v.toFun y := by
  have h₁ := congrArg (fun k : X ⟶ Q => k.toFun w) hsq
  simp only [comp_toFun, Function.comp_apply, imageFactor_toFun] at h₁
  rw [h₁]
  exact congrArg v.toFun (Subtype.ext hw)

/-- The diagonal filler of a square from the first factor of an image factorization to a
monomorphism: a point of the image is sent to the value of the top map at any of its preimages,
which is well defined because the right-hand map is injective. -/
noncomputable def imageDiagonal (hz : Function.Injective z.toFun)
    (hsq : u ≫ z = imageFactor f ≫ v) : imageAsm f ⟶ P where
  toFun y := u.toFun y.2.choose
  tracked := by
    obtain ⟨t, ht⟩ := u.tracked
    refine ⟨t, fun a y ha => ?_⟩
    obtain ⟨x, hx, hax⟩ := ha
    obtain ⟨w, hw, hwx⟩ := ht a x hax
    refine ⟨w, hw, ?_⟩
    have hval : u.toFun x = u.toFun y.2.choose :=
      hz ((imageDiagonal_key f u v z hsq x y hx).trans
        (imageDiagonal_key f u v z hsq y.2.choose y y.2.choose_spec).symm)
    rwa [hval] at hwx

theorem imageDiagonal_comp (hz : Function.Injective z.toFun)
    (hsq : u ≫ z = imageFactor f ≫ v) : imageDiagonal f u v z hz hsq ≫ z = v :=
  hom_ext fun y => imageDiagonal_key f u v z hsq y.2.choose y y.2.choose_spec

theorem imageFactor_comp_imageDiagonal (hz : Function.Injective z.toFun)
    (hsq : u ≫ z = imageFactor f ≫ v) : imageFactor f ≫ imageDiagonal f u v z hz hsq = u :=
  hom_ext fun x => hz
    ((imageDiagonal_key f u v z hsq ((imageFactor f).toFun x).2.choose ((imageFactor f).toFun x)
        ((imageFactor f).toFun x).2.choose_spec).trans
      (imageDiagonal_key f u v z hsq x ((imageFactor f).toFun x) rfl).symm)

end Diagonal

instance hasLiftingProperty_imageFactor (f : X ⟶ Y) {P Q : Assembly.{u, v} A} (z : P ⟶ Q)
    [Mono z] : HasLiftingProperty (imageFactor f) z where
  sq_hasLift {u v} sq :=
    ⟨⟨⟨imageDiagonal f u v z (injective_of_mono z) sq.w,
      imageFactor_comp_imageDiagonal f u v z (injective_of_mono z) sq.w,
      imageDiagonal_comp f u v z (injective_of_mono z) sq.w⟩⟩⟩

/-- **The first factor of the image factorization is a strong epimorphism.** -/
instance strongEpi_imageFactor (f : X ⟶ Y) : StrongEpi (imageFactor f) where
  epi := inferInstance
  llp {_ _} z _ := hasLiftingProperty_imageFactor f z

/-- The image factorization of a morphism of assemblies, as a strong epi-mono factorization. -/
noncomputable def imageFactorisation (f : X ⟶ Y) : StrongEpiMonoFactorisation f where
  I := imageAsm f
  m := imageIncl f
  e := imageFactor f
  fac := imageFactor_comp_imageIncl f

/-- **The assemblies have strong epi-mono factorizations.** -/
instance instHasStrongEpiMonoFactorisations :
    HasStrongEpiMonoFactorisations (Assembly.{u, v} A) :=
  ⟨fun f => ⟨imageFactorisation f⟩⟩

/-- **The assemblies have images.** -/
instance instHasImages : HasImages (Assembly.{u, v} A) := inferInstance

end Assembly

end Realizability
