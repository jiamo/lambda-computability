/-
**The assemblies are a regular category.**

`Start/AssemblyImage.lean` factors every morphism of assemblies as a strong epimorphism followed
by a monomorphism.  This module identifies the strong epimorphisms computationally and shows they
are stable under pullback, which together with the finite limits of `Start/AssemblyLimits.lean`
is exactly regularity of `Asm(A)`.

A morphism **lifts realizers** when a single element of the algebra turns a realizer of a point of
the codomain into a realizer of one of its preimages.  Such a morphism is in particular surjective
— every point has a realizer — and the two conditions are equivalent:

* if `f` lifts realizers, the lifting combinator tracks a section of the second factor of the
  image factorization, so that factor is an isomorphism and `f` is the first factor up to
  isomorphism, hence a strong epimorphism;
* conversely, a strong epimorphism lifts against the monomorphism `imageIncl f`, and the tracker
  of the resulting diagonal is a lifting combinator.

Pullbacks are then computed explicitly, as the sub-assembly of the product where the two maps
agree, and the lifting combinator of the base map is transported: from a realizer `c` of a point
`z` of the base, apply the tracker of `g` to reach a realizer of `g z`, lift it to a realizer of a
preimage `x`, and pair it with `c` to realize `(x, z)`.

Main results:

* `Realizability.Assembly.strongEpi_iff_liftsRealizers` — **the strong epimorphisms of `Asm(A)`
  are exactly the morphisms that lift realizers**;
* `Realizability.Assembly.isPullback_pbAsm` — the explicit pullback of two morphisms;
* `Realizability.Assembly.strongEpi_of_isPullback` — **strong epimorphisms are stable under
  pullback**, so `Asm(A)` is a regular category.
-/

import Start.AssemblyImage

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A] {X Y Z : Assembly.{u, v} A}

/-! ### Lifting realizers -/

/-- A morphism **lifts realizers** when a single element of the algebra turns a realizer of a
point of the codomain into a realizer of one of its preimages. -/
def LiftsRealizers (f : X ⟶ Y) : Prop :=
  ∃ r : A, ∀ (a : A) (y : Y.carrier), Y.realizes a y →
    ∃ v ∈ PCA.app r a, ∃ x, f.toFun x = y ∧ X.realizes v x

theorem LiftsRealizers.surjective {f : X ⟶ Y} (h : LiftsRealizers f) :
    Function.Surjective f.toFun := by
  obtain ⟨r, hr⟩ := h
  intro y
  obtain ⟨a, ha⟩ := Y.exists_realizer y
  obtain ⟨_, _, x, hx, _⟩ := hr a y ha
  exact ⟨x, hx⟩

/-- A morphism that lifts realizers has an invertible second factor: the image of `f` is `Y`,
with the same realizability relation up to a combinator. -/
noncomputable def imageInclInv {f : X ⟶ Y} (h : LiftsRealizers f) : Y ⟶ imageAsm f where
  toFun y := ⟨y, h.surjective y⟩
  tracked := by
    obtain ⟨r, hr⟩ := h
    refine ⟨r, fun a y ha => ?_⟩
    obtain ⟨v, hv, x, hx, hvx⟩ := hr a y ha
    exact ⟨v, hv, x, hx, hvx⟩

theorem isIso_imageIncl_of_liftsRealizers {f : X ⟶ Y} (h : LiftsRealizers f) :
    IsIso (imageIncl f) :=
  ⟨imageInclInv h, hom_ext fun _ => Subtype.ext rfl, hom_ext fun _ => rfl⟩

/-- A morphism that lifts realizers is a strong epimorphism. -/
theorem strongEpi_of_liftsRealizers {f : X ⟶ Y} (h : LiftsRealizers f) : StrongEpi f := by
  have : IsIso (imageIncl f) := isIso_imageIncl_of_liftsRealizers h
  have hcomp : StrongEpi (imageFactor f ≫ imageIncl f) := inferInstance
  rwa [imageFactor_comp_imageIncl] at hcomp

/-- A strong epimorphism lifts realizers. -/
theorem liftsRealizers_of_strongEpi (f : X ⟶ Y) [StrongEpi f] : LiftsRealizers f := by
  have sq : CommSq (imageFactor f) f (imageIncl f) (𝟙 Y) :=
    ⟨by rw [Category.comp_id, imageFactor_comp_imageIncl]⟩
  obtain ⟨r, hr⟩ := sq.lift.tracked
  refine ⟨r, fun a y ha => ?_⟩
  obtain ⟨v, hv, x, hx, hvx⟩ := hr a y ha
  refine ⟨v, hv, x, ?_, hvx⟩
  rw [hx]
  exact congrArg (fun k : Y ⟶ Y => k.toFun y) sq.fac_right

/-- **The strong epimorphisms of `Asm(A)` are exactly the morphisms that lift realizers.** -/
theorem strongEpi_iff_liftsRealizers (f : X ⟶ Y) : StrongEpi f ↔ LiftsRealizers f :=
  ⟨fun _ => liftsRealizers_of_strongEpi f, strongEpi_of_liftsRealizers⟩

/-! ### Explicit pullbacks -/

/-- The pullback of two morphisms of assemblies: the sub-assembly of the product on which they
agree. -/
def pbAsm (f : X ⟶ Y) (g : Z ⟶ Y) : Assembly.{u, v} A :=
  subAsm (prodAsm X Z) fun p => f.toFun p.1 = g.toFun p.2

/-- The first projection of the explicit pullback. -/
noncomputable def pbFst (f : X ⟶ Y) (g : Z ⟶ Y) : pbAsm f g ⟶ X :=
  subIncl _ _ ≫ prodFst X Z

/-- The second projection of the explicit pullback. -/
noncomputable def pbSnd (f : X ⟶ Y) (g : Z ⟶ Y) : pbAsm f g ⟶ Z :=
  subIncl _ _ ≫ prodSnd X Z

@[simp] theorem pbFst_toFun (f : X ⟶ Y) (g : Z ⟶ Y) (p : (pbAsm f g).carrier) :
    (pbFst f g).toFun p = p.1.1 := rfl

@[simp] theorem pbSnd_toFun (f : X ⟶ Y) (g : Z ⟶ Y) (p : (pbAsm f g).carrier) :
    (pbSnd f g).toFun p = p.1.2 := rfl

theorem pb_condition (f : X ⟶ Y) (g : Z ⟶ Y) : pbFst f g ≫ f = pbSnd f g ≫ g :=
  hom_ext fun p => p.2

/-- The explicit pullback really is a pullback. -/
noncomputable def pbIsLimit (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLimit (PullbackCone.mk (pbFst f g) (pbSnd f g) (pb_condition f g)) :=
  PullbackCone.IsLimit.mk _
    (fun s => subLift (prodLift s.fst s.snd)
      fun z => congrArg (fun k : s.pt ⟶ Y => k.toFun z) s.condition)
    (fun _ => hom_ext fun _ => rfl) (fun _ => hom_ext fun _ => rfl)
    (fun s _ h₁ h₂ => hom_ext fun z => Subtype.ext (Prod.ext
      (congrArg (fun k : s.pt ⟶ X => k.toFun z) h₁)
      (congrArg (fun k : s.pt ⟶ Z => k.toFun z) h₂)))

theorem isPullback_pbAsm (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsPullback (pbFst f g) (pbSnd f g) f g :=
  ⟨⟨pb_condition f g⟩, ⟨pbIsLimit f g⟩⟩

/-! ### Strong epimorphisms are stable under pullback -/

/-- The combinator `λc. pair (s c) c`. -/
theorem exists_pairWith (s : A) : ∃ q : A, ∀ c v : A, v ∈ PCA.app s c →
    PCA.pairEl v c ∈ PCA.app q c := by
  refine ⟨PCA.lam 0 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
    (Expr.app (Expr.const s) (Expr.var 0))) (Expr.var 0)) (PCA.env0 A), fun c v hv => ?_⟩
  have hle := PCA.lam_app 0 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
    (Expr.app (Expr.const s) (Expr.var 0))) (Expr.var 0)) (PCA.env0 A) c
  refine hle _ ?_
  have hmono : (Part.some (PCA.pairComb A) ⬝ Part.some v) ⬝ Part.some c
      ≤ (Part.some (PCA.pairComb A) ⬝ (Part.some s ⬝ Part.some c)) ⬝ Part.some c := by
    refine papp_mono (papp_mono le_rfl ?_) le_rfl
    rw [papp_some_some]
    exact fun _ h => by rwa [Part.mem_some_iff.1 h]
  have hmem : PCA.pairEl v c ∈ (Part.some (PCA.pairComb A) ⬝ (Part.some s ⬝ Part.some c))
      ⬝ Part.some c := by
    refine hmono _ ?_
    rw [PCA.pairComb_app]
    exact Part.mem_some _
  simpa [Expr.eval] using hmem

/-- **The pullback of a strong epimorphism is a strong epimorphism**, for the explicit
pullback. -/
theorem liftsRealizers_pbSnd {f : X ⟶ Y} (g : Z ⟶ Y) (h : LiftsRealizers f) :
    LiftsRealizers (pbSnd f g) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨t, ht⟩ := g.tracked
  obtain ⟨q, hq⟩ := exists_pairWith (PCA.comp r t)
  refine ⟨q, fun c z hc => ?_⟩
  obtain ⟨b, hb, hbz⟩ := ht c z hc
  obtain ⟨w, hw, x, hx, hwx⟩ := hr b (g.toFun z) hbz
  have hmem0 : w ∈ Part.some r ⬝ (Part.some t ⬝ Part.some c) := by
    rw [papp_some_some, papp_some_left]
    exact Part.mem_bind_iff.2 ⟨b, hb, hw⟩
  have hmem : w ∈ PCA.app (PCA.comp r t) c := by
    have hc := PCA.comp_app r t c w hmem0
    rwa [papp_some_some] at hc
  exact ⟨PCA.pairEl w c, hq c w hmem, ⟨(x, z), hx⟩, rfl, w, c, hwx, hc, rfl⟩

instance strongEpi_pbSnd (f : X ⟶ Y) (g : Z ⟶ Y) [StrongEpi f] : StrongEpi (pbSnd f g) :=
  strongEpi_of_liftsRealizers (liftsRealizers_pbSnd g (liftsRealizers_of_strongEpi f))

/-- **Strong epimorphisms of assemblies are stable under pullback**: with the finite limits and
the image factorizations, this says that `Asm(A)` is a regular category. -/
theorem strongEpi_of_isPullback {P : Assembly.{u, v} A} {fst : P ⟶ X} {snd : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y} (h : IsPullback fst snd f g) [StrongEpi f] : StrongEpi snd := by
  have he : (h.isoIsPullback _ _ (isPullback_pbAsm f g)).hom ≫ pbSnd f g = snd :=
    h.isoIsPullback_hom_snd _ _ (isPullback_pbAsm f g)
  rw [← he]
  infer_instance

end Assembly

end Realizability
