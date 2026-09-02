/-
Finite colimits in the category of assemblies.

`Start/Assembly.lean` and `Start/AssemblyLimits.lean` build the finite *limits* of `Asm(A)`: the
terminal assembly, binary products realized by Church pairs, and equalizers carved out as
sub-assemblies.  This file builds the finite *colimits*.

* the initial assembly is empty, and there is nothing to realize;
* the coproduct of two assemblies is the disjoint union, a realizer being a Church pair whose
  first component is the boolean tag `k` or `k i` saying which summand the element lies in, and
  whose second component realizes the element there — so the copairing of two tracked maps is
  tracked by the combinator that reads the tag, *selects* one of the two trackers (an ordinary
  element of the algebra, so no divergence can be caused by the branch not taken) and applies it
  to the payload;
* the coequalizer of two morphisms is the quotient of the codomain by the equivalence relation
  they generate, with the realizers inherited from the representatives; the projection is
  therefore tracked by the identity combinator, and a map out of the quotient is tracked by
  whatever tracked the map it descends from.

Main definitions:

* `Realizability.Assembly.emptyAsm`, `.isInitialEmptyAsm` — the initial assembly;
* `Realizability.Assembly.coprodAsm`, `.coprodInl`, `.coprodInr`, `.coprodDesc`,
  `.coprodCofanIsColimit` — binary coproducts;
* `Realizability.Assembly.coeqAsm`, `.coeqProj`, `.coeqCoforkIsColimit` — coequalizers.

Main results:

* `Realizability.Assembly.instHasFiniteCoproducts`;
* `Realizability.Assembly.instHasCoequalizers`;
* `Realizability.Assembly.instHasFiniteColimits` — **`Asm(A)` has all finite colimits**, hence in
  particular pushouts.
-/

import Start.AssemblyLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A]

/-! ### The initial assembly -/

/-- The initial assembly: no elements, hence nothing to realize. -/
def emptyAsm (A : Type u) [PCA A] : Assembly.{u, v} A where
  carrier := PEmpty
  realizes _ _ := True
  exists_realizer x := x.elim

/-- The unique morphism out of the initial assembly; it is tracked by anything. -/
noncomputable def fromEmpty (X : Assembly.{u, v} A) : emptyAsm A ⟶ X where
  toFun x := x.elim
  tracked := ⟨PCA.k, fun _ x _ => x.elim⟩

/-- The empty assembly is initial. -/
noncomputable def isInitialEmptyAsm : IsInitial (emptyAsm.{u, v} A) :=
  IsInitial.ofUniqueHom fromEmpty fun _ _ => hom_ext fun x => x.elim

instance : HasInitial (Assembly.{u, v} A) :=
  IsInitial.hasInitial isInitialEmptyAsm

/-! ### Binary coproducts -/

/-- The coproduct of two assemblies: the disjoint union, realized by a Church pair of a boolean
tag and a realizer of the element in its summand. -/
def coprodAsm (X Y : Assembly.{u, v} A) : Assembly.{u, v} A where
  carrier := X.carrier ⊕ Y.carrier
  realizes p z :=
    Sum.elim (fun x => ∃ a, X.realizes a x ∧ p = PCA.pairEl (PCA.k : A) a)
      (fun y => ∃ b, Y.realizes b y ∧ p = PCA.pairEl (PCA.kI A) b) z
  exists_realizer z := by
    cases z with
    | inl x =>
      obtain ⟨a, ha⟩ := X.exists_realizer x
      exact ⟨_, a, ha, rfl⟩
    | inr y =>
      obtain ⟨b, hb⟩ := Y.exists_realizer y
      exact ⟨_, b, hb, rfl⟩

/-- The combinator `λx. pair t x` tagging its argument with `t`. -/
noncomputable def tagComb (t : A) : A :=
  PCA.lam 0 (Expr.app (Expr.app (Expr.const (PCA.pairComb A)) (Expr.const t)) (Expr.var 0))
    (PCA.env0 A)

theorem tagComb_app (t a : A) : PCA.pairEl t a ∈ PCA.app (tagComb t) a := by
  have hle := PCA.lam_app 0 (Expr.app (Expr.app (Expr.const (PCA.pairComb A)) (Expr.const t))
    (Expr.var 0)) (PCA.env0 A) a
  refine hle _ ?_
  have h : PCA.pairEl t a ∈ (Part.some (PCA.pairComb A) ⬝ Part.some t) ⬝ Part.some a := by
    rw [PCA.pairComb_app]
    exact Part.mem_some _
  simpa [Expr.eval] using h

/-- The left injection, tracked by `λx. pair k x`. -/
noncomputable def coprodInl (X Y : Assembly.{u, v} A) : X ⟶ coprodAsm X Y where
  toFun := Sum.inl
  tracked := ⟨tagComb (PCA.k : A), fun a _ hx =>
    ⟨PCA.pairEl (PCA.k : A) a, tagComb_app _ a, a, hx, rfl⟩⟩

/-- The right injection, tracked by `λy. pair (k i) y`. -/
noncomputable def coprodInr (X Y : Assembly.{u, v} A) : Y ⟶ coprodAsm X Y where
  toFun := Sum.inr
  tracked := ⟨tagComb (PCA.kI A), fun b _ hy =>
    ⟨PCA.pairEl (PCA.kI A) b, tagComb_app _ b, b, hy, rfl⟩⟩

@[simp] theorem coprodInl_toFun (X Y : Assembly.{u, v} A) :
    (coprodInl X Y).toFun = Sum.inl := rfl

@[simp] theorem coprodInr_toFun (X Y : Assembly.{u, v} A) :
    (coprodInr X Y).toFun = Sum.inr := rfl

/-- The body of the copairing combinator: read the tag of the argument, use it to select one of
the two trackers, and apply the selected tracker to the payload. -/
noncomputable def descBody (r t : A) : Expr A :=
  Expr.app
    (Expr.app (Expr.app (Expr.app (Expr.const (PCA.fstComb A)) (Expr.var 0)) (Expr.const r))
      (Expr.const t))
    (Expr.app (Expr.const (PCA.sndComb A)) (Expr.var 0))

/-- The copairing of two morphisms out of a coproduct. -/
noncomputable def coprodDesc {X Y Z : Assembly.{u, v} A} (f : X ⟶ Z) (g : Y ⟶ Z) :
    coprodAsm X Y ⟶ Z where
  toFun := Sum.elim f.toFun g.toFun
  tracked := by
    obtain ⟨r, hr⟩ := f.tracked
    obtain ⟨t, ht⟩ := g.tracked
    refine ⟨PCA.lam 0 (descBody r t) (PCA.env0 A), fun p z hz => ?_⟩
    cases z with
    | inl x =>
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨w, hw, hwx⟩ := hr a x ha
      refine ⟨w, ?_, hwx⟩
      refine PCA.lam_app 0 (descBody r t) (PCA.env0 A) _ _ ?_
      have hmem : w ∈
          (((Part.some (PCA.fstComb A) ⬝ Part.some (PCA.pairEl (PCA.k : A) a)) ⬝ Part.some r)
            ⬝ Part.some t)
            ⬝ (Part.some (PCA.sndComb A) ⬝ Part.some (PCA.pairEl (PCA.k : A) a)) := by
        rw [PCA.fstComb_pairEl, PCA.sndComb_pairEl, PCA.k_app_app, papp_some_some]
        exact hw
      simpa [descBody, Expr.eval] using hmem
    | inr y =>
      obtain ⟨b, hb, rfl⟩ := hz
      obtain ⟨w, hw, hwy⟩ := ht b y hb
      refine ⟨w, ?_, hwy⟩
      refine PCA.lam_app 0 (descBody r t) (PCA.env0 A) _ _ ?_
      have hmem : w ∈
          (((Part.some (PCA.fstComb A) ⬝ Part.some (PCA.pairEl (PCA.kI A) b)) ⬝ Part.some r)
            ⬝ Part.some t)
            ⬝ (Part.some (PCA.sndComb A) ⬝ Part.some (PCA.pairEl (PCA.kI A) b)) := by
        rw [PCA.fstComb_pairEl, PCA.sndComb_pairEl, PCA.kI_app, papp_some_some]
        exact hw
      simpa [descBody, Expr.eval] using hmem

@[simp] theorem coprodDesc_toFun {X Y Z : Assembly.{u, v} A} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (coprodDesc f g).toFun = Sum.elim f.toFun g.toFun := rfl

/-- The cofan given by the coproduct assembly. -/
noncomputable def coprodCofan (X Y : Assembly.{u, v} A) : BinaryCofan X Y :=
  BinaryCofan.mk (coprodInl X Y) (coprodInr X Y)

/-- The coproduct assembly really is a coproduct. -/
noncomputable def coprodCofanIsColimit (X Y : Assembly.{u, v} A) :
    IsColimit (coprodCofan X Y) :=
  BinaryCofan.isColimitMk (fun s => coprodDesc (BinaryCofan.inl s) (BinaryCofan.inr s))
    (fun _ => hom_ext fun _ => rfl) (fun _ => hom_ext fun _ => rfl)
    (fun s m h₁ h₂ => hom_ext fun z => by
      cases z with
      | inl x => exact congrArg (fun k : X ⟶ s.pt => k.toFun x) h₁
      | inr y => exact congrArg (fun k : Y ⟶ s.pt => k.toFun y) h₂)

instance (X Y : Assembly.{u, v} A) : HasBinaryCoproduct X Y :=
  ⟨⟨⟨coprodCofan X Y, coprodCofanIsColimit X Y⟩⟩⟩

instance instHasBinaryCoproducts : HasBinaryCoproducts (Assembly.{u, v} A) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance instHasFiniteCoproducts : HasFiniteCoproducts (Assembly.{u, v} A) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-! ### Coequalizers -/

variable {X Y : Assembly.{u, v} A}

/-- The relation generated by two morphisms: the codomain quotiented by it is their
coequalizer. -/
inductive CoeqRel (f g : X ⟶ Y) : Y.carrier → Y.carrier → Prop
  /-- The images of a common element are identified. -/
  | rel (x : X.carrier) : CoeqRel f g (f.toFun x) (g.toFun x)

/-- The coequalizer of two morphisms of assemblies: the quotient of the codomain, an element
being realized by the realizers of its representatives. -/
def coeqAsm (f g : X ⟶ Y) : Assembly.{u, v} A where
  carrier := Quot (CoeqRel f g)
  realizes a q := ∃ y, Quot.mk _ y = q ∧ Y.realizes a y
  exists_realizer q := by
    induction q using Quot.ind with
    | _ y =>
      obtain ⟨a, ha⟩ := Y.exists_realizer y
      exact ⟨a, y, rfl, ha⟩

/-- The projection onto the coequalizer, tracked by `i`: no computation is performed. -/
noncomputable def coeqProj (f g : X ⟶ Y) : Y ⟶ coeqAsm f g where
  toFun y := Quot.mk _ y
  tracked := ⟨PCA.i A, fun a y hy => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, y, rfl, hy⟩⟩

@[simp] theorem coeqProj_toFun (f g : X ⟶ Y) (y : Y.carrier) :
    (coeqProj f g).toFun y = Quot.mk _ y := rfl

theorem coeqProj_comp (f g : X ⟶ Y) : f ≫ coeqProj f g = g ≫ coeqProj f g :=
  hom_ext fun x => Quot.sound (CoeqRel.rel x)

/-- The morphism out of the coequalizer induced by a morphism that identifies the two
composites; it is tracked by whatever tracked that morphism. -/
noncomputable def coeqDesc {Z : Assembly.{u, v} A} {f g : X ⟶ Y} (h : Y ⟶ Z)
    (hh : f ≫ h = g ≫ h) : coeqAsm f g ⟶ Z where
  toFun := Quot.lift h.toFun fun _ _ hrel => by
    cases hrel with
    | rel x => exact congrArg (fun k : X ⟶ Z => k.toFun x) hh
  tracked := by
    obtain ⟨r, hr⟩ := h.tracked
    refine ⟨r, fun a q hq => ?_⟩
    obtain ⟨y, rfl, hy⟩ := hq
    exact hr a y hy

/-- The cofork built from the quotient assembly. -/
noncomputable def coeqCofork (f g : X ⟶ Y) : Cofork f g :=
  Cofork.ofπ (coeqProj f g) (coeqProj_comp f g)

theorem cofork_apply {f g : X ⟶ Y} (s : Cofork f g) (x : X.carrier) :
    s.π.toFun (f.toFun x) = s.π.toFun (g.toFun x) :=
  congrArg (fun k : X ⟶ s.pt => k.toFun x) s.condition

/-- The quotient assembly really is the coequalizer. -/
noncomputable def coeqCoforkIsColimit (f g : X ⟶ Y) : IsColimit (coeqCofork f g) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨coeqDesc s.π s.condition, hom_ext fun _ => rfl, fun {m} hm => hom_ext fun q => by
      induction q using Quot.ind with
      | _ y => exact congrArg (fun k : Y ⟶ s.pt => k.toFun y) hm⟩

instance hasColimit_parallelPair (f g : X ⟶ Y) : HasColimit (parallelPair f g) :=
  ⟨⟨⟨coeqCofork f g, coeqCoforkIsColimit f g⟩⟩⟩

instance instHasCoequalizers : HasCoequalizers (Assembly.{u, v} A) :=
  hasCoequalizers_of_hasColimit_parallelPair _

instance instHasFiniteColimits : HasFiniteColimits (Assembly.{u, v} A) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance instHasPushouts : HasPushouts (Assembly.{u, v} A) :=
  hasPushouts_of_hasColimit_span _

end Assembly

end Realizability
