/-
`Type u` is locally cartesian closed, with the dependent product computed as an honest
dependent function type -- and that categorical dependent product is *the same* as the Π-type of
the standard model of dependent type theory built in `Start/CwaType.lean`.

Mathlib supplies the interfaces `CategoryTheory.ChosenPullbacksAlong` and
`CategoryTheory.ExponentiableMorphism`, but no instance for `Type u`.  This file builds both by
hand, choosing representatives that compute:

* the pullback of `A : Over X` along `f : Y ⟶ X` has total space `Σ y : Y, Fib A (f y)`
  (`LcccType.PbObj`), so substitution is literally reindexing of fibers;
* the pushforward of `B : Over Y` along `f` has total space `Σ x : X, ∀ y ∈ f⁻¹(x), Fib B y`
  (`LcccType.PiObj`), so the dependent product is literally the type of sections over a fiber.

The two adjunctions `Σ_f ⊣ f*` (`LcccType.mapPullbackAdj`) and `f* ⊣ Π_f`
(`LcccType.pullbackPushforwardAdj`) are proved directly, giving
`LcccType.instLocallyCartesianClosedType`.

The last section is the bridge between the two sides of the correspondence: for a family
`A : Γ → Type u` and a family `B` over its total space, the categorical dependent product of `B`
along the display map of `A` is isomorphic, in the slice over `Γ`, to the family
`fun x => (a : A x) → B ⟨x, a⟩`, which is exactly `CwaType.piStruct.Pi A B`
(`LcccType.piIso`, `LcccType.pi_fiber_equiv`).  So "categorical Π" and "type-theoretic Π" agree.
-/

import Start.Lccc
import Start.CwaType

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory

namespace LcccType

variable {X Y : Type u}

/-- The fiber of `A : Over X` over a point. -/
abbrev Fib (A : Over X) (x : X) : Type u := {a : A.left // A.hom a = x}

/-- Total space of the substituted family. -/
abbrev PbObj (f : Y ⟶ X) (A : Over X) : Type u := Σ y : Y, Fib A (f y)

@[simp] lemma hom_left_apply {A B : Over X} (g : A ⟶ B) (a : A.left) :
    B.hom (g.left a) = A.hom a := ConcreteCategory.congr_hom (Over.w g) a

theorem PbObj.ext {f : Y ⟶ X} {A : Over X} {p q : PbObj f A}
    (h1 : p.1 = q.1) (h2 : (p.2 : A.left) = (q.2 : A.left)) : p = q := by
  obtain ⟨y, a, ha⟩ := p
  obtain ⟨y', a', ha'⟩ := q
  cases h1
  cases h2
  rfl

def pullbackFunctor (f : Y ⟶ X) : Over X ⥤ Over Y where
  obj A := Over.mk (↾(fun p : PbObj f A => p.1))
  map {A B} g := Over.homMk (↾(fun p : PbObj f A =>
      (⟨p.1, ⟨g.left p.2.1, by simpa using p.2.2⟩⟩ : PbObj f B))) rfl
  map_id := by intro A; apply Over.OverMorphism.ext; rfl
  map_comp := by intro A B C g h; apply Over.OverMorphism.ext; rfl

def mapPullbackAdj (f : Y ⟶ X) : Over.map f ⊣ pullbackFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun B A =>
        { toFun := fun h => Over.homMk
            (↾fun b => (⟨B.hom b, ⟨h.left b, by
              simp [Over.map]⟩⟩ : PbObj f A)) rfl
          invFun := fun k => Over.homMk (↾fun b => ((k.left b).2 : A.left)) (by
            ext b
            have hb : (k.left b).1 = B.hom b := hom_left_apply k b
            change A.hom ((k.left b).2 : A.left) = f (B.hom b)
            rw [← hb]
            exact (k.left b).2.2)
          left_inv := by
            intro h
            apply Over.OverMorphism.ext
            rfl
          right_inv := by
            intro k
            ext b
            refine PbObj.ext ?_ rfl
            exact (hom_left_apply k b).symm }
      homEquiv_naturality_left_symm := by
        intro B B' A g h
        apply Over.OverMorphism.ext
        rfl
      homEquiv_naturality_right := by
        intro B A A' h k
        apply Over.OverMorphism.ext
        rfl }

instance chosenPullbacksAlong (f : Y ⟶ X) : ChosenPullbacksAlong f where
  pullback := pullbackFunctor f
  mapPullbackAdj := mapPullbackAdj f

/-- The total space of the dependent product of `B : Over Y` along `f : Y ⟶ X`: over a point
`x : X` it is the set of sections of `B` over the fiber of `f` at `x`. -/
abbrev PiObj (f : Y ⟶ X) (B : Over Y) : Type u :=
  Σ x : X, ∀ y : {y : Y // f y = x}, Fib B y.1

def pushforwardFunctor (f : Y ⟶ X) : Over Y ⥤ Over X where
  obj B := Over.mk (↾(fun p : PiObj f B => p.1))
  map {B B'} g := Over.homMk (↾fun p =>
    (⟨p.1, fun y => ⟨g.left (p.2 y).1, by simpa using (p.2 y).2⟩⟩ : PiObj f B')) rfl
  map_id := by intro B; apply Over.OverMorphism.ext; rfl
  map_comp := by intro B B' B'' g h; apply Over.OverMorphism.ext; rfl

theorem PiObj.ext' {f : Y ⟶ X} {B : Over Y} {x : X} {p : PiObj f B}
    (g : ∀ y : {y : Y // f y = x}, Fib B y.1) (hx : p.1 = x)
    (hg : ∀ (y : Y) (h1 : f y = x) (h2 : f y = p.1),
      ((g ⟨y, h1⟩ : Fib B y) : B.left) = ((p.2 ⟨y, h2⟩ : Fib B y) : B.left)) :
    (⟨x, g⟩ : PiObj f B) = p := by
  obtain ⟨x0, g0⟩ := p
  simp only at hx
  subst hx
  have hgg : g = g0 := by
    funext y
    exact Subtype.ext (hg y.1 y.2 y.2)
  rw [hgg]

def pullbackPushforwardAdj (f : Y ⟶ X) : pullbackFunctor f ⊣ pushforwardFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B =>
        { toFun := fun h => Over.homMk (↾fun a =>
            (⟨A.hom a, fun y => ⟨h.left ⟨y.1, ⟨a, y.2.symm⟩⟩, hom_left_apply h _⟩⟩ : PiObj f B)) rfl
          invFun := fun k => Over.homMk (↾fun p =>
            (((k.left p.2.1).2 ⟨p.1, ((hom_left_apply k p.2.1).trans p.2.2).symm⟩ : Fib B p.1) :
              B.left)) (by
            ext p
            change B.hom (((k.left p.2.1).2 ⟨p.1, _⟩ : Fib B p.1) : B.left) = p.1
            exact ((k.left p.2.1).2 ⟨p.1, _⟩).2)
          left_inv := by
            intro h
            ext p
            rfl
          right_inv := by
            intro k
            ext a
            refine PiObj.ext' _ (hom_left_apply k a) ?_
            intro y h1 h2
            rfl }
      homEquiv_naturality_left_symm := by
        intro A A' B g h
        apply Over.OverMorphism.ext
        rfl
      homEquiv_naturality_right := by
        intro A B B' h k
        apply Over.OverMorphism.ext
        rfl }

instance exponentiableMorphism (f : Y ⟶ X) : ExponentiableMorphism f where
  pushforward := pushforwardFunctor f
  pullbackPushforwardAdj := pullbackPushforwardAdj f


/-- **`Type u` is locally cartesian closed.** -/
instance instLocallyCartesianClosedType : LocallyCartesianClosed (Type u) where
  pushforward f := pushforwardFunctor f
  pullbackPushforwardAdj f := pullbackPushforwardAdj f

@[simp] theorem Pi_obj_eq {X Y : Type u} (f : Y ⟶ X) (B : Over Y) :
    (LocallyCartesianClosed.Pi f).obj B = Over.mk (↾(fun p : PiObj f B => p.1)) := rfl

@[simp] theorem Pullback_obj_eq {X Y : Type u} (f : Y ⟶ X) (A : Over X) :
    (LocallyCartesianClosed.Pullback f).obj A = Over.mk (↾(fun p : PbObj f A => p.1)) := rfl

/-! ### The categorical dependent product is the dependent function type

We now identify the pushforward along a *display map* with the Π-type of the standard model
`CwaType.families`. -/

open CwaType

/-- A family of types, viewed as an object of the slice category: its total space, projected to
the base.  This is exactly the display map of the category with attributes `CwaType.families`. -/
abbrev famOver {Γ : Type u} (A : Γ → Type u) : Over Γ := Over.mk (families.disp A)

/-- **The fibre of a display map is the family.**  The slice-category and family presentations of
a dependent type agree pointwise. -/
def famFibEquiv {Γ : Type u} (C : Γ → Type u) (x : Γ) : Fib (famOver C) x ≃ C x where
  toFun p := p.2 ▸ p.1.2
  invFun c := ⟨⟨x, c⟩, rfl⟩
  left_inv p := Subtype.ext (sigma_mk_eq p.1 x p.2)
  right_inv _ := rfl

/-- Isomorphic objects of a slice category have the same fibres. -/
def fibEquivOfIso {Γ : Type u} {A B : Over Γ} (e : A ≅ B) (x : Γ) : Fib A x ≃ Fib B x where
  toFun p := ⟨e.hom.left p.1, (hom_left_apply e.hom p.1).trans p.2⟩
  invFun q := ⟨e.inv.left q.1, (hom_left_apply e.inv q.1).trans q.2⟩
  left_inv p := Subtype.ext (by
    have h := congrArg CategoryTheory.CommaMorphism.left e.hom_inv_id
    simp only [Over.comp_left, Over.id_left] at h
    exact ConcreteCategory.congr_hom h p.1)
  right_inv q := Subtype.ext (by
    have h := congrArg CategoryTheory.CommaMorphism.left e.inv_hom_id
    simp only [Over.comp_left, Over.id_left] at h
    exact ConcreteCategory.congr_hom h q.1)

/-- Transport a dependent function `g` along the identification of the fibre of the display map
of `A` at `x` with `A x`. -/
def famTransport {Γ : Type u} {A : Γ → Type u} (B : Total A → Type u) {x : Γ}
    (g : (a : A x) → B ⟨x, a⟩) (y : Fib (famOver A) x) : B y.1 :=
  (sigma_mk_eq y.1 x y.2) ▸ g (y.2 ▸ y.1.2)

/-- Sections of a family `B` over the fibre of the display map of `A` at `x` are exactly the
dependent functions `(a : A x) → B ⟨x, a⟩`.  This is the fibrewise form of the identification of
the categorical dependent product with the type-theoretic one. -/
def piFiberEquiv {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) (x : Γ) :
    (∀ y : Fib (famOver A) x, Fib (famOver B) y.1) ≃ ((a : A x) → B ⟨x, a⟩) where
  toFun s a := famFibEquiv B ⟨x, a⟩ (s ⟨⟨x, a⟩, rfl⟩)
  invFun g y := (famFibEquiv B y.1).symm (famTransport B g y)
  left_inv s := by
    funext y
    obtain ⟨⟨x', a'⟩, h⟩ := y
    cases h
    exact (famFibEquiv B ⟨x', a'⟩).symm_apply_apply _
  right_inv g := by funext a; rfl

/-- **The categorical dependent product is the type-theoretic one.**  Pushing a family `B`
forward along the display map of `A` gives, up to isomorphism in the slice over `Γ`, the family
`CwaType.piStruct.Pi A B = fun x => (a : A x) → B ⟨x, a⟩`. -/
def piIso {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) :
    (LocallyCartesianClosed.Pi (families.disp A)).obj (famOver B) ≅
      famOver (piStruct.Pi A B) :=
  Over.isoMk (Equiv.toIso (Equiv.sigmaCongrRight (piFiberEquiv A B))) rfl

/-- **The categorical dependent sum is the sigma type.**  Composing the display map of `B` with
the display map of `A` -- that is, applying `Σ` along the display map of `A` -- gives, up to
isomorphism in the slice over `Γ`, the family
`CwaType.sigmaStruct.Sig A B = fun x => Σ a : A x, B ⟨x, a⟩`. -/
def sigmaIso {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) :
    (LocallyCartesianClosed.Sigma (families.disp A)).obj (famOver B) ≅
      famOver (sigmaStruct.Sig A B) :=
  Over.isoMk (Equiv.toIso (Equiv.sigmaAssoc (fun (x : Γ) (a : A x) => B ⟨x, a⟩))) rfl

/-- The fibre of the categorical dependent sum over `x` is the sigma type `Σ a : A x, B ⟨x, a⟩`,
i.e. the value at `x` of the Σ-type of the standard model. -/
def sigmaFibEquiv {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) (x : Γ) :
    Fib ((LocallyCartesianClosed.Sigma (families.disp A)).obj (famOver B)) x ≃
      sigmaStruct.Sig A B x :=
  (fibEquivOfIso (sigmaIso A B) x).trans (famFibEquiv (sigmaStruct.Sig A B) x)

/-- The fibre of the categorical dependent product over `x` is the dependent function type
`(a : A x) → B ⟨x, a⟩`, i.e. the value at `x` of the Π-type of the standard model. -/
def piFibEquiv {Γ : Type u} (A : Γ → Type u) (B : Total A → Type u) (x : Γ) :
    Fib ((LocallyCartesianClosed.Pi (families.disp A)).obj (famOver B)) x ≃
      piStruct.Pi A B x :=
  (famFibEquiv (fun x => ∀ y : Fib (famOver A) x, Fib (famOver B) y.1) x).trans
    (piFiberEquiv A B x)

end LcccType
