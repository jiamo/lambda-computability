/-
**The modest assemblies are a reflective subcategory of the assemblies.**

An assembly is modest when its realizers determine its elements.  A general assembly can be forced
to be modest by identifying any two elements that share a realizer: the quotient
`Realizability.Assembly.modestQuot X` by the relation "`x` and `y` have a realizer in common"
carries the realizers of the representatives and *is* modest, because two classes with a common
realizer have representatives with a common realizer.

The quotient is universal.  A morphism from `X` into a modest assembly cannot separate two
elements that share a realizer — its tracker computes a single value on that common realizer, and
modesty of the codomain identifies the two images — so it factors through the quotient, uniquely
because the projection is surjective.  The projection is tracked by the identity combinator: no
computation happens, only the identification of elements.

This makes the quotient a left adjoint to the inclusion of the modest assemblies, i.e. exhibits
`Realizability.ModestCat A` as a *reflective* subcategory of `Asm(A)`; since the modest assemblies
are the PERs (`Start/ModestEquiv.lean`), the PERs are a reflective subcategory too.

Main definitions:

* `Realizability.Assembly.ShareRealizer`, `.modestQuot` — the relation and the quotient assembly;
* `Realizability.Assembly.modestUnit`, `.modestLift` — the projection and the induced map;
* `Realizability.Modest.reflector` — the reflection functor `Asm(A) ⥤ ModestCat A`.

Main results:

* `Realizability.Assembly.modest_modestQuot` — the quotient is modest;
* `Realizability.Assembly.modestLift_uniq` — the factorization is unique;
* `Realizability.Modest.reflectorAdj` — **the reflection is left adjoint to the inclusion**;
* `Realizability.Modest.instReflective` — the modest assemblies are a reflective subcategory;
* `Realizability.PER.reflectorAdj` — hence so are the PERs.
-/

import Start.ModestColimits
import Mathlib.CategoryTheory.Adjunction.Reflective

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Realizability

variable {A : Type u} [PCA A]

namespace Assembly

/-! ### The modest quotient of an assembly -/

/-- Two elements of an assembly *share a realizer* when some element of the algebra realizes both
of them.  A modest assembly is one for which this relation is equality. -/
def ShareRealizer (X : Assembly.{u, u} A) (x y : X.carrier) : Prop :=
  ∃ a, X.realizes a x ∧ X.realizes a y

/-- The **modest quotient** of an assembly: elements sharing a realizer are identified, and a
class is realized by the realizers of its representatives. -/
def modestQuot (X : Assembly.{u, u} A) : Assembly.{u, u} A where
  carrier := Quot (ShareRealizer X)
  realizes a q := ∃ x, Quot.mk _ x = q ∧ X.realizes a x
  exists_realizer q := by
    induction q using Quot.ind with
    | _ x =>
      obtain ⟨a, ha⟩ := X.exists_realizer x
      exact ⟨a, x, rfl, ha⟩

/-- **The modest quotient is modest**: two classes realized by the same element have
representatives sharing that realizer, hence are the same class. -/
theorem modest_modestQuot (X : Assembly.{u, u} A) : (modestQuot X).Modest := by
  rintro a q q' ⟨x, rfl, hx⟩ ⟨x', rfl, hx'⟩
  exact Quot.sound ⟨a, hx, hx'⟩

/-- The projection onto the modest quotient, tracked by `i`. -/
noncomputable def modestUnit (X : Assembly.{u, u} A) : X ⟶ modestQuot X where
  toFun x := Quot.mk _ x
  tracked := ⟨PCA.i A, fun a x hx => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, x, rfl, hx⟩⟩

@[simp] theorem modestUnit_toFun (X : Assembly.{u, u} A) (x : X.carrier) :
    (modestUnit X).toFun x = Quot.mk _ x := rfl

/-- A morphism into a modest assembly identifies elements sharing a realizer: its tracker computes
a single value on the common realizer, which realizes both images. -/
theorem apply_eq_of_shareRealizer {X M : Assembly.{u, u} A} (hM : M.Modest) (f : X ⟶ M)
    {x y : X.carrier} (h : ShareRealizer X x y) : f.toFun x = f.toFun y := by
  obtain ⟨a, hx, hy⟩ := h
  obtain ⟨r, hr⟩ := f.tracked
  obtain ⟨v, hv, hvx⟩ := hr a x hx
  obtain ⟨w, hw, hwy⟩ := hr a y hy
  rw [← Part.mem_unique hv hw] at hwy
  exact hM v _ _ hvx hwy

/-- The morphism out of the modest quotient induced by a morphism into a modest assembly; it is
tracked by whatever tracked that morphism. -/
noncomputable def modestLift {X M : Assembly.{u, u} A} (hM : M.Modest) (f : X ⟶ M) :
    modestQuot X ⟶ M where
  toFun := Quot.lift f.toFun fun _ _ h => apply_eq_of_shareRealizer hM f h
  tracked := by
    obtain ⟨r, hr⟩ := f.tracked
    refine ⟨r, fun a q hq => ?_⟩
    obtain ⟨x, rfl, hx⟩ := hq
    exact hr a x hx

@[simp] theorem modestLift_toFun {X M : Assembly.{u, u} A} (hM : M.Modest) (f : X ⟶ M)
    (x : X.carrier) : (modestLift hM f).toFun (Quot.mk _ x) = f.toFun x := rfl

theorem modestUnit_comp_modestLift {X M : Assembly.{u, u} A} (hM : M.Modest) (f : X ⟶ M) :
    modestUnit X ≫ modestLift hM f = f :=
  hom_ext fun _ => rfl

/-- **The factorization through the modest quotient is unique**, the projection being
surjective. -/
theorem modestLift_uniq {X M : Assembly.{u, u} A} (hM : M.Modest) (f : X ⟶ M)
    (g : modestQuot X ⟶ M) (hg : modestUnit X ≫ g = f) : g = modestLift hM f :=
  hom_ext fun q => by
    induction q using Quot.ind with
    | _ x => exact congrArg (fun k : X ⟶ M => k.toFun x) hg

end Assembly

/-! ### The reflection functor -/

namespace Modest

open Assembly

/-- The modest quotient as an object of the subcategory. -/
def quotModest (X : Assembly.{u, u} A) : ModestCat A :=
  ⟨modestQuot X, modest_modestQuot X⟩

/-- **The reflection of an assembly into the modest assemblies.** -/
noncomputable def reflector : Assembly.{u, u} A ⥤ ModestCat A where
  obj X := quotModest X
  map f := ObjectProperty.homMk (modestLift (modest_modestQuot _) (f ≫ modestUnit _))
  map_id X := ObjectProperty.hom_ext _ (hom_ext fun q => by
    induction q using Quot.ind with
    | _ x => rfl)
  map_comp f g := ObjectProperty.hom_ext _ (hom_ext fun q => by
    induction q using Quot.ind with
    | _ x => rfl)

@[simp] theorem reflector_obj_obj (X : Assembly.{u, u} A) :
    (reflector.obj X).obj = modestQuot X := rfl

/-- **The modest quotient is left adjoint to the inclusion of the modest assemblies.** -/
noncomputable def reflectorAdj : reflector ⊣ (modestProperty A).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M =>
        { toFun := fun g => modestUnit X ≫ g.hom
          invFun := fun f => ObjectProperty.homMk (modestLift M.2 f)
          left_inv := fun g => ObjectProperty.hom_ext _
            (modestLift_uniq M.2 _ g.hom rfl).symm
          right_inv := fun f => modestUnit_comp_modestLift M.2 f }
      homEquiv_naturality_left_symm := fun {X Y M} f g =>
        ObjectProperty.hom_ext _ (hom_ext fun q => by
          induction q using Quot.ind with
          | _ x => rfl)
      homEquiv_naturality_right := fun {X M N} g h => hom_ext fun _ => rfl }

/-- **The modest assemblies are a reflective subcategory of the assemblies.** -/
noncomputable instance instReflective : Reflective (modestProperty A).ι where
  L := reflector
  adj := reflectorAdj

end Modest

/-! ### The same for the PERs -/

namespace PER

/-- The reflection of an assembly into the PERs, along the equivalence with the modest
assemblies. -/
noncomputable def reflector : Assembly.{u, u} A ⥤ PER A :=
  Modest.reflector ⋙ (perEquivModest A).inverse

/-- **The PERs are a reflective subcategory of the assemblies**: the quotient of an assembly by
"sharing a realizer" is left adjoint to the assembly of a PER. -/
noncomputable def reflectorAdj :
    PER.reflector ⊣ (perEquivModest A).functor ⋙ (modestProperty A).ι :=
  Modest.reflectorAdj.comp (perEquivModest A).symm.toAdjunction

end PER

end Realizability
