/-
A classifier for the sub-assemblies of an assembly.

`Start/AssemblyLimits.lean` cuts out of an assembly `X` the sub-assembly `subAsm X P` of the
elements satisfying a predicate `P`, with the realizers they already had in `X`.  This file shows
that those sub-assemblies are **classified**: the assembly `propAsm A` of propositions, in which
every element of the algebra realizes every proposition, plays the role of `Ω`, and `subAsm X P`
is the pullback of `true : 1 ⟶ Ω` along the characteristic map of `P`.

* `Realizability.Assembly.propAsm` — the assembly of propositions, with no computational content;
* `Realizability.Assembly.charMap`, `.trueMap` — the characteristic map of a predicate, and the
  point picking out `True`;
* `Realizability.Assembly.homPropEquiv` — maps `X ⟶ propAsm A` are exactly the predicates on the
  carrier of `X`, so a characteristic map is determined by the predicate it tests;
* `Realizability.Assembly.isPullback_subAsm` — the classifying square is a pullback;
* `Realizability.Assembly.charMap_uniq`, `.exists_unique_charMap` — and the classifying map is the
  only one with that property.

The predicate `P` is an arbitrary proposition-valued function: no decidability and no realizer for
the truth of `P x` is asked for, which is why `propAsm` carries the indiscrete realizability
relation.  What is classified is therefore the sub-assemblies of `X` — equivalently the
*regular* subobjects, the ones whose realizers are inherited from `X` — and not every mono into
`X`; a mono may realize its elements with strictly fewer realizers than `X` does, and the category
of assemblies is not a topos.
-/

import Start.AssemblyLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A]

/-! ### The assembly of propositions -/

/-- The assembly of propositions: the carrier is `Prop` and every element of the algebra realizes
every proposition, so no computational information is attached to the truth of a proposition. -/
def propAsm (A : Type u) [PCA A] : Assembly.{u, v} A where
  carrier := ULift.{v} Prop
  realizes _ _ := True
  exists_realizer _ := ⟨PCA.k, trivial⟩

@[simp] theorem propAsm_realizes (a : A) (p : (propAsm.{u, v} A).carrier) :
    (propAsm.{u, v} A).realizes a p ↔ True := Iff.rfl

/-- Every function into `propAsm` is tracked, by the identity combinator: there is nothing to
compute. -/
theorem tracked_toPropAsm (X : Assembly.{u, v} A) (f : X.carrier → (propAsm.{u, v} A).carrier) :
    Tracked X (propAsm A) f :=
  ⟨PCA.i A, fun a x _ => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, trivial⟩⟩

/-- The characteristic map of a predicate on an assembly. -/
noncomputable def charMap (X : Assembly.{u, v} A) (P : X.carrier → Prop) : X ⟶ propAsm A where
  toFun x := ULift.up (P x)
  tracked := tracked_toPropAsm X _

@[simp] theorem charMap_toFun (X : Assembly.{u, v} A) (P : X.carrier → Prop) (x : X.carrier) :
    (charMap X P).toFun x = ULift.up (P x) := rfl

/-- The point of `propAsm` picking out `True`. -/
noncomputable def trueMap (A : Type u) [PCA A] : unitAsm.{u, v} A ⟶ propAsm A :=
  charMap _ fun _ => True

@[simp] theorem trueMap_toFun (t : (unitAsm.{u, v} A).carrier) :
    (trueMap A).toFun t = ULift.up True := rfl

/-- Morphisms into `propAsm` are exactly the predicates on the carrier: a characteristic map
carries no more information than the predicate it tests. -/
noncomputable def homPropEquiv (X : Assembly.{u, v} A) :
    (X ⟶ propAsm.{u, v} A) ≃ (X.carrier → Prop) where
  toFun f x := (f.toFun x).down
  invFun P := charMap X P
  left_inv _ := hom_ext fun _ => rfl
  right_inv _ := rfl

/-- The global element of `X` given by an element of its carrier, tracked by `k b` for any
realizer `b` of that element. -/
noncomputable def pointMap (X : Assembly.{u, v} A) (x : X.carrier) : unitAsm A ⟶ X where
  toFun _ := x
  tracked := by
    obtain ⟨b, hb⟩ := X.exists_realizer x
    have hr : Part.some ((PCA.app (PCA.k : A) b).get (PCA.k_dom b))
        = Part.some (PCA.k : A) ⬝ Part.some b := by
      rw [papp_some_some]; exact Part.some_get _
    refine ⟨(PCA.app (PCA.k : A) b).get (PCA.k_dom b), fun a _ _ => ⟨b, ?_, hb⟩⟩
    have hka := PCA.k_app_app b a
    rw [← hr, papp_some_some] at hka
    rw [hka]
    exact Part.mem_some _

@[simp] theorem pointMap_toFun (X : Assembly.{u, v} A) (x : X.carrier)
    (t : (unitAsm.{u, v} A).carrier) : (pointMap X x).toFun t = x := rfl

/-! ### The classifying square -/

variable {X : Assembly.{u, v} A} (P : X.carrier → Prop)

/-- The classifying square commutes: on the sub-assembly cut out by `P`, the predicate is true. -/
theorem subIncl_charMap :
    toUnit (subAsm X P) ≫ trueMap A = subIncl X P ≫ charMap X P :=
  hom_ext fun x => congrArg ULift.up (eq_true x.2).symm

/-- The classifying square, as a cone over `true` and the characteristic map. -/
noncomputable def charCone : PullbackCone (trueMap.{u, v} A) (charMap X P) :=
  PullbackCone.mk (toUnit (subAsm X P)) (subIncl X P) (subIncl_charMap P)

/-- Any cone over `true` and the characteristic map lands in the part of `X` where `P` holds. -/
theorem holds_of_cone (s : PullbackCone (trueMap.{u, v} A) (charMap X P)) (z : s.pt.carrier) :
    P (s.snd.toFun z) := by
  have h : True = P (s.snd.toFun z) :=
    congrArg (fun k : s.pt ⟶ propAsm A => (k.toFun z).down) s.condition
  exact h ▸ trivial

/-- The classifying square is a pullback: `subAsm X P` is the pullback of `true` along the
characteristic map of `P`. -/
noncomputable def charConeIsLimit : IsLimit (charCone P) :=
  PullbackCone.IsLimit.mk _
    (fun s => subLift (P := P) s.snd (holds_of_cone P s))
    (fun _ => isTerminalUnitAsm.hom_ext _ _)
    (fun _ => hom_ext fun _ => rfl)
    (fun s _ _ hsnd => hom_ext fun z =>
      Subtype.ext (congrArg (fun k : s.pt ⟶ X => k.toFun z) hsnd))

/-- **The sub-assemblies of `X` are classified by `propAsm`**: the square with the inclusion of
`subAsm X P` on one side and the characteristic map of `P` on the other is a pullback. -/
theorem isPullback_subAsm :
    IsPullback (toUnit (subAsm X P)) (subIncl X P) (trueMap.{u, v} A) (charMap X P) :=
  { w := subIncl_charMap P
    isLimit' := ⟨charConeIsLimit P⟩ }

/-! ### Uniqueness of the classifying map -/

/-- A map into `propAsm` whose square over `subAsm X P` is a pullback tests exactly `P`, so it is
the characteristic map of `P`. -/
theorem charMap_uniq (chi : X ⟶ propAsm.{u, v} A)
    (h : IsPullback (toUnit (subAsm X P)) (subIncl X P) (trueMap.{u, v} A) chi) :
    chi = charMap X P := by
  refine hom_ext fun x => ?_
  have hforward : ∀ y : X.carrier, P y → (chi.toFun y).down := by
    intro y hy
    have hy' : True = (chi.toFun y).down :=
      congrArg (fun k : subAsm X P ⟶ propAsm A => (k.toFun ⟨y, hy⟩).down) h.w
    exact hy' ▸ trivial
  have hbackward : (chi.toFun x).down → P x := by
    intro hx
    -- the element `x` gives a cone over `true` and `chi`, hence a point of `subAsm X P`
    have hw : toUnit (unitAsm.{u, v} A) ≫ trueMap A = pointMap X x ≫ chi :=
      hom_ext fun _ => congrArg ULift.up (eq_true hx).symm
    have hsnd : h.lift (toUnit (unitAsm.{u, v} A)) (pointMap X x) hw ≫ subIncl X P
        = pointMap X x := h.lift_snd _ _ hw
    have hx' : ((h.lift (toUnit (unitAsm.{u, v} A)) (pointMap X x) hw).toFun PUnit.unit).1 = x :=
      congrArg (fun k : unitAsm.{u, v} A ⟶ X => k.toFun PUnit.unit) hsnd
    exact hx' ▸ ((h.lift (toUnit (unitAsm.{u, v} A)) (pointMap X x) hw).toFun PUnit.unit).2
  have hprop : (chi.toFun x).down = P x := propext ⟨hbackward, hforward x⟩
  exact congrArg ULift.up hprop

/-- The characteristic map is the unique map making the square over `subAsm X P` a pullback. -/
theorem exists_unique_charMap :
    ∃! chi : X ⟶ propAsm.{u, v} A,
      IsPullback (toUnit (subAsm X P)) (subIncl X P) (trueMap.{u, v} A) chi :=
  ⟨charMap X P, isPullback_subAsm P, fun chi h => charMap_uniq P chi h⟩

end Assembly

end Realizability
