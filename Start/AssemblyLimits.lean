/-
Finite limits in the category of assemblies.

`Start/Assembly.lean` builds the terminal assembly and binary products, and
`Start/AssemblyCcc.lean` the exponentials.  This file adds equalizers — a sub-assembly carved out
of the domain, with the realizers it inherits — and concludes that `Asm(A)` has all finite limits,
hence in particular pullbacks.

* `Realizability.Assembly.subAsm` — the sub-assembly of a predicate;
* `Realizability.Assembly.eqAsm`, `.eqFork`, `.eqForkIsLimit` — equalizers;
* `Realizability.Assembly.instHasEqualizers`, `.instHasFiniteLimits` — the conclusions.
-/

import Start.Assembly
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A]

/-! ### Sub-assemblies -/

/-- The sub-assembly of `X` cut out by a predicate: the elements satisfying `P`, with exactly the
realizers they had in `X`.  Nothing computational is added, which is why the inclusion is tracked
by the identity combinator. -/
def subAsm (X : Assembly.{u, v} A) (P : X.carrier → Prop) : Assembly.{u, v} A where
  carrier := {x : X.carrier // P x}
  realizes a x := X.realizes a x.1
  exists_realizer x := X.exists_realizer x.1

/-- The inclusion of a sub-assembly, tracked by `i`. -/
noncomputable def subIncl (X : Assembly.{u, v} A) (P : X.carrier → Prop) : subAsm X P ⟶ X where
  toFun x := x.1
  tracked := ⟨PCA.i A, fun a x hx => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, hx⟩⟩

@[simp] theorem subIncl_toFun (X : Assembly.{u, v} A) (P : X.carrier → Prop)
    (x : (subAsm X P).carrier) : (subIncl X P).toFun x = x.1 := rfl

/-- A morphism into `X` whose image satisfies `P` factors through the sub-assembly, with the same
realizer. -/
noncomputable def subLift {Z X : Assembly.{u, v} A} {P : X.carrier → Prop} (f : Z ⟶ X)
    (hf : ∀ z, P (f.toFun z)) : Z ⟶ subAsm X P where
  toFun z := ⟨f.toFun z, hf z⟩
  tracked := by
    obtain ⟨r, hr⟩ := f.tracked
    exact ⟨r, fun a z hz => hr a z hz⟩

@[simp] theorem subLift_toFun {Z X : Assembly.{u, v} A} {P : X.carrier → Prop} (f : Z ⟶ X)
    (hf : ∀ z, P (f.toFun z)) (z : Z.carrier) : (subLift f hf).toFun z = ⟨f.toFun z, hf z⟩ := rfl

/-- The inclusion of a sub-assembly is a monomorphism. -/
instance mono_subIncl (X : Assembly.{u, v} A) (P : X.carrier → Prop) : Mono (subIncl X P) where
  right_cancellation _ _ h :=
    hom_ext fun z => Subtype.ext (congrArg (fun k => k.toFun z) h)

/-! ### Equalizers -/

variable {X Y : Assembly.{u, v} A}

/-- The equalizer of two morphisms of assemblies: the sub-assembly on which they agree. -/
def eqAsm (f g : X ⟶ Y) : Assembly.{u, v} A :=
  subAsm X fun x => f.toFun x = g.toFun x

/-- The inclusion of the equalizer. -/
noncomputable def eqIncl (f g : X ⟶ Y) : eqAsm f g ⟶ X :=
  subIncl X _

theorem eqIncl_comp (f g : X ⟶ Y) : eqIncl f g ≫ f = eqIncl f g ≫ g :=
  hom_ext fun x => x.2

/-- The fork built from the equalizing sub-assembly. -/
noncomputable def eqFork (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (eqIncl f g) (eqIncl_comp f g)

theorem fork_apply {f g : X ⟶ Y} (s : Fork f g) (z : s.pt.carrier) :
    f.toFun (s.ι.toFun z) = g.toFun (s.ι.toFun z) :=
  congrArg (fun k : s.pt ⟶ Y => k.toFun z) s.condition

/-- The equalizing sub-assembly really is the equalizer: any fork factors through it uniquely,
and the factorization is tracked by whatever tracked the fork. -/
noncomputable def eqForkIsLimit (f g : X ⟶ Y) : IsLimit (eqFork f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨subLift (P := fun x => f.toFun x = g.toFun x) s.ι (fork_apply s), hom_ext fun _ => rfl,
      fun hm => hom_ext fun z =>
        Subtype.ext (congrArg (fun k : s.pt ⟶ X => k.toFun z) hm)⟩

instance hasLimit_parallelPair (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  ⟨⟨⟨eqFork f g, eqForkIsLimit f g⟩⟩⟩

instance instHasEqualizers : HasEqualizers (Assembly.{u, v} A) :=
  hasEqualizers_of_hasLimit_parallelPair _

instance instHasFiniteProducts : HasFiniteProducts (Assembly.{u, v} A) :=
  hasFiniteProducts_of_has_binary_and_terminal

instance instHasFiniteLimits : HasFiniteLimits (Assembly.{u, v} A) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance instHasPullbacks : HasPullbacks (Assembly.{u, v} A) :=
  hasPullbacks_of_hasLimit_cospan _

end Assembly

end Realizability
