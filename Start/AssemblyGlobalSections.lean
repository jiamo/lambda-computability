/-
Global sections and the indiscrete assembly.

An assembly can be stripped of its realizers, leaving its carrier; conversely a bare set can be
made into an assembly in which every element of the algebra realizes every element, so that no
computational information is imposed.  This file shows that the two constructions are adjoint,

  `Γ ⊣ ∇`,  `Γ : Asm(A) ⥤ Type`,  `∇ : Type ⥤ Asm(A)`,

that `∇` is fully faithful — a bare set is recovered from the assembly it generates — and that the
carrier of an assembly really is its set of *global sections*, the maps out of the terminal
assembly.  The assembly of propositions of `Start/AssemblySubobject.lean` is the value of `∇` at
`Prop`.

* `Realizability.Assembly.nablaAsm`, `.tracked_toNabla` — the indiscrete assembly on a set, and
  the fact that every function into it is tracked;
* `Realizability.Assembly.nablaFunctor`, `.gammaFunctor` — the two functors;
* `Realizability.Assembly.gammaNablaAdj` — the adjunction;
* `Realizability.Assembly.nablaFullyFaithful` — `∇` is fully faithful;
* `Realizability.Assembly.globalSectionsEquiv` — `Hom(1, X)` is the carrier of `X`;
* `Realizability.Assembly.propAsm_eq_nablaAsm` — the classifier is `∇ Prop`.

The other adjoint, the functor sending a set to the assembly whose realizers are indexed by the
set itself, is not constructed here.
-/

import Start.AssemblySubobject

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A]

/-! ### The indiscrete assembly -/

/-- The **indiscrete assembly** on a set: every element of the algebra realizes every element, so
nothing computational is required of a map into it. -/
def nablaAsm (A : Type u) [PCA A] (S : Type v) : Assembly.{u, v} A where
  carrier := S
  realizes _ _ := True
  exists_realizer _ := ⟨PCA.k, trivial⟩

@[simp] theorem nablaAsm_carrier (S : Type v) : (nablaAsm.{u, v} A S).carrier = S := rfl

/-- Every function into an indiscrete assembly is tracked, by the identity combinator. -/
theorem tracked_toNabla (X : Assembly.{u, v} A) {S : Type v} (f : X.carrier → S) :
    Tracked X (nablaAsm A S) f :=
  ⟨PCA.i A, fun a x _ => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, trivial⟩⟩

/-- The morphism of assemblies induced by a function into a set. -/
noncomputable def toNabla {X : Assembly.{u, v} A} {S : Type v} (f : X.carrier → S) :
    X ⟶ nablaAsm A S where
  toFun := f
  tracked := tracked_toNabla X f

@[simp] theorem toNabla_toFun {X : Assembly.{u, v} A} {S : Type v} (f : X.carrier → S)
    (x : X.carrier) : (toNabla f).toFun x = f x := rfl

/-- The assembly of propositions classifying the sub-assemblies is the indiscrete assembly on the
set of propositions. -/
theorem propAsm_eq_nablaAsm : propAsm.{u, v} A = nablaAsm A (ULift.{v} Prop) := rfl

/-! ### The two functors -/

/-- The indiscrete assembly, as a functor from sets to assemblies. -/
noncomputable def nablaFunctor (A : Type u) [PCA A] : Type v ⥤ Assembly.{u, v} A where
  obj S := nablaAsm A S
  map f := toNabla f
  map_id _ := hom_ext fun _ => rfl
  map_comp _ _ := hom_ext fun _ => rfl

/-- Global sections: an assembly is sent to its carrier and a tracked map to the function it
computes. -/
def gammaFunctor (A : Type u) [PCA A] : Assembly.{u, v} A ⥤ Type v where
  obj X := X.carrier
  map f := ↾f.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem gammaFunctor_obj (X : Assembly.{u, v} A) :
    (gammaFunctor A).obj X = X.carrier := rfl

/-! ### The adjunction -/

/-- Maps of assemblies into an indiscrete assembly are exactly functions on the carrier: there is
nothing to compute. -/
noncomputable def homNablaEquiv (X : Assembly.{u, v} A) (S : Type v) :
    (X.carrier ⟶ S) ≃ (X ⟶ nablaAsm A S) where
  toFun f := toNabla fun x => f x
  invFun f := ↾f.toFun
  left_inv _ := rfl
  right_inv _ := AsmHom.ext rfl

/-- **Global sections are left adjoint to the indiscrete assembly.** -/
noncomputable def gammaNablaAdj : gammaFunctor.{u, v} A ⊣ nablaFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homNablaEquiv
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => hom_ext fun _ => rfl }

/-- The indiscrete assembly functor is fully faithful: a set is recovered from the assembly it
generates. -/
noncomputable def nablaFullyFaithful : (nablaFunctor.{u, v} A).FullyFaithful where
  preimage f := ↾f.toFun
  map_preimage _ := AsmHom.ext rfl
  preimage_map _ := rfl

instance : (nablaFunctor.{u, v} A).Full := nablaFullyFaithful.full

instance : (nablaFunctor.{u, v} A).Faithful := nablaFullyFaithful.faithful

/-! ### Global sections are the points -/

/-- The carrier of an assembly is its set of **global sections**: every element is a morphism out
of the terminal assembly, tracked by a constant combinator, and distinct elements give distinct
morphisms. -/
noncomputable def globalSectionsEquiv (X : Assembly.{u, v} A) :
    (unitAsm.{u, v} A ⟶ X) ≃ X.carrier where
  toFun f := f.toFun PUnit.unit
  invFun x := pointMap X x
  left_inv _ := hom_ext fun t => by cases t; rfl
  right_inv _ := rfl

end Assembly

end Realizability
