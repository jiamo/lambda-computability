/-
**A full democratic model that is not equivalent to the strictification of its contexts.**

`Start/CwaStrictifyFull.lean` builds, for a full model `T` on a category of contexts `C`, a
morphism of models `Cwa.fullStrictify : Cwa.ofPullbacks C ⟶ T`, the identity on contexts,
bijective on terms and hitting every type up to an isomorphism of extended contexts.  What it does
not build is a morphism back, and it records why: a morphism `T ⟶ Cwa.ofPullbacks C` sends a type
over `Γ` to a local universe whose base and generic family may not depend on `Γ`, so it amounts to
a universe naming every type of the model.

This module shows the obstruction is real, so no such comparison can be built in general.  The
standard model of families (`CwaType.families`, contexts are types, a type over `Γ` is a family
`Γ → Type u`) is full and democratic, and yet:

* `CwaType.false_of_mor_isEquivalence` — **there is no morphism of models from the standard model
  to the strictification of its contexts whose functor on contexts is an equivalence**;
* `CwaType.not_equivalent_ofPullbacks` — hence the standard model is **not equivalent, in the lax
  2-category of models, to the strictification of its category of contexts**.  In that 2-category
  the 2-cells are exactly the natural transformations of the functors on contexts
  (`Cwa.LaxCModel.homEquivNatTrans`) and a 2-cell is invertible as soon as its natural
  transformation is (`Cwa.LaxCModel.isIso_of_isIso_nat`), so an equivalence is precisely a pair of
  morphisms of models whose functors on contexts compose to functors isomorphic to the identity —
  which is what the statement refutes.

The argument is a cardinality one.  Substitution acts on a local universe by composing with the
classifying map alone, so the generic family of the image of a type is unchanged by substitution
(`CwaType.total_tySub`).  A family over a two-element context connects any two closed types, so
*all* closed types have the same generic family (`CwaType.total_const_eq`); and the extended
context of a closed type embeds into that generic family (`CwaType.exists_injective_total`).  A
single type of `Type u` would therefore receive every type of `Type u`, which Cantor's theorem
forbids.

Main definitions and results:

* `CwaType.isFull_families`, `CwaType.isDemocratic_families`, `CwaType.extCoherent_families` — the
  standard model is full, democratic and coherent, so `Cwa.fullStrictify` applies to it;
* `CwaType.false_of_mor_isEquivalence`, `CwaType.not_equivalent_ofPullbacks` — the refutation.
-/

import Start.CwaStrictifyFull
import Start.CwaType

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace CwaType

/-! ### The standard model is full, democratic and coherent -/

/-- **The standard model is full**: a function is the first projection out of the total space of
its family of fibres. -/
def isFull_families : Cwa.IsFull families.{u} where
  ty {_X _Z} f := fun z => {x // f x = z}
  iso {X _Z} f :=
    { hom := ↾fun x => (⟨f x, x, rfl⟩ : Total fun z => {x // f x = z})
      inv := ↾fun p => p.2.1
      hom_inv_id := rfl
      inv_hom_id := TypeCat.homEquiv.injective (funext fun p => by
        obtain ⟨z, x, hx⟩ := p
        cases hx
        rfl) }
  iso_disp _ := rfl

/-- **The standard model is democratic**: a context is the closed type it is. -/
def isDemocratic_families : Cwa.IsDemocratic families.{u} where
  empty := PUnit
  isTerminal := Types.isTerminalPUnit
  ty Γ := fun _ => Γ
  iso Γ :=
    { hom := ↾fun x => (⟨⟨⟩, x⟩ : Total fun _ : PUnit => Γ)
      inv := ↾fun p => p.2
      hom_inv_id := rfl
      inv_hom_id := TypeCat.homEquiv.injective (funext fun p => by
        obtain ⟨⟨⟩, x⟩ := p
        rfl) }

/-- **The standard model is coherent**: substitution on extended contexts is functorial. -/
theorem extCoherent_families : Cwa.ExtCoherent families.{u} where
  extend_id _ := rfl
  extend_comp _ _ _ := rfl

/-! ### No morphism to the strictification of the contexts -/

variable (M : Cwa.Mor families.{u} (Cwa.ofPullbacks (Type u)))

/-- **Substitution does not change the generic family**: it acts on the classifying map alone. -/
theorem total_tySub {Γ Δ : Type u} (σ : Δ ⟶ Γ) (A : families.Ty Γ) :
    (M.tyMap (families.tySub σ A)).total = (M.tyMap A).total :=
  congrArg LuTy.total (M.tyMap_sub σ A)

/-- **All closed types have the same generic family**: a family over a two-element context has
both of them as substitution instances. -/
theorem total_const_eq (X Y : Type u) :
    (M.tyMap (fun _ : PUnit => X)).total = (M.tyMap (fun _ : PUnit => Y)).total := by
  have hx : (M.tyMap (fun _ : PUnit => X)).total
      = (M.tyMap (fun b : ULift.{u} Bool => cond b.down X Y)).total :=
    total_tySub M (↾fun _ : PUnit => (⟨true⟩ : ULift.{u} Bool))
      (fun b : ULift.{u} Bool => cond b.down X Y)
  have hy : (M.tyMap (fun _ : PUnit => Y)).total
      = (M.tyMap (fun b : ULift.{u} Bool => cond b.down X Y)).total :=
    total_tySub M (↾fun _ : PUnit => (⟨false⟩ : ULift.{u} Bool))
      (fun b : ULift.{u} Bool => cond b.down X Y)
  rw [hx, hy]

/-- **A closed type embeds into its generic family**: its extended context is the fibre of the
generic family over the classifying point. -/
theorem exists_injective_total (hsub : Subsingleton (M.fnc.obj PUnit))
    (hne : Nonempty (M.fnc.obj PUnit)) (hf : M.fnc.Faithful) (X : Type u) :
    ∃ f : X → (M.tyMap (fun _ : PUnit => X)).total, Function.Injective f := by
  have := hf
  obtain ⟨e0⟩ := hne
  set A : families.Ty PUnit := fun _ : PUnit => X with hA
  set P : LuTy (M.fnc.obj PUnit) := M.tyMap A with hP
  set pt : X → (PUnit ⟶ families.ext PUnit A) := fun x => ↾fun _ => ⟨⟨⟩, x⟩ with hpt
  refine ⟨fun x => LuTy.gen P ((M.extIso A).hom (M.fnc.map (pt x) e0)), ?_⟩
  intro x y hxy
  -- the two elements of the extended context agree, because they agree on both projections
  have hel : (M.extIso A).hom (M.fnc.map (pt x) e0) = (M.extIso A).hom (M.fnc.map (pt y) e0) := by
    have hk : (↾fun _ : PUnit => (M.extIso A).hom (M.fnc.map (pt x) e0))
        = (↾fun _ : PUnit => (M.extIso A).hom (M.fnc.map (pt y) e0)) := by
      refine (LuTy.isPullback_gen P).hom_ext ?_ ?_
      · exact TypeCat.homEquiv.injective (funext fun _ => hxy)
      · exact TypeCat.homEquiv.injective (funext fun _ => Subsingleton.elim _ _)
    exact congrArg (fun h : PUnit ⟶ LuTy.ext (M.fnc.obj PUnit) P => h ⟨⟩) hk
  -- hence the two maps out of the image of the terminal context agree
  have hmap : M.fnc.map (pt x) = M.fnc.map (pt y) :=
    TypeCat.homEquiv.injective (funext fun z => by
      have hz : z = e0 := Subsingleton.elim _ _
      subst hz
      exact (M.extIso A).toEquiv.injective hel)
  have hptxy : pt x = pt y := M.fnc.map_injective hmap
  have := congrArg (fun h : PUnit ⟶ families.ext PUnit A => (h ⟨⟩).2) hptxy
  exact this

/-- **There is no morphism of models from the standard model to the strictification of its
category of contexts whose functor on contexts is an equivalence.**  Every type of `Type u` would
embed into a single one. -/
theorem false_of_mor_isEquivalence (h : M.fnc.IsEquivalence) : False := by
  have := h
  -- the image of the terminal context is terminal, hence a singleton
  have hterm : IsTerminal (M.fnc.obj (PUnit : Type u)) :=
    IsTerminal.isTerminalObj M.fnc _ Types.isTerminalPUnit
  have hiso : M.fnc.obj (PUnit : Type u) ≅ (PUnit : Type u) :=
    hterm.uniqueUpToIso Types.isTerminalPUnit
  have hsub : Subsingleton (M.fnc.obj (PUnit : Type u)) :=
    hiso.toEquiv.subsingleton_congr.2 inferInstance
  have hne : Nonempty (M.fnc.obj (PUnit : Type u)) := ⟨hiso.inv ⟨⟩⟩
  -- every type embeds into one and the same type
  set Q : Type u := (M.tyMap (fun _ : PUnit => (PUnit : Type u))).total with hQ
  obtain ⟨f, hf'⟩ := exists_injective_total M hsub hne inferInstance (Set Q)
  have he : (M.tyMap (fun _ : PUnit => (Set Q : Type u))).total = Q :=
    total_const_eq M (Set Q) PUnit
  exact Function.cantor_injective (fun s => Equiv.cast he (f s))
    ((Equiv.cast he).injective.comp hf')

/-- **The standard model is not equivalent, in the lax 2-category of models, to the
strictification of its category of contexts.**  An equivalence there is a pair of morphisms of
models whose functors on contexts compose to functors isomorphic to the identity. -/
theorem not_equivalent_ofPullbacks (N : Cwa.Mor (Cwa.ofPullbacks (Type u)) families.{u})
    (i₁ : M.fnc ⋙ N.fnc ≅ 𝟭 (Type u)) (i₂ : N.fnc ⋙ M.fnc ≅ 𝟭 (Type u)) : False :=
  false_of_mor_isEquivalence M
    (CategoryTheory.Equivalence.mk M.fnc N.fnc i₁.symm i₂).isEquivalence_functor

end CwaType
