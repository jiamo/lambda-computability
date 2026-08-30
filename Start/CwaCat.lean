/-
**The models of a dependent type theory form a category.**

`Start/CwaMor.lean` defines a morphism of categories with attributes together with an identity
morphism and a composite, but stops there: it does not check that these satisfy the laws of a
category, and indeed they do so only up to a computation — the comparison isomorphism of a
composite is a composite of isomorphisms, and composing with the identity isomorphism is not
definitionally trivial.

This module supplies the missing extensionality principle for morphisms (`Cwa.Mor.ext`, a morphism
is determined by its functor, its action on types and its comparison of extended contexts, the
remaining fields being propositions) and, with it, the three laws.  Bundling a model with its
category of contexts then gives an honest `CategoryTheory.Category` instance on the type of models.

Main definitions:

* `Cwa.Model` — a model of a dependent type theory: a category of contexts together with a
  category-with-attributes structure on it;
* `Cwa.Model.instCategory` — the category of models and their morphisms.

Main results:

* `Cwa.Mor.ext` — a morphism is determined by its data;
* `Cwa.Mor.id_comp`, `Cwa.Mor.comp_id`, `Cwa.Mor.assoc` — **the laws of a category**.
-/

import Start.CwaMor

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w' u'' v'' w'' u''' v''' w'''

open CategoryTheory

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {B : Type u'''} [Category.{v'''} B]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D} {R : Cwa.{u'', v'', w''} E}
  {Q : Cwa.{u''', v''', w'''} B}

namespace Mor

/-- **A morphism of models is determined by its data**: the functor on contexts, the action on
types and the comparison of extended contexts.  The remaining fields are propositions. -/
theorem ext {F G : Mor T S} (hfnc : F.fnc = G.fnc)
    (hty : ∀ {Γ : C} (A : T.Ty Γ), HEq (F.tyMap A) (G.tyMap A))
    (hext : ∀ {Γ : C} (A : T.Ty Γ), HEq (F.extIso A) (G.extIso A)) : F = G := by
  revert hfnc hty hext
  cases F with
  | mk fnc₁ ty₁ hs₁ iso₁ hd₁ he₁ =>
    cases G with
    | mk fnc₂ ty₂ hs₂ iso₂ hd₂ he₂ =>
      intro hfnc hty hext
      cases hfnc
      have hty' : @ty₁ = @ty₂ := by
        funext Γ A
        exact eq_of_heq (hty A)
      cases hty'
      have hiso' : @iso₁ = @iso₂ := by
        funext Γ A
        exact eq_of_heq (hext A)
      cases hiso'
      rfl

/-- Composing with the identity on the left does nothing. -/
theorem id_comp (F : Mor T S) : (Mor.id T).comp F = F := by
  refine ext rfl (fun _ => HEq.rfl) (fun A => heq_of_eq ?_)
  refine Iso.ext ?_
  simp [Mor.comp, Mor.id]

/-- Composing with the identity on the right does nothing. -/
theorem comp_id (F : Mor T S) : F.comp (Mor.id S) = F := by
  refine ext rfl (fun _ => HEq.rfl) (fun A => heq_of_eq ?_)
  refine Iso.ext ?_
  simp [Mor.comp, Mor.id]

/-- Composition of morphisms of models is associative. -/
theorem assoc (F : Mor T S) (G : Mor S R) (H : Mor R Q) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  refine ext rfl (fun _ => HEq.rfl) (fun A => heq_of_eq ?_)
  refine Iso.ext ?_
  simp [Mor.comp]

end Mor

/-- Two comparisons of an object with extensions by *equal* types agree as heterogeneous data as
soon as they agree after transport along that equality.  This is what `Cwa.Mor.ext` needs of the
comparison isomorphisms when the two morphisms act differently — but equally — on types. -/
theorem heq_iso_ext {X Δ : D} {A B : S.Ty Δ} (h : A = B) {I : X ≅ S.ext Δ A} {J : X ≅ S.ext Δ B}
    (hh : I.hom ≫ eqToHom (congrArg (S.ext Δ) h) = J.hom) : HEq I J := by
  cases h
  simp only [eqToHom_refl, Category.comp_id] at hh
  exact heq_of_eq (Iso.ext hh)

/-! ### The category of models -/

-- The three universes (contexts, morphisms, types) are independent and are intended to be given
-- explicitly, exactly as for `CategoryTheory.Cat`.
-- A universe linter may see the three universes only inside the `max` of `Model`'s own type
-- and report them as inseparable; they are in fact independent (they are chosen separately in
-- the fields), exactly as for `CategoryTheory.Cat`.
set_option linter.checkUnivs false in
/-- A **model of a dependent type theory**: a category of contexts together with a
category-with-attributes structure on it. -/
structure Model where
  /-- The category of contexts. -/
  Ctx : Type u
  /-- Its categorical structure. -/
  [inst : Category.{v} Ctx]
  /-- The types, terms and context extensions. -/
  str : Cwa.{u, v, w} Ctx

attribute [instance] Model.inst

/-- **The models of a dependent type theory and their morphisms form a category.** -/
instance Model.instCategory : Category.{max u v w} Model.{u, v, w} where
  Hom M N := Mor M.str N.str
  id M := Mor.id M.str
  comp F G := F.comp G
  id_comp := Mor.id_comp
  comp_id := Mor.comp_id
  assoc F G H := Mor.assoc F G H

end Cwa
