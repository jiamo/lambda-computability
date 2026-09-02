/-
**Bi-initial objects, and the rigidity of the 2-cells out of the syntactic model of `λΠ`.**

In a 1-category an initial object has *exactly one* morphism into every object.  In a 2-category
the correct requirement is weaker and is the one the syntax of a type theory satisfies: the
hom-category into every object is **contractible** — there is a 1-cell, and between any two 1-cells
there is exactly one 2-cell.  This module defines that notion for an arbitrary
`CategoryTheory.Bicategory` and proves what it gives (any two 1-cells out of a bi-initial object are
canonically isomorphic; two bi-initial objects are equivalent), and then proves the half of it that
holds for `λΠ` unconditionally.

That half is **rigidity**.  A 2-cell out of the syntactic model is determined by its single
component at the *empty* context: every other context is an extension, and the component at an
extended context is forced by the component at the base, because the extension square is a
pullback (`Cwa.TwoCell.app_ext`).  Consequently, as soon as the *target* 1-cell sends the empty
context to a terminal object — which the canonical interpretation does, the empty context being
interpreted by the terminal object of the model — there is **at most one** 2-cell between two
1-cells out of the syntax, and any 2-cell between two such 1-cells is invertible as soon as one
exists in the other direction.

What is *not* proved here is the existence half: that every structure-preserving 1-cell out of the
syntax receives a 2-cell from the canonical interpretation.  That is the remaining content of the
biequivalence programme; the reduction is recorded in
`LambdaPiBiInitial.nonempty_iso_mor_iff`, which says that a 1-cell out of the syntax is isomorphic
to the canonical interpretation exactly when there are 2-cells in both directions — the 2-cells and
the isomorphism then being unique.

Main definitions:

* `CategoryTheory.Bicategory.BiInitial` — a bi-initial object of a bicategory;
* `LambdaPiFull.syntacticCModel` — the syntactic model of `λΠ` as an object of the 2-category of
  models.

Main results:

* `CategoryTheory.Bicategory.BiInitial.nonempty_iso` — any two 1-cells out of a bi-initial object
  are isomorphic;
* `CategoryTheory.Bicategory.BiInitial.nonempty_equiv` — **two bi-initial objects are equivalent**,
  by 1-cells whose composites are isomorphic to the identities;
* `LambdaPiBiInitial.app_eq_of_app_empty` — **rigidity**: a 2-cell out of the syntactic model is
  determined by its component at the empty context;
* `LambdaPiBiInitial.subsingleton_twoCell` — hence there is at most one 2-cell into a 1-cell
  sending the empty context to a terminal object;
* `LambdaPiBiInitial.isIso_twoCell` — such a 2-cell is invertible as soon as there is one in the
  other direction;
* `LambdaPiBiInitial.mor_obj_empty`, `LambdaPiBiInitial.isTerminal_mor_empty` — the canonical
  interpretation sends the empty context to the terminal object of the model.
-/

import Start.CwaBicat
import Start.LambdaPiInitial
import Start.LambdaPiCoherent

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory Limits

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- An object is **bi-initial** when the category of 1-cells out of it into any object is
contractible: there is a 1-cell, and between any two 1-cells there is exactly one 2-cell. -/
structure BiInitial (X : B) : Prop where
  /-- There is a 1-cell into every object. -/
  nonempty_hom : ∀ Y : B, Nonempty (X ⟶ Y)
  /-- There is a 2-cell between any two 1-cells. -/
  nonempty_twoCell : ∀ {Y : B} (F G : X ⟶ Y), Nonempty (F ⟶ G)
  /-- There is at most one 2-cell between two 1-cells. -/
  subsingleton_twoCell : ∀ {Y : B} (F G : X ⟶ Y), Subsingleton (F ⟶ G)

namespace BiInitial

variable {X : B}

/-- **Any two 1-cells out of a bi-initial object are isomorphic.** -/
theorem nonempty_iso (h : BiInitial X) {Y : B} (F G : X ⟶ Y) : Nonempty (F ≅ G) := by
  obtain ⟨θ⟩ := h.nonempty_twoCell F G
  obtain ⟨ψ⟩ := h.nonempty_twoCell G F
  exact ⟨⟨θ, ψ, (h.subsingleton_twoCell F F).elim _ _, (h.subsingleton_twoCell G G).elim _ _⟩⟩

/-- **Two bi-initial objects are equivalent**: there are 1-cells in both directions whose
composites are isomorphic to the identities. -/
theorem nonempty_equiv {X' : B} (h : BiInitial X) (h' : BiInitial X') :
    ∃ (F : X ⟶ X') (G : X' ⟶ X), Nonempty (F ≫ G ≅ 𝟙 X) ∧ Nonempty (G ≫ F ≅ 𝟙 X') := by
  obtain ⟨F⟩ := h.nonempty_hom X'
  obtain ⟨G⟩ := h'.nonempty_hom X
  exact ⟨F, G, h.nonempty_iso _ _, h'.nonempty_iso _ _⟩

end BiInitial

end CategoryTheory.Bicategory

/-! ### A category with attributes with no types -/

namespace Cwa

/-- **Any category carries a category with attributes with no types at all.**  Substitution,
context extension, the display maps and the pullback law are all vacuous, and so are the two
coherence laws, so this is an object of the 2-category of models. -/
def noTypes (C : Type u) [Category.{v} C] : Cwa.{u, v, 0} C where
  Ty _ := Empty
  tySub _ A := A
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  ext _ A := A.elim
  disp A := A.elim
  extend _ A := A.elim
  isPullback _ A := A.elim

/-- The coherence laws of a category with attributes with no types hold vacuously. -/
theorem extCoherent_noTypes (C : Type u) [Category.{v} C] : ExtCoherent (noTypes C) where
  extend_id A := A.elim
  extend_comp _ _ A := A.elim

end Cwa

/-! ### The syntactic model of `λΠ` as an object of the 2-category of models -/

namespace LambdaPiFull

open LambdaPiCat

/-- The syntactic model of `λΠ`, with all of its types, as an object of the 2-category of
models. -/
noncomputable def syntacticCModel : Cwa.CModel.{0, 0, 0} where
  Ctx := Ob
  str := syntactic
  coh := extCoherent_syntactic

end LambdaPiFull

/-! ### Rigidity of the 2-cells out of the syntax -/

namespace LambdaPiBiInitial

open LambdaPi LambdaPiCat LambdaPiFull Cwa

variable {D : Type u'} [Category.{v'} D] {S : Cwa.{u', v', w'} D}
  {F G : Cwa.Mor syntactic S}

/-- **Rigidity**: a 2-cell out of the syntactic model of `λΠ` is determined by its component at
the empty context.  Every context is an iterated extension of the empty one, and the component at
an extended context is forced by the component at the base, because the extension square is a
pullback. -/
theorem app_eq_of_app_empty (θ ψ : TwoCell F G)
    (h : θ.nat.app empty = ψ.nat.app empty) (Γ : Ob) : θ.nat.app Γ = ψ.nat.app Γ := by
  have key : ∀ (l : Ctx) (w : Wf l), θ.nat.app ⟨l, w⟩ = ψ.nat.app ⟨l, w⟩ := by
    intro l
    induction l with
    | nil => intro _; exact h
    | cons A l ih =>
        intro w
        cases w with
        | @cons _ _ s hl hA =>
            have i : (⟨A :: l, Wf.cons hl hA⟩ : Ob)
                ≅ extOb ⟨l, hl⟩ (tyMk ⟨A, s, hA⟩) :=
              convIso (C := ⟨A, s, hA⟩) (D := (tyMk (Γ := ⟨l, hl⟩) ⟨A, s, hA⟩).rep)
                TyQ.rep_conv.symm
            exact TwoCell.app_eq_of_iso _ i (ih hl)
  exact key Γ.ctx Γ.wf

/-- **There is at most one 2-cell out of the syntactic model into a 1-cell sending the empty
context to a terminal object.**  The component at the empty context has a terminal target, hence
is unique, and rigidity does the rest. -/
theorem subsingleton_twoCell (hterm : IsTerminal (G.fnc.obj empty)) :
    Subsingleton (TwoCell F G) := by
  refine ⟨fun θ ψ => TwoCell.ext ?_⟩
  refine NatTrans.ext ?_
  funext Γ
  exact app_eq_of_app_empty θ ψ (hterm.hom_ext _ _) Γ

/-- A 2-cell between 1-cells out of the syntactic model both of which send the empty context to a
terminal object is invertible as soon as there is a 2-cell in the other direction. -/
theorem isIso_twoCell (coh : ExtCoherent S) (hF : IsTerminal (F.fnc.obj empty))
    (hG : IsTerminal (G.fnc.obj empty)) (θ : TwoCell F G) (ψ : TwoCell G F) :
    @IsIso _ (morCategory (T := syntactic) coh) F G θ := by
  let _ := morCategory (T := syntactic) coh
  refine ⟨ψ, ?_, ?_⟩
  · exact (subsingleton_twoCell hF).elim _ _
  · exact (subsingleton_twoCell hG).elim _ _

/-! ### The canonical interpretation preserves the empty context -/

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- **The canonical interpretation sends the empty context to the interpretation of the empty
context**, which is the terminal object of the model. -/
theorem mor_obj_empty (hinj : M.PiInj) :
    (LambdaPiInitial.mor hinj).fnc.obj empty = M.emp := rfl

/-- Hence the canonical interpretation sends the empty context to a terminal object. -/
def isTerminal_mor_empty (hinj : M.PiInj) :
    IsTerminal ((LambdaPiInitial.mor hinj).fnc.obj empty) :=
  M.empIsTerminal

/-- **Reduction of bi-initiality to existence.**  A 1-cell out of the syntax sending the empty
context to a terminal object is isomorphic to the canonical interpretation exactly when there is a
2-cell in each direction; by rigidity, the 2-cells and hence the isomorphism are then unique. -/
theorem nonempty_iso_mor_iff (hinj : M.PiInj) (F : Cwa.Mor syntactic M.T)
    (hF : IsTerminal (F.fnc.obj empty)) :
    Nonempty (@Iso _ (morCategory (T := syntactic) M.co) (LambdaPiInitial.mor hinj) F)
      ↔ Nonempty (TwoCell (LambdaPiInitial.mor hinj) F)
          ∧ Nonempty (TwoCell F (LambdaPiInitial.mor hinj)) := by
  let _ := morCategory (T := syntactic) M.co
  constructor
  · rintro ⟨i⟩
    exact ⟨⟨i.hom⟩, ⟨i.inv⟩⟩
  · rintro ⟨⟨θ⟩, ⟨ψ⟩⟩
    exact ⟨⟨θ, ψ, (subsingleton_twoCell (isTerminal_mor_empty hinj)).elim _ _,
      (subsingleton_twoCell hF).elim _ _⟩⟩

/-- **At most one 2-cell into the canonical interpretation.** -/
theorem subsingleton_twoCell_mor (hinj : M.PiInj) (F : Cwa.Mor syntactic M.T) :
    Subsingleton (TwoCell F (LambdaPiInitial.mor hinj)) :=
  subsingleton_twoCell (isTerminal_mor_empty hinj)

/-! ### The syntactic model is *not* bi-initial among all coherent models -/

/-- The contexts of `λΠ` with no types at all, as an object of the 2-category of models. -/
def noTypesCModel : Cwa.CModel.{0, 0, 0} where
  Ctx := Ob
  str := Cwa.noTypes Ob
  coh := Cwa.extCoherent_noTypes Ob

/-- **The syntactic model of `λΠ` is not bi-initial in the 2-category of all coherent models.**
Bi-initiality asks for a 1-cell into *every* model, and a model need not have any types: a 1-cell
into the model with no types would have to produce a type out of the universe `∗` of the empty
context.  So the rigidity results above are the whole of what holds unconditionally; a positive
bi-initiality statement has to restrict the models. -/
theorem not_biInitial_syntacticCModel :
    ¬ CategoryTheory.Bicategory.BiInitial syntacticCModel := by
  intro h
  obtain ⟨F⟩ := h.nonempty_hom noTypesCModel
  exact (F.tyMap (LambdaPiUniv.uQ empty)).elim

end LambdaPiBiInitial
