/-
**Bi-initiality in the lax 2-category of models.**

`Start/CwaBiInitial.lean` studies bi-initiality of the syntactic model of `λΠ` in the 2-category of
coherent models with the *strict* 2-cells: the 2-cells out of the syntax are rigid, and the
syntactic model is not bi-initial among *all* coherent models, because a model need not have any
types at all.  With the lax 2-category of `Start/CwaLaxBicat.lean` now available, the same question
can be asked — and, for the first time, stated — for the lax 2-cells.  This module records what
holds.

The classification of lax 2-cells (`Cwa.LaxTwoCell.equivNatTrans`) turns bi-initiality in the lax
2-category into a statement about the functors on contexts alone: an object is bi-initial exactly
when there is a 1-cell into every object and, between any two 1-cells out of it, exactly one
natural transformation of the underlying functors.  That is `Cwa.LaxCModel.biInitial_iff`.

For the syntax of `λΠ` the negative half of the strict story survives unchanged: there is no 1-cell
at all into the model with no types, so the syntactic model is not bi-initial in the lax 2-category
either (`LambdaPiLaxBiInitial.not_biInitial_laxSyntacticCModel`).  Restricted to the models of `λΠ`
with injective products both existence clauses do hold: there is a morphism of models, and between
any two morphisms of models out of the syntax there is a lax 2-cell — the image of the unique
strict one.  What is *not* claimed is the uniqueness clause: by the classification it asks that the
interpretation functors admit at most one natural transformation between them, which the rigidity
argument for strict 2-cells does not give, since a lax 2-cell has no compatibility with the types
to be exploited.

Main definitions:

* `LambdaPi.Model.toCModel`, `LambdaPi.Model.toLaxCModel` — a model of `λΠ` as an object of the
  (lax) 2-category of coherent models;
* `LambdaPiLaxBiInitial.laxSyntacticCModel` — the syntactic model of `λΠ` as an object of the lax
  2-category.

Main results:

* `Cwa.LaxCModel.biInitial_iff` — **bi-initiality in the lax 2-category is a condition on the
  functors on contexts**;
* `LambdaPiLaxBiInitial.not_biInitial_laxSyntacticCModel` — the syntactic model of `λΠ` is not
  bi-initial in the lax 2-category of all coherent models;
* `LambdaPiLaxBiInitial.nonempty_hom_lax`, `LambdaPiLaxBiInitial.nonempty_laxTwoCell_modelHom` —
  the two existence clauses do hold for the models with injective products;
* `LambdaPiLaxBiInitial.subsingleton_laxTwoCell_iff_natTrans` — the outstanding uniqueness clause,
  reduced to a statement about natural transformations of the interpretation functors.
-/

import Start.CwaLaxBicat
import Start.CwaBiInitial
import Start.LambdaPiInitialModelHom

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

namespace LaxCModel

/-- **Bi-initiality in the lax 2-category of models is a condition on the functors on contexts**:
an object is bi-initial exactly when there is a 1-cell into every object and, between the functors
underlying any two 1-cells out of it, exactly one natural transformation.  This is the
classification `Cwa.LaxTwoCell.equivNatTrans` of the lax 2-cells. -/
theorem biInitial_iff (X : LaxCModel.{u, v, w}) :
    Bicategory.BiInitial X ↔
      (∀ Y : LaxCModel.{u, v, w}, Nonempty (X ⟶ Y)) ∧
        ∀ (Y : LaxCModel.{u, v, w}) (F G : X ⟶ Y),
          Nonempty (F.fnc ⟶ G.fnc) ∧ Subsingleton (F.fnc ⟶ G.fnc) := by
  constructor
  · intro h
    refine ⟨h.nonempty_hom, fun Y F G => ⟨?_, ?_⟩⟩
    · obtain ⟨θ⟩ := h.nonempty_twoCell F G
      exact ⟨(θ : LaxTwoCell F G).nat⟩
    · exact (LaxTwoCell.subsingleton_iff_subsingleton_natTrans F G).mp
        (h.subsingleton_twoCell F G)
  · rintro ⟨hhom, hcell⟩
    refine ⟨hhom, fun {Y} F G => ?_, fun {Y} F G => ?_⟩
    · obtain ⟨n⟩ := (hcell Y F G).1
      exact ⟨LaxTwoCell.ofNat F G n⟩
    · exact (LaxTwoCell.subsingleton_iff_subsingleton_natTrans F G).mpr (hcell Y F G).2

end LaxCModel

end Cwa

/-! ### Models of `λΠ` as objects of the lax 2-category -/

namespace LambdaPi

variable {C : Type u} [Category.{v} C]

/-- A model of `λΠ` is in particular a coherent model of a dependent type theory. -/
def Model.toCModel (M : Model.{u, v, w} C) : Cwa.CModel.{u, v, w} where
  Ctx := C
  str := M.T
  coh := M.co

/-- A model of `λΠ`, as an object of the lax 2-category of models. -/
def Model.toLaxCModel (M : Model.{u, v, w} C) : Cwa.LaxCModel.{u, v, w} :=
  Cwa.LaxCModel.of M.toCModel

end LambdaPi

/-! ### The syntactic model in the lax 2-category -/

namespace LambdaPiLaxBiInitial

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv Cwa

/-- The syntactic model of `λΠ`, as an object of the lax 2-category of models. -/
noncomputable def laxSyntacticCModel : Cwa.LaxCModel.{0, 0, 0} :=
  Cwa.LaxCModel.of syntacticCModel

/-- The contexts of `λΠ` with no types at all, as an object of the lax 2-category of models. -/
def laxNoTypesCModel : Cwa.LaxCModel.{0, 0, 0} :=
  Cwa.LaxCModel.of LambdaPiBiInitial.noTypesCModel

/-- **The syntactic model of `λΠ` is not bi-initial in the lax 2-category of all coherent
models** either.  The obstruction is the one of `Start/CwaBiInitial.lean` and has nothing to do
with the 2-cells: bi-initiality asks for a 1-cell into *every* model, and a model need not have
any types, while a 1-cell out of the syntax must produce a type out of the universe `∗`. -/
theorem not_biInitial_laxSyntacticCModel :
    ¬ CategoryTheory.Bicategory.BiInitial laxSyntacticCModel := by
  intro h
  obtain ⟨F⟩ := h.nonempty_hom laxNoTypesCModel
  exact (F.tyMap (LambdaPiUniv.uQ empty)).elim

/-- **Into every small model of `λΠ` with injective products there is a 1-cell out of the
syntax**, in the lax 2-category: the interpretation.  The universes are those of the syntactic
model, so that both are objects of the same 2-category. -/
theorem nonempty_hom_lax {C₀ : Type} [SmallCategory C₀] {M₀ : Model.{0, 0, 0} C₀}
    (hinj : M₀.PiInj) : Nonempty (laxSyntacticCModel ⟶ M₀.toLaxCModel) :=
  ⟨(LambdaPiInitial.modelHom hinj).mor⟩

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-- **Between any two morphisms of models out of the syntax there is a lax 2-cell**: the image of
the unique strict one. -/
theorem nonempty_laxTwoCell_modelHom (hinj : M.PiInj) (H K : ModelHom syntacticModel M) :
    Nonempty (Cwa.LaxTwoCell H.mor K.mor) :=
  ⟨(Classical.choice (LambdaPiSelf.nonempty_unique_twoCell_modelHom hinj H K).1).toLax⟩

/-- **The uniqueness clause of bi-initiality in the lax 2-category, reduced.**  A lax 2-cell is
exactly a natural transformation of the functors on contexts, so there is at most one lax 2-cell
between two 1-cells out of the syntax exactly when the two interpretation functors admit at most
one natural transformation.  Unlike for the strict 2-cells
(`LambdaPiBiInitial.subsingleton_twoCell`)
this is *not* proved here: the rigidity argument uses the compatibility of a strict 2-cell with
the types, which a lax 2-cell does not carry. -/
theorem subsingleton_laxTwoCell_iff_natTrans (F G : Cwa.Mor syntactic M.T) :
    Subsingleton (Cwa.LaxTwoCell F G) ↔ Subsingleton (F.fnc ⟶ G.fnc) :=
  Cwa.LaxTwoCell.subsingleton_iff_subsingleton_natTrans F G

end LambdaPiLaxBiInitial
