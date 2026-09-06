/-
**The uniqueness clause of lax bi-initiality fails.**

`Start/CwaBiInitial.lean` proves that the syntactic model of `λΠ` is rigid for the *strict* 2-cells:
between two morphisms of models out of the syntax there is exactly one.  `Start/CwaLaxBicat.lean`
weakens the 2-cells, and `Start/CwaLaxBiInitial.lean` reduces the corresponding uniqueness question
to a statement about the functors on contexts alone
(`LambdaPiLaxBiInitial.subsingleton_laxTwoCell_iff_natTrans`): there is at most one *lax* 2-cell
between two 1-cells out of the syntax exactly when the two interpretation functors admit at most
one natural transformation.  That question was left open.

It has a negative answer, and this module settles it.  The model of `Start/PointedModel.lean` lives
on the pointed sets, where the constant map to the base point is a natural endomorphism of the
identity functor; whiskering it with the interpretation gives a natural endomorphism of the
interpretation functor which is not the identity, because the interpretation of the context `x : ∗`
has more than one point.  So the two lax 2-cells it induces are distinct, and the syntactic model of
`λΠ` is **not** bi-initial in the lax 2-category, not even among the models of `λΠ` with injective
products.

The strict rigidity theorem is of course untouched: the collapsing 2-cell is not a strict one, since
substituting along a constant map does not carry a type to itself.

Main definitions:

* `PointedModel.collapseNat` — the collapsing natural endomorphism of a functor into the pointed
  sets;
* `PointedModel.ptModelHom` — the interpretation of the syntax of `λΠ` in the pointed model.

Main results:

* `PointedModel.not_subsingleton_natTrans` — **the interpretation functor of the syntax of `λΠ` in
  the pointed model admits two distinct natural endomorphisms**;
* `PointedModel.not_subsingleton_laxTwoCell` — hence two distinct lax 2-cells;
* `PointedModel.not_subsingleton_laxTwoCell_modelHom` — **the uniqueness clause of bi-initiality in
  the lax 2-category fails for the models of `λΠ` with injective products**.
-/

import Start.PointedModel
import Start.CwaLaxBiInitial

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace PointedModel

open LambdaPi LambdaPiCat LambdaPiUniv Cwa

/-! ### The collapsing natural transformation -/

/-- **The collapsing natural endomorphism of a functor into the pointed sets**: at every object it
is the constant map to the base point.  Naturality is exactly the fact that a morphism of pointed
sets preserves the base point. -/
def collapseNat {C : Type u} [Category.{v} C] (F : C ⥤ Pointed) : F ⟶ F where
  app Y := ⟨fun _ => (F.obj Y).point, rfl⟩
  naturality _ _ f := Pointed.Hom.ext (funext fun _ => ((F.map f).map_point).symm)

@[simp] theorem collapseNat_app_toFun {C : Type u} [Category.{v} C] (F : C ⥤ Pointed) (Y : C)
    (y : (F.obj Y).X) : ((collapseNat F).app Y).toFun y = (F.obj Y).point := rfl

/-- An object isomorphic to a one-point object has one point. -/
theorem eq_of_iso_subsingleton {Y Z : Pointed} (e : Y ≅ Z) (h : ∀ y y' : Y.X, y = y')
    (z z' : Z.X) : z = z' := by
  have h1 : ∀ x : Z.X, e.hom.toFun (e.inv.toFun x) = x :=
    fun x => congrFun (congrArg Pointed.Hom.toFun e.inv_hom_id) x
  rw [← h1 z, ← h1 z', h (e.inv.toFun z) (e.inv.toFun z')]

/-! ### The interpretation of the syntax in the pointed model -/

/-- **The interpretation of the syntax of `λΠ` in the pointed model.** -/
noncomputable def ptModelHom : ModelHom syntacticModel ptModel :=
  LambdaPiInitial.modelHom ptModel_piInj

/-- The interpretation functor on contexts. -/
noncomputable abbrev ptFnc : LambdaPiCat.Ob ⥤ Pointed := ptModelHom.mor.fnc

/-- The context `x : ∗` of `λΠ`. -/
noncomputable abbrev starCtx : LambdaPiCat.Ob := syntacticModel.T.ext empty (uQ empty)

/-- **The interpretation of the context `x : ∗` has more than one point**: it is isomorphic to the
extension of the interpretation of the empty context by the universe, whose fibre is `ℕ`. -/
theorem starCtx_not_subsingleton : ¬ ∀ y y' : (ptFnc.obj starCtx).X, y = y' := by
  intro h
  set X : Pointed := ptFnc.obj empty with hX
  have hU : ptModelHom.mor.tyMap (uQ empty) = (fun _ => uE : X.X → TyE) :=
    ptModelHom.pu.U_map empty
  have e : ptFnc.obj starCtx ≅ extPt X (fun _ => uE) :=
    ptModelHom.mor.extIso (uQ empty) ≪≫ eqToIso (congrArg (extPt X) hU)
  have hz : (⟨X.point, (0 : ℕ)⟩ : extCarrier X (fun _ => uE))
      = ⟨X.point, (1 : ℕ)⟩ := eq_of_iso_subsingleton e h _ _
  exact Nat.zero_ne_one (eq_of_heq (Sigma.mk.inj_iff.mp hz).2)

/-! ### Two distinct lax 2-cells -/

/-- **The collapsing natural endomorphism of the interpretation functor is not the identity.** -/
theorem collapseNat_ne_id : collapseNat ptFnc ≠ 𝟙 ptFnc := by
  intro h
  refine starCtx_not_subsingleton (fun y y' => ?_)
  have hy : ∀ z : (ptFnc.obj starCtx).X, (ptFnc.obj starCtx).point = z := by
    intro z
    exact congrFun (congrArg Pointed.Hom.toFun (congrFun (congrArg NatTrans.app h) starCtx)) z
  rw [← hy y, ← hy y']

/-- **The interpretation functor of the syntax of `λΠ` in the pointed model admits two distinct
natural endomorphisms**, the identity and the collapsing one. -/
theorem not_subsingleton_natTrans : ¬ Subsingleton (ptModelHom.mor.fnc ⟶ ptModelHom.mor.fnc) := by
  intro h
  exact collapseNat_ne_id (h.elim _ _)

/-- **There are two distinct lax 2-cells between the interpretation and itself.** -/
theorem not_subsingleton_laxTwoCell :
    ¬ Subsingleton (Cwa.LaxTwoCell ptModelHom.mor ptModelHom.mor) := by
  intro h
  exact not_subsingleton_natTrans
    ((Cwa.LaxTwoCell.subsingleton_iff_subsingleton_natTrans _ _).mp h)

/-- **The uniqueness clause of bi-initiality in the lax 2-category fails**, even for the models of
`λΠ` with injective products: there is such a model, the pointed one, and a morphism of models out
of the syntax which admits two distinct lax 2-cells to itself.  Compare
`LambdaPiSelf.nonempty_unique_twoCell_modelHom`, which gives exactly one *strict* 2-cell. -/
theorem not_subsingleton_laxTwoCell_modelHom :
    ¬ ∀ (C : Type 1) (_ : Category.{0} C) (M : Model.{1, 0, 0} C), M.PiInj →
        ∀ H K : ModelHom syntacticModel M, Subsingleton (Cwa.LaxTwoCell H.mor K.mor) := by
  intro h
  exact not_subsingleton_laxTwoCell
    (h Pointed Pointed.largeCategory ptModel ptModel_piInj ptModelHom ptModelHom)

end PointedModel
