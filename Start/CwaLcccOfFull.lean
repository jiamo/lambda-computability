/-
**The category of contexts of a full model with dependent products is locally cartesian closed.**

`Start/CwaDemocratic.lean` defines a *full* model — one in which every morphism of contexts is a
display map up to isomorphism over its codomain — and proves that its category of contexts has
pullbacks.  This module proves the second half of the intrinsic description of the models that
locally cartesian closed categories present: if a full model carries a natural Π-structure, then
its category of contexts is locally cartesian closed.

`Start/CwaLcccOfPi.lean` proves this for the *strictified* model of a category with pullbacks,
where a type is a local universe and a term is presented by its code.  Here nothing of the sort is
available: the dependent product is built from the presentation of a morphism given by fullness,
and the terms are handled through the bijection of `Start/CwaHomOver.lean` between the maps into a
display map lying over a substitution and the terms of the substituted type.

Main definitions:

* `Cwa.LcccOfFull.piObj` — the candidate dependent product of an object of a slice: the display
  map of the dependent product of the two types presenting the morphism and the object;
* `Cwa.LcccOfFull.transpose` — the transposition, a bijection between the maps out of the pullback
  and the maps into the dependent product.

Main results:

* `Cwa.LcccOfFull.transpose_naturality` — the transposition is natural in the slice object, which
  is the law `(λ b)[σ] = λ (b[σ⁺])` of a natural Π-structure;
* `LcccPullbacks.ofIsFull` — **the category of contexts of a full model with a natural
  Π-structure is locally cartesian closed**.
-/

import Start.CwaDemocratic
import Start.CwaHomOver
import Start.CwaLcccOfPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- Maps over the structure map of a slice object into a display map are morphisms of the slice. -/
def overHomEquiv {Y : C} (w : Over Y) (B : T.Ty Y) :
    HomOver (T := T) w.hom B ≃ (w ⟶ Over.mk (T.disp B)) where
  toFun k := Over.homMk k.1 k.2
  invFun k := ⟨k.left, Over.w k⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

namespace LcccOfFull

/-! ### The two presentations -/

/-- The type over the extended context `Y.f` presenting an object of the slice over `X`: the
object is a morphism into `X`, and `X` is the extended context. -/
def sliceTy {X Y : C} (h : IsFull T) (f : X ⟶ Y) (g : Over X) : T.Ty (T.ext Y (h.ty f)) :=
  h.ty (g.hom ≫ (h.iso f).hom)

/-- The presentation of an object of the slice over `X` as an extended context. -/
def sliceIso {X Y : C} (h : IsFull T) (f : X ⟶ Y) (g : Over X) :
    g.left ≅ T.ext (T.ext Y (h.ty f)) (sliceTy h f g) :=
  h.iso (g.hom ≫ (h.iso f).hom)

theorem sliceIso_disp {X Y : C} (h : IsFull T) (f : X ⟶ Y) (g : Over X) :
    (sliceIso h f g).hom ≫ T.disp (sliceTy h f g) = g.hom ≫ (h.iso f).hom :=
  h.iso_disp _

theorem sliceIso_inv_hom {X Y : C} (h : IsFull T) (f : X ⟶ Y) (g : Over X) :
    (sliceIso h f g).inv ≫ g.hom = T.disp (sliceTy h f g) ≫ (h.iso f).inv := by
  have hd : (sliceIso h f g).hom ≫ T.disp (sliceTy h f g) ≫ (h.iso f).inv = g.hom := by
    rw [← Category.assoc, sliceIso_disp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hd, Iso.inv_hom_id_assoc]

/-- The extension square of the substituted presentation is the pullback of `w.hom` along `f`. -/
theorem isPullback_ext {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y) :
    IsPullback (T.disp (T.tySub w.hom (h.ty f)))
      (T.extend w.hom (h.ty f) ≫ (h.iso f).inv) w.hom f :=
  (h.isPullback f w.hom).flip

/-- The comparison of the extended context with the chosen pullback. -/
noncomputable def pbIso [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y) :
    T.ext w.left (T.tySub w.hom (h.ty f)) ≅ Limits.pullback w.hom f :=
  (isPullback_ext h f w).isoPullback

@[simp] theorem pbIso_hom_fst [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y) :
    (pbIso h f w).hom ≫ Limits.pullback.fst w.hom f = T.disp (T.tySub w.hom (h.ty f)) :=
  IsPullback.isoPullback_hom_fst _

@[simp] theorem pbIso_hom_snd [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y) :
    (pbIso h f w).hom ≫ Limits.pullback.snd w.hom f
      = T.extend w.hom (h.ty f) ≫ (h.iso f).inv :=
  IsPullback.isoPullback_hom_snd _

theorem pbIso_hom_snd_hom [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y) :
    (pbIso h f w).hom ≫ Limits.pullback.snd w.hom f ≫ (h.iso f).hom
      = T.extend w.hom (h.ty f) := by
  rw [← Category.assoc, pbIso_hom_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem pbIso_inv_snd [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y) :
    (pbIso h f w).inv ≫ T.extend w.hom (h.ty f) ≫ (h.iso f).inv
      = Limits.pullback.snd w.hom f := by
  rw [← pbIso_hom_snd h f w, Iso.inv_hom_id_assoc]

/-- **A morphism of the slice over `X` out of the pullback of `w.hom` along `f` is a map over the
action of `w.hom` on extended contexts into the display map of the presented type.** -/
noncomputable def sliceHomEquiv [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y)
    (w : Over Y) (g : Over X) :
    ((Over.pullback f).obj w ⟶ g)
      ≃ HomOver (T := T) (T.extend w.hom (h.ty f)) (sliceTy h f g) where
  toFun k := ⟨(pbIso h f w).hom ≫ k.left ≫ (sliceIso h f g).hom, by
    rw [Category.assoc, Category.assoc, sliceIso_disp, ← Category.assoc k.left, Over.w k]
    exact pbIso_hom_snd_hom h f w⟩
  invFun k := Over.homMk ((pbIso h f w).inv ≫ k.1 ≫ (sliceIso h f g).inv) (by
    rw [Category.assoc, Category.assoc, sliceIso_inv_hom, ← Category.assoc k.1, k.2]
    exact pbIso_inv_snd h f w)
  left_inv k := by
    ext
    simp
  right_inv k := by
    refine Subtype.ext ?_
    simp

@[simp] theorem sliceHomEquiv_val [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y)
    (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    (sliceHomEquiv h f w g k).1 = (pbIso h f w).hom ≫ k.left ≫ (sliceIso h f g).hom := rfl

/-! ### The transposition -/

/-- **The candidate dependent product** of an object of the slice over `X`: the display map of the
dependent product of the two presented types. -/
def piObj {X Y : C} (h : IsFull T) (P : NaturalPiStruct T) (f : X ⟶ Y) (g : Over X) : Over Y :=
  Over.mk (T.disp (P.Pi (h.ty f) (sliceTy h f g)))

/-- The body of the transposition: a morphism out of the pullback, read as a term. -/
noncomputable def bodyOf [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y)
    (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    T.Tm (T.ext w.left (T.tySub w.hom (h.ty f)))
      (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g)) :=
  homOverEquivTm _ _ (sliceHomEquiv h f w g k)

theorem bodyOf_extend [HasPullbacks C] {X Y : C} (h : IsFull T) (f : X ⟶ Y) (w : Over Y)
    (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    (bodyOf h f w g k).1 ≫ T.extend (T.extend w.hom (h.ty f)) (sliceTy h f g)
      = (pbIso h f w).hom ≫ k.left ≫ (sliceIso h f g).hom := by
  rw [← homOverEquivTm_symm_val, bodyOf, Equiv.symm_apply_apply, sliceHomEquiv_val]

/-- The term transposing a morphism out of the pullback: the abstraction of its body. -/
noncomputable def tmOf [HasPullbacks C] {X Y : C} (h : IsFull T) (P : NaturalPiStruct T)
    (f : X ⟶ Y) (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    T.Tm w.left (T.tySub w.hom (P.Pi (h.ty f) (sliceTy h f g))) :=
  tmCast (P.Pi_sub w.hom (h.ty f) (sliceTy h f g)).symm (P.lam (bodyOf h f w g k))

/-- **The transposition**: morphisms out of the pullback of `w` along `f` are morphisms into the
dependent product. -/
noncomputable def transpose [HasPullbacks C] {X Y : C} (h : IsFull T) (P : NaturalPiStruct T)
    (f : X ⟶ Y) (w : Over Y) (g : Over X) :
    ((Over.pullback f).obj w ⟶ g) ≃ (w ⟶ piObj h P f g) :=
  (sliceHomEquiv h f w g).trans <| (homOverEquivTm _ _).trans <|
    (P.toPiStruct.equiv _ _).trans <|
      (tmCastEquiv (P.Pi_sub w.hom (h.ty f) (sliceTy h f g)).symm).trans <|
        (homOverEquivTm w.hom (P.Pi (h.ty f) (sliceTy h f g))).symm.trans
          (overHomEquiv w (P.Pi (h.ty f) (sliceTy h f g)))

theorem transpose_left [HasPullbacks C] {X Y : C} (h : IsFull T) (P : NaturalPiStruct T)
    (f : X ⟶ Y) (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    (transpose h P f w g k).left
      = (tmOf h P f w g k).1 ≫ T.extend w.hom (P.Pi (h.ty f) (sliceTy h f g)) := rfl

/-! ### Naturality -/

/-- The presentation of `f` substituted along the two composable morphisms. -/
theorem tySub_hom_comp {X Y : C} (h : IsFull T) (f : X ⟶ Y) {w' w : Over Y} (t : w' ⟶ w) :
    T.tySub w'.hom (h.ty f) = T.tySub t.left (T.tySub w.hom (h.ty f)) := by
  have hw : t.left ≫ w.hom = w'.hom := Over.w t
  rw [← hw]
  exact T.tySub_comp w.hom t.left (h.ty f)

/-- The comparison of the two extended contexts of a morphism of the slice over `Y`. -/
noncomputable def extCompare {X Y : C} (h : IsFull T) (f : X ⟶ Y) {w' w : Over Y} (t : w' ⟶ w) :
    T.ext w'.left (T.tySub w'.hom (h.ty f)) ⟶ T.ext w.left (T.tySub w.hom (h.ty f)) :=
  eqToHom (congrArg (T.ext w'.left) (tySub_hom_comp h f t))
    ≫ T.extend t.left (T.tySub w.hom (h.ty f))

theorem extCompare_disp {X Y : C} (h : IsFull T) (f : X ⟶ Y) {w' w : Over Y} (t : w' ⟶ w) :
    extCompare h f t ≫ T.disp (T.tySub w.hom (h.ty f))
      = T.disp (T.tySub w'.hom (h.ty f)) ≫ t.left := by
  rw [extCompare, Category.assoc, (T.isPullback t.left (T.tySub w.hom (h.ty f))).w,
    ← Category.assoc, eqToHom_ext_disp]
  exact tySub_hom_comp h f t

/-- The comparison of extended contexts lies over the action of the base. -/
theorem extCompare_extend (co : ExtCoherent T) {X Y : C} (h : IsFull T) (f : X ⟶ Y)
    {w' w : Over Y} (t : w' ⟶ w) :
    extCompare h f t ≫ T.extend w.hom (h.ty f) = T.extend w'.hom (h.ty f) := by
  have hw : t.left ≫ w.hom = w'.hom := Over.w t
  have h1 := co.extend_comp w.hom t.left (h.ty f)
  have h2 := extend_congr (T := T) hw (h.ty f)
  have key : T.extend t.left (T.tySub w.hom (h.ty f)) ≫ T.extend w.hom (h.ty f)
      = eqToHom (congrArg (T.ext w'.left) (T.tySub_comp w.hom t.left (h.ty f))).symm
          ≫ T.extend (t.left ≫ w.hom) (h.ty f) := by
    rw [h1]
    simp
  rw [extCompare, Category.assoc, key, h2]
  simp

/-- **The comparison of extended contexts is the pullback of `t` along `f`.** -/
theorem pbIso_naturality [HasPullbacks C] (co : ExtCoherent T) {X Y : C} (h : IsFull T)
    (f : X ⟶ Y) {w' w : Over Y} (t : w' ⟶ w) :
    (pbIso h f w').hom ≫ ((Over.pullback f).map t).left
      = extCompare h f t ≫ (pbIso h f w).hom := by
  refine pullback.hom_ext ?_ ?_
  · have hl : ((Over.pullback f).map t).left ≫ Limits.pullback.fst w.hom f
        = Limits.pullback.fst w'.hom f ≫ t.left := by
      simp only [Over.pullback, Over.homMk_left]
      exact pullback.lift_fst _ _ _
    rw [Category.assoc, hl, ← Category.assoc, pbIso_hom_fst, Category.assoc, pbIso_hom_fst,
      extCompare_disp]
  · have hl : ((Over.pullback f).map t).left ≫ Limits.pullback.snd w.hom f
        = Limits.pullback.snd w'.hom f := by
      simp only [Over.pullback, Over.homMk_left]
      exact pullback.lift_snd _ _ _
    rw [Category.assoc, hl, pbIso_hom_snd, Category.assoc, pbIso_hom_snd, ← Category.assoc,
      extCompare_extend co]

/-- **The body of the transposition is natural**: the body over `w'` is the substitution of the
body over `w` along the comparison of the extended contexts. -/
theorem bodyOf_naturality [HasPullbacks C] (co : ExtCoherent T) {X Y : C} (h : IsFull T)
    (f : X ⟶ Y) {w' w : Over Y} (g : Over X) (t : w' ⟶ w) (k : (Over.pullback f).obj w ⟶ g)
    (hB : T.tySub (extCompare h f t) (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g))
      = T.tySub (T.extend w'.hom (h.ty f)) (sliceTy h f g)) :
    bodyOf h f w' g ((Over.pullback f).map t ≫ k)
      = tmCast hB (T.tmSub (extCompare h f t) (bodyOf h f w g k)) := by
  refine tm_eq_of_extend_eq _ _ ?_
  rw [bodyOf_extend, tmCast_tmSub_extend co (T.extend w.hom (h.ty f)) (extCompare h f t)
      (extCompare_extend co h f t) (sliceTy h f g) (bodyOf h f w g k) hB,
    bodyOf_extend, Over.comp_left]
  simp only [Category.assoc]
  rw [← Category.assoc (pbIso h f w').hom, pbIso_naturality co h f t]
  simp only [Category.assoc]

/-- **Abstraction of the body is natural**: the transposing term over `w'` is the substitution of
the transposing term over `w`.  This is the law `(λ b)[σ] = λ (b[σ⁺])` of a natural Π-structure,
transported along the comparison of the extended contexts. -/
theorem lam_bodyOf_naturality [HasPullbacks C] (co : ExtCoherent T) {X Y : C} (h : IsFull T)
    (P : NaturalPiStruct T) (f : X ⟶ Y) {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (k : (Over.pullback f).obj w ⟶ g)
    (Z : T.tySub t.left (P.Pi (T.tySub w.hom (h.ty f))
          (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g)))
      = P.Pi (T.tySub w'.hom (h.ty f)) (T.tySub (T.extend w'.hom (h.ty f)) (sliceTy h f g))) :
    P.lam (bodyOf h f w' g ((Over.pullback f).map t ≫ k))
      = tmCast Z (T.tmSub t.left (P.lam (bodyOf h f w g k))) := by
  have hA := tySub_hom_comp h f t
  have hB : T.tySub (extCompare h f t) (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g))
      = T.tySub (T.extend w'.hom (h.ty f)) (sliceTy h f g) := by
    rw [← T.tySub_comp, extCompare_extend co]
  have hy := co.tmSub_comp (T.extend t.left (T.tySub w.hom (h.ty f)))
    (eqToHom (congrArg (T.ext w'.left) hA)) (bodyOf h f w g k)
  have hlam := P.lam_sub t.left (A := T.tySub w.hom (h.ty f))
    (B := T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g)) (bodyOf h f w g k)
  have hPi := (Pi_congr P.toPiStruct hA
    (B := T.tySub (T.extend t.left (T.tySub w.hom (h.ty f)))
      (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g))) rfl).symm
  have hcast := NaturalPiStruct.lam_tmSub_eqToHom co P hA
    (T.tmSub (T.extend t.left (T.tySub w.hom (h.ty f))) (bodyOf h f w g k)) hPi
  rw [tmCast_eq_iff] at hy hcast
  rw [bodyOf_naturality co h f g t k hB, PiStruct.lam_tmCast P.toPiStruct hB]
  simp only [extCompare]
  rw [hy, PiStruct.lam_tmCast P.toPiStruct _, hcast, ← hlam]
  simp only [tmCast_trans]
  exact tmCast_trans _ _ _

/-- **The transposition is natural in the slice object over `Y`.** -/
theorem transpose_naturality [HasPullbacks C] (co : ExtCoherent T) {X Y : C} (h : IsFull T)
    (P : NaturalPiStruct T) (f : X ⟶ Y) {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (k : (Over.pullback f).obj w ⟶ g) :
    transpose h P f w' g ((Over.pullback f).map t ≫ k) = t ≫ transpose h P f w g k := by
  have hA := tySub_hom_comp h f t
  have hBcomp : T.tySub (extCompare h f t) (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g))
      = T.tySub (T.extend w'.hom (h.ty f)) (sliceTy h f g) := by
    rw [← T.tySub_comp, extCompare_extend co]
  have hB : T.tySub (eqToHom (congrArg (T.ext w'.left) hA))
        (T.tySub (T.extend t.left (T.tySub w.hom (h.ty f)))
          (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g)))
      = T.tySub (T.extend w'.hom (h.ty f)) (sliceTy h f g) :=
    (T.tySub_comp (T.extend t.left (T.tySub w.hom (h.ty f)))
      (eqToHom (congrArg (T.ext w'.left) hA))
      (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g))).symm.trans hBcomp
  have Z : T.tySub t.left (P.Pi (T.tySub w.hom (h.ty f))
        (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g)))
      = P.Pi (T.tySub w'.hom (h.ty f))
        (T.tySub (T.extend w'.hom (h.ty f)) (sliceTy h f g)) :=
    (P.Pi_sub t.left (T.tySub w.hom (h.ty f))
      (T.tySub (T.extend w.hom (h.ty f)) (sliceTy h f g))).trans (Pi_congr P.toPiStruct hA hB)
  have hPi' : T.tySub t.left (T.tySub w.hom (P.Pi (h.ty f) (sliceTy h f g)))
      = T.tySub w'.hom (P.Pi (h.ty f) (sliceTy h f g)) := by
    rw [← T.tySub_comp, Over.w t]
  have key : tmOf h P f w' g ((Over.pullback f).map t ≫ k)
      = tmCast hPi' (T.tmSub t.left (tmOf h P f w g k)) := by
    rw [tmOf, tmOf, lam_bodyOf_naturality co h P f g t k Z, tmSub_tmCast, tmCast_trans,
      tmCast_trans]
  refine Over.OverMorphism.ext ?_
  rw [transpose_left, Over.comp_left, transpose_left, key]
  exact tmCast_tmSub_extend co w.hom t.left (Over.w t) (P.Pi (h.ty f) (sliceTy h f g))
    (tmOf h P f w g k) hPi'

end LcccOfFull

end Cwa

/-! ### The dependent product of a full model -/

/-- **The category of contexts of a full model with a natural Π-structure is locally cartesian
closed.**  A morphism `f : X ⟶ Y` is presented by a type over `Y`, an object of the slice over `X`
by a type over the extended context, and the dependent product of the two is a type over `Y` whose
display map is the pushforward: morphisms into it are terms of the product
(`Cwa.homOverEquivTm`), which are terms of the body (`lam`/`app`), which are morphisms out of the
pullback.  Naturality of the resulting bijection is the law `(λ b)[σ] = λ (b[σ⁺])`. -/
@[reducible]
noncomputable def LcccPullbacks.ofIsFull {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}
    (co : Cwa.ExtCoherent T) (h : Cwa.IsFull T) (P : Cwa.NaturalPiStruct T) :
    @LcccPullbacks C _ (Cwa.hasPullbacks_of_isFull h) :=
  haveI := Cwa.hasPullbacks_of_isFull h
  { pushforward := fun f =>
      Adjunction.rightAdjointOfEquiv (F := Over.pullback f) (Cwa.LcccOfFull.transpose h P f)
        (fun _ _ g t k => Cwa.LcccOfFull.transpose_naturality co h P f g t k)
    adj := fun _ => Adjunction.adjunctionOfEquivRight _ _ }
