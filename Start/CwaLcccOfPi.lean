/-
**The converse of the strictification: a dependent product on the strictified model makes the
category locally cartesian closed.**

`Start/CwaPi.lean` turns a locally cartesian closed category into a model of dependent types: the
local-universe category with attributes `Cwa.ofPullbacks C` of a category with pullbacks carries a
Π-structure as soon as every pullback functor between slices has a right adjoint, and
`Start/CwaPiSub.lean` upgrades that structure to a `Cwa.NaturalPiStruct`.  This module proves the
**converse**, which is what an equivalence between the two sides needs: a natural Π-structure on
the strictified model is exactly a locally cartesian closed structure on `C`.

Main results:

* `LuTy.homOverEquivTm` — a morphism over `Γ` into the display map of a type is a term of the
  substituted type;
* `LcccPullbacks.ofNaturalPiStruct` — **a natural Π-structure on the strictified model of a
  category with pullbacks makes it locally cartesian closed**.
-/

import Start.CwaPiSub
import Start.CwaSubFunctorial
import Start.CwaUnivLocal

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace LuTy

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ### Morphisms over the base into a display map are terms -/

/-- **A morphism over `Γ` into the display map of a type is a term of the substituted type.**
Both are, by the universal property of the extension square, a map into the total space of the
presentation lying over the classifying map. -/
noncomputable def homOverEquivTm {Γ W : C} (w : W ⟶ Γ) (P : LuTy Γ) :
    {h : W ⟶ ext Γ P // h ≫ disp P = w} ≃ Cwa.Tm (Cwa.ofPullbacks C) W (sub w P) where
  toFun h := (CwaUniv.tmSectionEquiv (sub w P)).symm
    ⟨h.1 ≫ gen P, by
      change (h.1 ≫ gen P) ≫ P.proj = w ≫ P.cls
      rw [Category.assoc, ← disp_cls, ← Category.assoc, h.2]⟩
  invFun a := ⟨pullback.lift w (CwaUniv.codeOf a)
      (by exact ((CwaUniv.tmSectionEquiv (sub w P) a).2).symm),
    pullback.lift_fst _ _ _⟩
  left_inv h := by
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans h.2.symm
    · refine (pullback.lift_snd _ _ _).trans ?_
      change CwaUniv.codeOf ((CwaUniv.tmSectionEquiv (sub w P)).symm _) = h.1 ≫ gen P
      exact congrArg Subtype.val ((CwaUniv.tmSectionEquiv (sub w P)).apply_symm_apply _)
  right_inv a := by
    refine Eq.trans ?_ ((CwaUniv.tmSectionEquiv (sub w P)).symm_apply_apply a)
    refine congrArg (CwaUniv.tmSectionEquiv (sub w P)).symm (Subtype.ext ?_)
    exact pullback.lift_snd _ _ _

@[simp] theorem homOverEquivTm_symm_disp {Γ W : C} (w : W ⟶ Γ) (P : LuTy Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) W (sub w P)) :
    ((homOverEquivTm w P).symm a).1 ≫ disp P = w :=
  ((homOverEquivTm w P).symm a).2

@[simp] theorem homOverEquivTm_symm_gen {Γ W : C} (w : W ⟶ Γ) (P : LuTy Γ)
    (a : Cwa.Tm (Cwa.ofPullbacks C) W (sub w P)) :
    ((homOverEquivTm w P).symm a).1 ≫ gen P = CwaUniv.codeOf a :=
  pullback.lift_snd _ _ _

end LuTy

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, max u v} C}

/-- Transport of terms along an equality of types, as a bijection. -/
def tmCastEquiv {Γ : C} {A A' : T.Ty Γ} (h : A = A') : T.Tm Γ A ≃ T.Tm Γ A' where
  toFun := tmCast h
  invFun := tmCast h.symm
  left_inv a := by cases h; rfl
  right_inv a := by cases h; rfl

@[simp] theorem tmCastEquiv_apply {Γ : C} {A A' : T.Ty Γ} (h : A = A') (a : T.Tm Γ A) :
    tmCastEquiv (T := T) h a = tmCast h a := rfl

end Cwa

/-! ### A natural Π-structure is a locally cartesian closed structure -/

namespace LcccOfPi

open LuTy

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y)

/-- The type over `Y` presented by the morphism `f`: its display map is `f` itself.  This is
`LuTy.ofHom f`, spelled out so that its components reduce. -/
@[reducible] def tyOf : LuTy Y := ⟨Y, X, f, 𝟙 Y⟩

/-- The extension square of the substituted type is the pullback of `w` along `f`. -/
theorem isPullback_sub {W : C} (w : W ⟶ Y) :
    IsPullback (disp (sub w (tyOf f))) (gen (sub w (tyOf f))) w f := by
  have h := (isPullback_gen (sub w (tyOf f))).flip
  simpa only [tyOf, sub, Category.comp_id] using h

/-- The comparison of the extended context with the chosen pullback. -/
noncomputable def extIsoPullback {W : C} (w : W ⟶ Y) :
    ext W (sub w (tyOf f)) ≅ Limits.pullback w f :=
  (isPullback_sub f w).isoPullback

@[simp] theorem extIsoPullback_hom_fst {W : C} (w : W ⟶ Y) :
    (extIsoPullback f w).hom ≫ Limits.pullback.fst w f = disp (sub w (tyOf f)) :=
  IsPullback.isoPullback_hom_fst _

@[simp] theorem extIsoPullback_hom_snd {W : C} (w : W ⟶ Y) :
    (extIsoPullback f w).hom ≫ Limits.pullback.snd w f = gen (sub w (tyOf f)) :=
  IsPullback.isoPullback_hom_snd _

@[simp] theorem extIsoPullback_inv_snd {W : C} (w : W ⟶ Y) :
    (extIsoPullback f w).inv ≫ gen (sub w (tyOf f)) = Limits.pullback.snd w f := by
  rw [← extIsoPullback_hom_snd f w, Iso.inv_hom_id_assoc]

/-- The type over the extended context `Y.f` presented by an object of the slice over `X`. -/
@[reducible] noncomputable def sliceTy (g : Over X) : LuTy (ext Y (tyOf f)) :=
  ⟨X, g.left, g.hom, gen (tyOf f)⟩

variable (P : Cwa.NaturalPiStruct (Cwa.ofPullbacks C))

/-- **The candidate dependent product** of an object of the slice over `X`: the display map of the
dependent product of the two presented types. -/
noncomputable def piOver (g : Over X) : Over Y :=
  Over.mk (disp (P.Pi (tyOf f) (sliceTy f g)))

/-- A morphism of the slice over `X` out of the pullback of `w` is a map over `X` out of the
extended context. -/
noncomputable def pullbackHomEquiv (w : Over Y) (g : Over X) :
    ((Over.pullback f).obj w ⟶ g) ≃
      {k : ext w.left (sub w.hom (tyOf f)) ⟶ g.left // k ≫ g.hom = gen (sub w.hom (tyOf f))} where
  toFun k := ⟨(extIsoPullback f w.hom).hom ≫ k.left, by
    rw [Category.assoc, Over.w k]
    exact extIsoPullback_hom_snd f w.hom⟩
  invFun k := Over.homMk ((extIsoPullback f w.hom).inv ≫ k.1) (by
    rw [Category.assoc, k.2]
    exact extIsoPullback_inv_snd f w.hom)
  left_inv k := by
    ext
    simp
  right_inv k := by
    refine Subtype.ext ?_
    simp

/-- A map over `X` out of the extended context is a term of the presented type. -/
noncomputable def sliceTmEquiv (w : Over Y) (g : Over X) :
    {k : ext w.left (sub w.hom (tyOf f)) ⟶ g.left // k ≫ g.hom = gen (sub w.hom (tyOf f))}
      ≃ Cwa.Tm (Cwa.ofPullbacks C) (ext w.left (sub w.hom (tyOf f)))
          (sub (extend w.hom (tyOf f)) (sliceTy f g)) :=
  (Equiv.subtypeEquivRight (fun k => by
      change k ≫ g.hom = gen (sub w.hom (tyOf f)) ↔
        k ≫ g.hom = extend w.hom (tyOf f) ≫ gen (tyOf f)
      rw [extend_gen])).trans
    (CwaUniv.tmSectionEquiv (sub (extend w.hom (tyOf f)) (sliceTy f g))).symm

/-- Abstraction and application are mutually inverse, so terms of a dependent product are terms of
its body. -/
noncomputable def lamEquiv {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    Cwa.Tm (Cwa.ofPullbacks C) (ext Γ A) B ≃ Cwa.Tm (Cwa.ofPullbacks C) Γ (P.Pi A B) where
  toFun := P.lam
  invFun := P.app
  left_inv := P.app_lam
  right_inv := P.lam_app

/-- A term of the dependent product over `Y` is a morphism over `Y` into its display map. -/
noncomputable def piOverHomEquiv (w : Over Y) (g : Over X) :
    Cwa.Tm (Cwa.ofPullbacks C) w.left (sub w.hom (P.Pi (tyOf f) (sliceTy f g)))
      ≃ (w ⟶ piOver f P g) :=
  (LuTy.homOverEquivTm w.hom (P.Pi (tyOf f) (sliceTy f g))).symm.trans
    { toFun := fun h => Over.homMk h.1 h.2
      invFun := fun h => ⟨h.left, Over.w h⟩
      left_inv := fun h => Subtype.ext rfl
      right_inv := fun h => by ext; rfl }

/-- **The transposition**: morphisms out of the pullback of `w` along `f` are morphisms into the
dependent product. -/
noncomputable def transpose (w : Over Y) (g : Over X) :
    ((Over.pullback f).obj w ⟶ g) ≃ (w ⟶ piOver f P g) :=
  (pullbackHomEquiv f w g).trans <| (sliceTmEquiv f w g).trans <|
    (lamEquiv P (sub w.hom (tyOf f)) (sub (extend w.hom (tyOf f)) (sliceTy f g))).trans <|
      (Cwa.tmCastEquiv (P.Pi_sub w.hom (tyOf f) (sliceTy f g)).symm).trans
        (piOverHomEquiv f P w g)

/-! ### Naturality of the transposition -/

/-- The body of the transposition: the map over `X` read as a term of the presented type. -/
noncomputable def bodyOf (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    Cwa.Tm (Cwa.ofPullbacks C) (ext w.left (sub w.hom (tyOf f)))
      (sub (extend w.hom (tyOf f)) (sliceTy f g)) :=
  sliceTmEquiv f w g (pullbackHomEquiv f w g k)

theorem codeOf_bodyOf (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    CwaUniv.codeOf (bodyOf f w g k) = (extIsoPullback f w.hom).hom ≫ k.left :=
  congrArg Subtype.val
    ((CwaUniv.tmSectionEquiv (sub (extend w.hom (tyOf f)) (sliceTy f g))).apply_symm_apply _)

/-- The term transposing a map over `X`: the abstraction of its body. -/
noncomputable def tmOf (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    Cwa.Tm (Cwa.ofPullbacks C) w.left (sub w.hom (P.Pi (tyOf f) (sliceTy f g))) :=
  Cwa.tmCast (P.Pi_sub w.hom (tyOf f) (sliceTy f g)).symm (P.lam (bodyOf f w g k))

theorem transpose_apply (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    transpose f P w g k = piOverHomEquiv f P w g (tmOf f P w g k) := rfl

/-- Abstraction commutes with transport of the body along an equality of types. -/
theorem lam_tmCast {Γ : C} {A : LuTy Γ} {B B' : LuTy (ext Γ A)} (h : B = B')
    (b : Cwa.Tm (Cwa.ofPullbacks C) (ext Γ A) B) :
    P.lam (Cwa.tmCast h b) = Cwa.tmCast (congrArg (P.Pi A) h) (P.lam b) := by
  cases h
  rfl

/-- Abstraction commutes with transport of the domain along an equality of types. -/
theorem lam_tmSub_eqToHom {Γ : C} {A A' : LuTy Γ} (hA : A' = A) {B : LuTy (ext Γ A)}
    (x : Cwa.Tm (Cwa.ofPullbacks C) (ext Γ A) B)
    (hPi : P.Pi A' (sub (eqToHom (congrArg (ext Γ) hA)) B) = P.Pi A B) :
    Cwa.tmCast hPi (P.lam (Cwa.tmSub (T := Cwa.ofPullbacks C) (eqToHom (congrArg (ext Γ) hA)) x))
      = P.lam x := by
  cases hA
  change Cwa.tmCast hPi (P.lam (Cwa.tmSub (T := Cwa.ofPullbacks C) (𝟙 (ext Γ A)) x)) = P.lam x
  have h2 := (Cwa.extCoherent_ofPullbacks C).tmSub_id (T := Cwa.ofPullbacks C) x
  have h3 : Cwa.tmSub (T := Cwa.ofPullbacks C) (𝟙 (ext Γ A)) x
      = Cwa.tmCast (sub_id B).symm x := by
    rw [Cwa.tmCast_eq_iff] at h2
    exact h2
  rw [h3]
  have hstep := Cwa.tmCast_trans (T := Cwa.ofPullbacks C)
    (congrArg (P.Pi A) (sub_id B).symm) hPi (P.lam x)
  exact (congrArg (Cwa.tmCast hPi) (lam_tmCast P (sub_id B).symm x)).trans (hstep.trans rfl)

/-- The dependent product is congruent: equal domains and bodies give equal products. -/
theorem Pi_congr {Γ : C} {A A' : LuTy Γ} (hA : A' = A) {B : LuTy (ext Γ A)} {B' : LuTy (ext Γ A')}
    (hB : sub (eqToHom (congrArg (ext Γ) hA)) B = B') : P.Pi A B = P.Pi A' B' := by
  cases hA
  have hBB : B' = B := hB.symm.trans (sub_id B)
  rw [hBB]

variable {f}

/-- The comparison of the two extended contexts of a morphism of the slice over `Y`. -/
noncomputable def extCompare {w' w : Over Y} (t : w' ⟶ w)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f))) :
    ext w'.left (sub w'.hom (tyOf f)) ⟶ ext w.left (sub w.hom (tyOf f)) :=
  eqToHom (congrArg (ext w'.left) hA) ≫ extend t.left (sub w.hom (tyOf f))

omit [HasPullbacks C] in
theorem sub_hom_comp {w' w : Over Y} (t : w' ⟶ w) :
    sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f)) := by
  rw [← Over.w t]
  exact sub_comp w.hom t.left (tyOf f)

@[simp] theorem extCompare_disp {w' w : Over Y} (t : w' ⟶ w)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f))) :
    extCompare t hA ≫ disp (sub w.hom (tyOf f)) = disp (sub w'.hom (tyOf f)) ≫ t.left := by
  rw [extCompare, Category.assoc, extend_disp, Cwa.eqToHom_lu_disp_assoc]
  exact hA

@[simp] theorem extCompare_gen {w' w : Over Y} (t : w' ⟶ w)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f))) :
    extCompare t hA ≫ gen (sub w.hom (tyOf f)) = gen (sub w'.hom (tyOf f)) := by
  rw [extCompare, Category.assoc, extend_gen, Cwa.eqToHom_lu_gen,
    Subsingleton.elim (congrArg LuTy.total hA) rfl, eqToHom_refl, Category.comp_id]
  exact hA

/-- The comparison of extended contexts is the pullback of `t` along `f`. -/
theorem extIsoPullback_naturality {w' w : Over Y} (t : w' ⟶ w)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f))) :
    (extIsoPullback f w'.hom).hom ≫ ((Over.pullback f).map t).left
      = extCompare t hA ≫ (extIsoPullback f w.hom).hom := by
  refine pullback.hom_ext ?_ ?_
  · have hl : ((Over.pullback f).map t).left ≫ Limits.pullback.fst w.hom f
        = Limits.pullback.fst w'.hom f ≫ t.left := by
      simp only [Over.pullback, Over.homMk_left]
      exact pullback.lift_fst _ _ _
    rw [Category.assoc, hl, ← Category.assoc, extIsoPullback_hom_fst, Category.assoc,
      extIsoPullback_hom_fst, extCompare_disp]
  · have hl : ((Over.pullback f).map t).left ≫ Limits.pullback.snd w.hom f
        = Limits.pullback.snd w'.hom f := by
      simp only [Over.pullback, Over.homMk_left]
      exact pullback.lift_snd _ _ _
    rw [Category.assoc, hl, extIsoPullback_hom_snd, Category.assoc, extIsoPullback_hom_snd,
      extCompare_gen]

/-- A term of the strictified model is determined by its code. -/
theorem codeOf_injective {Γ : C} {A : LuTy Γ} {a b : Cwa.Tm (Cwa.ofPullbacks C) Γ A}
    (h : CwaUniv.codeOf a = CwaUniv.codeOf b) : a = b :=
  code_injective h

/-- **The body of the transposition is natural**: the body over `w'` is the substitution of the
body over `w` along the comparison of the extended contexts. -/
theorem bodyOf_naturality {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (k : (Over.pullback f).obj w ⟶ g)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f)))
    (hB : sub (extCompare t hA) (sub (extend w.hom (tyOf f)) (sliceTy f g))
      = sub (extend w'.hom (tyOf f)) (sliceTy f g)) :
    bodyOf f w' g ((Over.pullback f).map t ≫ k)
      = Cwa.tmCast hB (Cwa.tmSub (T := Cwa.ofPullbacks C) (extCompare t hA) (bodyOf f w g k)) := by
  refine codeOf_injective ?_
  have h1 : CwaUniv.codeOf (Cwa.tmCast hB
        (Cwa.tmSub (T := Cwa.ofPullbacks C) (extCompare t hA) (bodyOf f w g k)))
      = extCompare t hA ≫ CwaUniv.codeOf (bodyOf f w g k) := by
    rw [CwaUniv.codeOf_tmCast, CwaUniv.codeOf_tmSub,
      Subsingleton.elim (congrArg LuTy.total hB) rfl, eqToHom_refl, Category.comp_id]
  rw [h1, codeOf_bodyOf, codeOf_bodyOf, Over.comp_left, ← Category.assoc,
    extIsoPullback_naturality t hA, Category.assoc]

/-- The comparison of extended contexts lies over the extension of the base. -/
theorem extCompare_extend {w' w : Over Y} (t : w' ⟶ w)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f))) :
    extCompare t hA ≫ extend w.hom (tyOf f) = extend w'.hom (tyOf f) := by
  refine ext_hom_ext ?_ ?_
  · have h1 : extend w.hom (tyOf f) ≫ disp (tyOf f) = disp (sub w.hom (tyOf f)) ≫ w.hom :=
      extend_disp w.hom (tyOf f)
    rw [Category.assoc, h1, ← Category.assoc, extCompare_disp, Category.assoc, Over.w t,
      extend_disp]
  · rw [Category.assoc, extend_gen, extCompare_gen, extend_gen]

/-- The body of the transposition is stable under the comparison of extended contexts. -/
theorem sub_extCompare_sliceTy {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (hA : sub w'.hom (tyOf f) = sub t.left (sub w.hom (tyOf f))) :
    sub (extCompare t hA) (sub (extend w.hom (tyOf f)) (sliceTy f g))
      = sub (extend w'.hom (tyOf f)) (sliceTy f g) := by
  rw [← sub_comp, extCompare_extend]

/-- **Abstraction of the body is natural**: the transposing term over `w'` is the substitution of
the transposing term over `w`.  This is the law `(λ b)[σ] = λ (b[σ⁺])` of `Cwa.NaturalPiStruct`,
transported along the comparison of the extended contexts. -/
theorem lam_bodyOf_naturality {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (k : (Over.pullback f).obj w ⟶ g)
    (Z : sub t.left (P.Pi (sub w.hom (tyOf f)) (sub (extend w.hom (tyOf f)) (sliceTy f g)))
      = P.Pi (sub w'.hom (tyOf f)) (sub (extend w'.hom (tyOf f)) (sliceTy f g))) :
    P.lam (bodyOf f w' g ((Over.pullback f).map t ≫ k))
      = Cwa.tmCast Z (Cwa.tmSub (T := Cwa.ofPullbacks C) t.left (P.lam (bodyOf f w g k))) := by
  have hA := sub_hom_comp (f := f) t
  have hB := sub_extCompare_sliceTy (f := f) g t hA
  have hy := (Cwa.extCoherent_ofPullbacks C).tmSub_comp
    (extend t.left (sub w.hom (tyOf f))) (eqToHom (congrArg (ext w'.left) hA))
    (bodyOf f w g k)
  have hlam := P.lam_sub t.left (A := sub w.hom (tyOf f))
    (B := sub (extend w.hom (tyOf f)) (sliceTy f g)) (bodyOf f w g k)
  have hPi := (Pi_congr P hA (B := sub (extend t.left (sub w.hom (tyOf f)))
    (sub (extend w.hom (tyOf f)) (sliceTy f g))) rfl).symm
  have hcast := lam_tmSub_eqToHom P hA
    (Cwa.tmSub (T := Cwa.ofPullbacks C) (extend t.left (sub w.hom (tyOf f))) (bodyOf f w g k)) hPi
  rw [Cwa.tmCast_eq_iff] at hy hcast
  rw [bodyOf_naturality (f := f) g t k hA hB, lam_tmCast P hB]
  simp only [extCompare]
  rw [hy, lam_tmCast P _, hcast, ← hlam]
  simp only [Cwa.tmCast_trans]
  exact Cwa.tmCast_trans _ _ _

/-- **The code of the transposing term is natural.** -/
theorem codeOf_tmOf_naturality {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (k : (Over.pullback f).obj w ⟶ g) :
    CwaUniv.codeOf (tmOf f P w' g ((Over.pullback f).map t ≫ k))
      = t.left ≫ CwaUniv.codeOf (tmOf f P w g k) := by
  have hA := sub_hom_comp (f := f) t
  have hB : sub (eqToHom (congrArg (ext w'.left) hA))
      (sub (extend t.left (sub w.hom (tyOf f))) (sub (extend w.hom (tyOf f)) (sliceTy f g)))
      = sub (extend w'.hom (tyOf f)) (sliceTy f g) :=
    (sub_comp (extend t.left (sub w.hom (tyOf f))) (eqToHom (congrArg (ext w'.left) hA))
      (sub (extend w.hom (tyOf f)) (sliceTy f g))).symm.trans
        (sub_extCompare_sliceTy (f := f) g t hA)
  have Z : sub t.left (P.Pi (sub w.hom (tyOf f)) (sub (extend w.hom (tyOf f)) (sliceTy f g)))
      = P.Pi (sub w'.hom (tyOf f)) (sub (extend w'.hom (tyOf f)) (sliceTy f g)) :=
    (P.Pi_sub t.left (sub w.hom (tyOf f)) (sub (extend w.hom (tyOf f)) (sliceTy f g))).trans
      (Pi_congr P hA hB)
  rw [tmOf, tmOf, CwaUniv.codeOf_tmCast, CwaUniv.codeOf_tmCast,
    lam_bodyOf_naturality P g t k Z, CwaUniv.codeOf_tmCast, CwaUniv.codeOf_tmSub,
    Category.assoc, Category.assoc, eqToHom_trans]

theorem transpose_left (w : Over Y) (g : Over X) (k : (Over.pullback f).obj w ⟶ g) :
    (transpose f P w g k).left
      = ((LuTy.homOverEquivTm w.hom (P.Pi (tyOf f) (sliceTy f g))).symm
          (tmOf f P w g k)).1 := rfl

/-- **The transposition is natural in the slice object over `Y`.** -/
theorem transpose_naturality {w' w : Over Y} (g : Over X) (t : w' ⟶ w)
    (k : (Over.pullback f).obj w ⟶ g) :
    transpose f P w' g ((Over.pullback f).map t ≫ k) = t ≫ transpose f P w g k := by
  have hdispL : (transpose f P w' g ((Over.pullback f).map t ≫ k)).left
      ≫ disp (P.Pi (tyOf f) (sliceTy f g)) = w'.hom :=
    homOverEquivTm_symm_disp _ _ _
  have hgenL : (transpose f P w' g ((Over.pullback f).map t ≫ k)).left
      ≫ gen (P.Pi (tyOf f) (sliceTy f g))
      = CwaUniv.codeOf (tmOf f P w' g ((Over.pullback f).map t ≫ k)) :=
    homOverEquivTm_symm_gen _ _ _
  have hdispR : (t ≫ transpose f P w g k).left ≫ disp (P.Pi (tyOf f) (sliceTy f g)) = w'.hom := by
    rw [Over.comp_left]
    exact (Category.assoc t.left _ _).trans
      ((congrArg (fun x => t.left ≫ x)
        (homOverEquivTm_symm_disp w.hom (P.Pi (tyOf f) (sliceTy f g))
          (tmOf f P w g k))).trans (Over.w t))
  have hgenR : (t ≫ transpose f P w g k).left ≫ gen (P.Pi (tyOf f) (sliceTy f g))
      = CwaUniv.codeOf (tmOf f P w' g ((Over.pullback f).map t ≫ k)) := by
    rw [Over.comp_left]
    exact (Category.assoc t.left _ _).trans
      ((congrArg (fun x => t.left ≫ x)
        (homOverEquivTm_symm_gen w.hom (P.Pi (tyOf f) (sliceTy f g))
          (tmOf f P w g k))).trans (codeOf_tmOf_naturality P g t k).symm)
  ext
  exact ext_hom_ext (hdispL.trans hdispR.symm) (hgenL.trans hgenR.symm)

end LcccOfPi

/-! ### The converse of the strictification -/

/-- **A natural Π-structure on the strictified model of a category with pullbacks makes it
locally cartesian closed.**  A morphism `f : X ⟶ Y` is a type over `Y`, an object of the slice
over `X` is a type over the extended context, and the dependent product of the two is a type over
`Y` whose display map is the pushforward: morphisms into it are terms of the product
(`LuTy.homOverEquivTm`), which are terms of the body (`lam`/`app`), which are morphisms out of the
pullback.  Naturality of the resulting bijection is the law `(λ b)[σ] = λ (b[σ⁺])`. -/
@[reducible]
noncomputable def LcccPullbacks.ofNaturalPiStruct {C : Type u} [Category.{v} C] [HasPullbacks C]
    (P : Cwa.NaturalPiStruct (Cwa.ofPullbacks C)) : LcccPullbacks C where
  pushforward f :=
    Adjunction.rightAdjointOfEquiv (F := Over.pullback f) (LcccOfPi.transpose f P)
      (fun _ _ g t k => LcccOfPi.transpose_naturality P g t k)
  adj _ := Adjunction.adjunctionOfEquivRight _ _

/-- **The dependent product of the strictified model and local cartesian closure are the same
structure.**  One direction is `Cwa.naturalPiStructOfLccc`, the other
`LcccPullbacks.ofNaturalPiStruct`. -/
theorem Cwa.nonempty_naturalPiStruct_ofPullbacks_iff (C : Type u) [Category.{v} C]
    [HasPullbacks C] [HasBinaryProducts C] :
    Nonempty (Cwa.NaturalPiStruct (Cwa.ofPullbacks C)) ↔ Nonempty (LcccPullbacks C) :=
  ⟨fun ⟨P⟩ => ⟨LcccPullbacks.ofNaturalPiStruct P⟩,
    fun ⟨L⟩ => ⟨@Cwa.naturalPiStructOfLccc C _ _ _ L⟩⟩
