/-
**The dependent product of the strictified model.**

`Start/CwaLocalUniverse.lean` turns every category with pullbacks into a category with attributes
by presenting a type as a *local universe*: a morphism `proj : total ⟶ base` together with a
classifying map `cls : Γ ⟶ base`.  What that file leaves open is the Π-structure.

This module builds it, for a category which is locally cartesian closed in the sense that
substitution `Over.pullback f` has a right adjoint for every `f` (`LcccPullbacks`).  The point is
that a *presented* dependent product must have a base and a total space that do not mention the
context `Γ` at all — otherwise substitution could not be strict.  Both are therefore built
generically:

* the **base** `LuTy.piBase A B` is the pushforward along `A.proj` of the constant family over
  `A.total` with fibre `B.base`; by the adjunction, a map `Γ ⟶ piBase A B` over `A.base` is
  exactly a classifying map `Γ.A ⟶ B.base`, so this object classifies the *data* of a Π-type;
* over that base sit the generic copies `piGenA`, `piGenB` of `A` and `B`, and the **total space**
  `LuTy.piW` is the pushforward of the display map of `piGenB` along the display map of `piGenA`.

The classifying map of `Pi A B` is the transpose of the pair `(A.cls, B.cls)`, and because
transposition is natural in `Γ`, substitution is strict on the nose: stability of `Pi` under
substitution is `Adjunction.homEquiv_naturality_left` alone.

Main definitions:

* `LcccPullbacks` — a locally cartesian closed structure relative to the pullback functors of a
  category with pullbacks;
* `LuTy.piTy`, `LuTy.sigTy` — the dependent product and the dependent sum of two local universes.

Main results:

* `LuTy.piTy_sub` — the dependent product is strictly stable under substitution;
* `LuTy.tmEquivPi` — terms of `piTy A B` in `Γ` are exactly terms of `B` in `Γ.A`;
* `Cwa.piStructOfLccc` — **the local-universe category with attributes of a locally cartesian
  closed category has a Π-structure**, with both β and η;
* `Cwa.sigmaStructOfLccc` — and a Σ-structure, whose pairing isomorphism is the two-step context
  extension.
-/

import Start.CwaLocalUniverse
import Start.Lccc
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

/-- A **locally cartesian closed structure** on a category with pullbacks: a right adjoint to
every substitution functor `Over.pullback f`.  This is `CategoryTheory.LocallyCartesianClosed`
stated for the pullback functors that a category with pullbacks already has, which is what the
local-universe model of `Start/CwaLocalUniverse.lean` is built from. -/
class LcccPullbacks (C : Type u) [Category.{v} C] [HasPullbacks C] where
  /-- The dependent product (pushforward) along a morphism. -/
  pushforward : {X Y : C} → (X ⟶ Y) → (Over X ⥤ Over Y)
  /-- Substitution is left adjoint to the dependent product. -/
  adj : ∀ {X Y : C} (f : X ⟶ Y), Over.pullback f ⊣ pushforward f

namespace LuTy

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ### Terms as lifts -/

/-- A section of the display map of `A`: the terms of the category with attributes, spelled out
without reference to `Cwa.ofPullbacks`. -/
def Sect (Γ : C) (A : LuTy Γ) : Type v := {s : Γ ⟶ ext Γ A // s ≫ disp A = 𝟙 Γ}

/-- Terms in the sense of `Start/Cwa.lean` are sections of the display map. -/
def tmEquivSect {Γ : C} (A : LuTy Γ) : (Cwa.ofPullbacks C).Tm Γ A ≃ Sect Γ A := Equiv.refl _

/-- A term of the type presented by `A`, described as a lift of the classifying map through the
generic family. -/
def TmLift (Γ : C) (A : LuTy Γ) : Type v := {t : Γ ⟶ A.total // t ≫ A.proj = A.cls}

/-- Morphisms into a pullback with a prescribed first component. -/
noncomputable def pullbackLiftEquiv {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ X) :
    {h : W ⟶ pullback f g // h ≫ pullback.fst f g = p} ≃ {v : W ⟶ Y // p ≫ f = v ≫ g} where
  toFun := fun ⟨h, hh⟩ => ⟨h ≫ pullback.snd f g, by
    rw [← hh, Category.assoc, Category.assoc, pullback.condition]⟩
  invFun := fun ⟨v, hv⟩ => ⟨pullback.lift p v hv, pullback.lift_fst _ _ _⟩
  left_inv := fun ⟨h, hh⟩ => Subtype.ext (pullback.hom_ext
    (by rw [pullback.lift_fst, hh]) (by rw [pullback.lift_snd]))
  right_inv := fun ⟨v, hv⟩ => Subtype.ext (pullback.lift_snd _ _ _)

/-- Morphisms out of `Over.mk x` are morphisms of `C` commuting with the structure maps. -/
def overHomEquivLift {Z W : C} (x : W ⟶ Z) (Y : Over Z) :
    (Over.mk x ⟶ Y) ≃ {h : W ⟶ Y.left // h ≫ Y.hom = x} where
  toFun f := ⟨f.left, Over.w f⟩
  invFun h := Over.homMk h.1 h.2
  left_inv f := by ext; rfl
  right_inv h := rfl

/-- Sections of the display map are lifts through the generic family. -/
noncomputable def sectEquivLift {Γ : C} (A : LuTy Γ) : Sect Γ A ≃ TmLift Γ A where
  toFun := fun ⟨s, hs⟩ => ⟨s ≫ gen A, by
    calc (s ≫ gen A) ≫ A.proj = s ≫ gen A ≫ A.proj := Category.assoc _ _ _
      _ = s ≫ disp A ≫ A.cls := by rw [disp_cls]
      _ = (s ≫ disp A) ≫ A.cls := (Category.assoc _ _ _).symm
      _ = A.cls := by rw [hs, Category.id_comp]⟩
  invFun := fun ⟨t, ht⟩ => ⟨pullback.lift (𝟙 Γ) t (by rw [Category.id_comp, ht]),
    pullback.lift_fst _ _ _⟩
  left_inv := fun ⟨s, hs⟩ => Subtype.ext (pullback.hom_ext
    (by rw [pullback.lift_fst]; exact hs.symm) (by rw [pullback.lift_snd]; rfl))
  right_inv := fun ⟨t, ht⟩ => Subtype.ext (pullback.lift_snd _ _ _)

variable [HasBinaryProducts C] [LcccPullbacks C]

/-! ### The generic dependent product -/

/-- The **base of the dependent product**: the pushforward along the generic family of `A` of the
constant family with fibre `B.base`.  A map `Γ ⟶ piBase A B` over `A.base` is the same thing as a
classifying map `Γ.A ⟶ B.base`, so this object classifies the data of a Π-type. -/
noncomputable def piBase {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) : Over A.base :=
  (LcccPullbacks.pushforward A.proj).obj (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))

/-- The classifying map of `Pi A B`, as a morphism over `A.base`: the transpose of the pair
`(A.cls, B.cls)`. -/
noncomputable def piClsHom {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    Over.mk A.cls ⟶ piBase A B :=
  (LcccPullbacks.adj A.proj).homEquiv (Over.mk A.cls) _
    (Over.homMk (prod.lift (gen A) B.cls) (prod.lift_fst _ _))

/-- The classifying map of `Pi A B`. -/
noncomputable def piCls {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) : Γ ⟶ (piBase A B).left :=
  (piClsHom A B).left

@[simp] theorem piCls_comp {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    piCls A B ≫ (piBase A B).hom = A.cls :=
  Over.w (piClsHom A B)

/-- The generic copy of `A` over the base of the dependent product. -/
noncomputable def piGenA {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) : LuTy (piBase A B).left :=
  ⟨A.base, A.total, A.proj, (piBase A B).hom⟩

/-- The generic classifying map for `B`, obtained from the counit of the adjunction. -/
noncomputable def piGenCls {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ext (piBase A B).left (piGenA A B) ⟶ B.base :=
  ((LcccPullbacks.adj A.proj).counit.app
    (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))).left ≫ prod.snd

/-- The generic copy of `B` over the extended generic context. -/
noncomputable def piGenB {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    LuTy (ext (piBase A B).left (piGenA A B)) :=
  ⟨B.base, B.total, B.proj, piGenCls A B⟩

/-- The generic dependent product, as an object over the base: the pushforward of the display map
of the generic `B` along the display map of the generic `A`. -/
noncomputable def piW {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) : Over (piBase A B).left :=
  (LcccPullbacks.pushforward (disp (piGenA A B))).obj (Over.mk (disp (piGenB A B)))

/-- **The dependent product of two local universes.**  Its base and total space are generic — they
do not mention the context — so substitution, which acts on the classifying map alone, is
strict. -/
noncomputable def piTy {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) : LuTy Γ :=
  ⟨(piBase A B).left, (piW A B).left, (piW A B).hom, piCls A B⟩

/-! ### Stability under substitution -/

/-- The classifying map of the dependent product is natural in the context: this is the
transposition of the adjunction being natural on the left. -/
theorem piCls_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    piCls (sub σ A) (sub (extend σ A) B) = σ ≫ piCls A B := by
  have hpl : extend σ A ≫ prod.lift (gen A) B.cls =
      prod.lift (gen (sub σ A)) (extend σ A ≫ B.cls) :=
    (prod.comp_lift _ _ _).trans
      (congrArg (fun x => prod.lift x (extend σ A ≫ B.cls)) (extend_gen σ A))
  have hmap :
      (Over.pullback A.proj).map (Over.homMk σ rfl :
          (Over.mk (σ ≫ A.cls) : Over A.base) ⟶ Over.mk A.cls) ≫
        (Over.homMk (prod.lift (gen A) B.cls) (prod.lift_fst _ _) :
          (Over.pullback A.proj).obj (Over.mk A.cls) ⟶
            Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total)) =
      (Over.homMk (prod.lift (gen (sub σ A)) (extend σ A ≫ B.cls))
          (prod.lift_fst _ _) :
          (Over.pullback A.proj).obj (Over.mk (σ ≫ A.cls)) ⟶
            Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total)) :=
    Over.OverMorphism.ext hpl
  have key := (LcccPullbacks.adj A.proj).homEquiv_naturality_left
    (Over.homMk σ rfl : (Over.mk (σ ≫ A.cls) : Over A.base) ⟶ Over.mk A.cls)
    (Over.homMk (prod.lift (gen A) B.cls) (prod.lift_fst _ _) :
      (Over.pullback A.proj).obj (Over.mk A.cls) ⟶
        Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))
  rw [hmap] at key
  exact congrArg CategoryTheory.CommaMorphism.left key

/-- **Beck–Chevalley, strictly**: the dependent product commutes with substitution on the nose. -/
theorem piTy_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    sub σ (piTy A B) = piTy (sub σ A) (sub (extend σ A) B) :=
  congrArg
    (fun c => (⟨(piBase A B).left, (piW A B).left, (piW A B).hom, c⟩ : LuTy Δ))
    (piCls_sub σ A B).symm

/-! ### Terms of the dependent product -/

/-- The comparison map from the extended context into the generic extended context. -/
noncomputable def piGenMap {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ext Γ A ⟶ ext (piBase A B).left (piGenA A B) :=
  pullback.lift (disp A ≫ piCls A B) (gen A) (by
    change (disp A ≫ piCls A B) ≫ (piBase A B).hom = gen A ≫ A.proj
    rw [Category.assoc, piCls_comp, disp_cls])

@[simp] theorem piGenMap_disp {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    piGenMap A B ≫ disp (piGenA A B) = disp A ≫ piCls A B :=
  pullback.lift_fst _ _ _

@[simp] theorem piGenMap_gen {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    piGenMap A B ≫ gen (piGenA A B) = gen A :=
  pullback.lift_snd _ _ _

/-- The generic classifying map for `B`, pulled back along the transpose, is `B.cls`: the
computation rule of the adjunction. -/
theorem piGenMap_cls {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    piGenMap A B ≫ piGenCls A B = B.cls := by
  have h1 : ((LcccPullbacks.adj A.proj).homEquiv (Over.mk A.cls)
        (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))).symm (piClsHom A B) =
      (Over.pullback A.proj).map (piClsHom A B) ≫
        (LcccPullbacks.adj A.proj).counit.app
          (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total)) :=
    Adjunction.homEquiv_counit _ _ _ _
  have h2 : ((LcccPullbacks.adj A.proj).homEquiv (Over.mk A.cls)
        (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))).symm (piClsHom A B) =
      (Over.homMk (prod.lift (gen A) B.cls) (prod.lift_fst _ _) :
        (Over.pullback A.proj).obj (Over.mk A.cls) ⟶
          Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total)) :=
    Equiv.symm_apply_apply _ _
  have hL : piGenMap A B ≫
      ((LcccPullbacks.adj A.proj).counit.app
        (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))).left = prod.lift (gen A) B.cls :=
    congrArg CategoryTheory.CommaMorphism.left (h1.symm.trans h2)
  calc piGenMap A B ≫ piGenCls A B
      = (piGenMap A B ≫ ((LcccPullbacks.adj A.proj).counit.app
          (Over.mk (prod.fst : A.total ⨯ B.base ⟶ A.total))).left) ≫ prod.snd :=
        (Category.assoc _ _ _).symm
    _ = prod.lift (gen A) B.cls ≫ prod.snd := by rw [hL]
    _ = B.cls := prod.lift_snd _ _

theorem isPullback_piGenMap {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    IsPullback (disp A) (piGenMap A B) (piCls A B) (disp (piGenA A B)) := by
  refine (IsPullback.of_right ?_ (piGenMap_disp A B) (isPullback_gen (piGenA A B))).flip
  have e1 : piGenMap A B ≫ gen (piGenA A B) = gen A := piGenMap_gen A B
  have e2 : piCls A B ≫ (piGenA A B).cls = A.cls := piCls_comp A B
  rw [e1, e2]
  exact isPullback_gen A

/-- The identification of the extended context with the pullback of the generic extended
context. -/
noncomputable def piCtxIso {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ext Γ A ≅ pullback (piCls A B) (disp (piGenA A B)) :=
  (isPullback_piGenMap A B).isoPullback

theorem piCtxIso_hom_snd {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (piCtxIso A B).hom ≫ pullback.snd (piCls A B) (disp (piGenA A B)) = piGenMap A B :=
  IsPullback.isoPullback_hom_snd _

theorem piCtxIso_inv_piGenMap {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (piCtxIso A B).inv ≫ piGenMap A B = pullback.snd (piCls A B) (disp (piGenA A B)) :=
  calc (piCtxIso A B).inv ≫ piGenMap A B
      = (piCtxIso A B).inv ≫ (piCtxIso A B).hom ≫
        pullback.snd (piCls A B) (disp (piGenA A B)) := by rw [piCtxIso_hom_snd]
    _ = pullback.snd (piCls A B) (disp (piGenA A B)) := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Transporting terms along the identification of the extended context with the pullback of the
generic extended context. -/
noncomputable def piBodyEquiv {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    {v : pullback (piCls A B) (disp (piGenA A B)) ⟶ B.total //
        pullback.snd (piCls A B) (disp (piGenA A B)) ≫ piGenCls A B = v ≫ B.proj} ≃
      TmLift (ext Γ A) B where
  toFun v := ⟨(piCtxIso A B).hom ≫ v.1, by
    rw [Category.assoc, ← v.2, ← Category.assoc, piCtxIso_hom_snd, piGenMap_cls]⟩
  invFun t := ⟨(piCtxIso A B).inv ≫ t.1, by
    rw [Category.assoc, t.2, ← piCtxIso_inv_piGenMap, Category.assoc, piGenMap_cls]⟩
  left_inv v := Subtype.ext ((piCtxIso A B).inv_hom_id_assoc v.1)
  right_inv t := Subtype.ext ((piCtxIso A B).hom_inv_id_assoc t.1)

/-- **Terms of the dependent product are terms of the body**: the `lam`/`app` bijection. -/
noncomputable def tmEquivPi {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (Cwa.ofPullbacks C).Tm (ext Γ A) B ≃ (Cwa.ofPullbacks C).Tm Γ (piTy A B) :=
  (tmEquivSect B).trans <| (sectEquivLift B).trans <|
    (piBodyEquiv A B).symm.trans <|
    ((pullbackLiftEquiv (piGenCls A B) B.proj
        (pullback.snd (piCls A B) (disp (piGenA A B)))).symm.trans <|
      (overHomEquivLift (pullback.snd (piCls A B) (disp (piGenA A B)))
          (Over.mk (disp (piGenB A B)))).symm.trans <|
        ((LcccPullbacks.adj (disp (piGenA A B))).homEquiv (Over.mk (piCls A B))
            (Over.mk (disp (piGenB A B)))).trans <|
          (overHomEquivLift (piCls A B) (piW A B)).trans <|
            (sectEquivLift (piTy A B)).symm.trans (tmEquivSect (piTy A B)).symm)

/-! ### The dependent sum -/

/-- **The dependent sum of two local universes.**  Its base is the same object as for the
dependent product — it classifies the same data, a pair `(A, B)` — and its total space is the
two-step extension of the generic context. -/
noncomputable def sigTy {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) : LuTy Γ :=
  ⟨(piBase A B).left, ext (ext (piBase A B).left (piGenA A B)) (piGenB A B),
    disp (piGenB A B) ≫ disp (piGenA A B), piCls A B⟩

/-- The dependent sum is strictly stable under substitution, for the same reason as the dependent
product: only the classifying map depends on the context. -/
theorem sigTy_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    sub σ (sigTy A B) = sigTy (sub σ A) (sub (extend σ A) B) :=
  congrArg
    (fun c => (⟨(piBase A B).left, ext (ext (piBase A B).left (piGenA A B)) (piGenB A B),
      disp (piGenB A B) ≫ disp (piGenA A B), c⟩ : LuTy Δ))
    (piCls_sub σ A B).symm

/-- The comparison map from the two-step extension into the generic two-step extension. -/
noncomputable def sigGenMap {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ext (ext Γ A) B ⟶ ext (ext (piBase A B).left (piGenA A B)) (piGenB A B) :=
  pullback.lift (disp B ≫ piGenMap A B) (gen B) (by
    change (disp B ≫ piGenMap A B) ≫ piGenCls A B = gen B ≫ B.proj
    rw [Category.assoc, piGenMap_cls, disp_cls])

@[simp] theorem sigGenMap_disp {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    sigGenMap A B ≫ disp (piGenB A B) = disp B ≫ piGenMap A B :=
  pullback.lift_fst _ _ _

@[simp] theorem sigGenMap_gen {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    sigGenMap A B ≫ gen (piGenB A B) = gen B :=
  pullback.lift_snd _ _ _

theorem isPullback_sigGenMap {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    IsPullback (disp B) (sigGenMap A B) (piGenMap A B) (disp (piGenB A B)) := by
  refine (IsPullback.of_right ?_ (sigGenMap_disp A B) (isPullback_gen (piGenB A B))).flip
  have e1 : sigGenMap A B ≫ gen (piGenB A B) = gen B := sigGenMap_gen A B
  have e2 : piGenMap A B ≫ (piGenB A B).cls = B.cls := piGenMap_cls A B
  rw [e1, e2]
  exact isPullback_gen B

/-- **Pairing**: extending by `A` and then by `B` is extending by the dependent sum. -/
theorem isPullback_sigTy {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    IsPullback (disp B ≫ disp A) (sigGenMap A B) (piCls A B)
      (disp (piGenB A B) ≫ disp (piGenA A B)) :=
  (isPullback_sigGenMap A B).paste_horiz (isPullback_piGenMap A B)

/-- The pairing isomorphism of the dependent sum. -/
noncomputable def sigPair {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ext (ext Γ A) B ≅ ext Γ (sigTy A B) :=
  (isPullback_sigTy A B).isoPullback

@[simp] theorem sigPair_disp {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (sigPair A B).hom ≫ disp (sigTy A B) = disp B ≫ disp A :=
  IsPullback.isoPullback_hom_fst _

/-- **The Σ-structure of the local-universe model of a locally cartesian closed category.** -/
noncomputable def sigmaStruct : Cwa.SigmaStruct (Cwa.ofPullbacks C) where
  Sig := sigTy
  Sig_sub := sigTy_sub
  pair := sigPair
  pair_disp := sigPair_disp

/-- **The Π-structure of the local-universe model of a locally cartesian closed category.** -/
noncomputable def piStruct : Cwa.PiStruct (Cwa.ofPullbacks C) where
  Pi := piTy
  Pi_sub := piTy_sub
  lam := fun {_ A B} b => tmEquivPi A B b
  app := fun {_ A B} f => (tmEquivPi A B).symm f
  app_lam := fun {_ A B} b => (tmEquivPi A B).symm_apply_apply b
  lam_app := fun {_ A B} f => (tmEquivPi A B).apply_symm_apply f

end LuTy

/-- **A locally cartesian closed category models the dependent product.**  Types are local
universes, so substitution is strict, and the Π-type is the pushforward along the display map. -/
noncomputable def Cwa.piStructOfLccc (C : Type u) [Category.{v} C] [HasPullbacks C]
    [HasBinaryProducts C] [LcccPullbacks C] : Cwa.PiStruct (Cwa.ofPullbacks C) :=
  LuTy.piStruct

/-- **A locally cartesian closed category models the dependent sum as well**, on the same
strictified model, with the same base classifying the data of the type. -/
noncomputable def Cwa.sigmaStructOfLccc (C : Type u) [Category.{v} C] [HasPullbacks C]
    [HasBinaryProducts C] [LcccPullbacks C] : Cwa.SigmaStruct (Cwa.ofPullbacks C) :=
  LuTy.sigmaStruct

/-- A category that is locally cartesian closed in the sense of `Start/Lccc.lean` — with respect to
a possibly different choice of pullbacks — is one in the sense of `LcccPullbacks`: the two
pullback functors are both right adjoint to `Over.map f`, hence canonically isomorphic. -/
@[reducible]
noncomputable def LcccPullbacks.ofLocallyCartesianClosed (C : Type u) [Category.{v} C]
    [HasPullbacks C] [ChosenPullbacks C] [LocallyCartesianClosed C] : LcccPullbacks C where
  pushforward f := LocallyCartesianClosed.Pi f
  adj f := (LocallyCartesianClosed.pullbackPiAdj f).ofNatIsoLeft
    ((ChosenPullbacksAlong.mapPullbackAdj f).rightAdjointUniq (Over.mapPullbackAdj f))
