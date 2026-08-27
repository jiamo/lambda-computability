/-
**Abstraction and application of the strictified model commute with substitution.**

`Start/CwaPi.lean` equips the local-universe model of a locally cartesian closed category with a
dependent product: the type former `LuTy.piTy` is strictly stable under substitution, and terms of
`piTy A B` in `Γ` correspond bijectively to terms of `B` in `Γ.A`.  What that file does not record
is that the bijection itself is *natural*: the interface `Cwa.PiStruct` of `Start/Cwa.lean`
demands stability of the type former only.  Naturality is what makes the model sound for a
calculus with substitution, since it is the equation `(λ b)[σ] = λ (b[σ⁺])`.

This module proves it.  A term is compared through its **code**, the composite of its section with
the generic element of the local universe; a term is determined by its code (`LuTy.code_injective`),
substitution acts on codes by precomposition (`LuTy.code_tmSub`), and the codes of `lam` and `app`
are unchanged by substitution up to that precomposition.

The proof is the naturality of the adjunction transposition on the left, exactly as for
`LuTy.piCls_sub`: all the *generic* data of the dependent product (`piBase`, `piGenA`, `piGenB`,
`piW`) depends on the local universes alone and not on their classifying maps, so it is literally
unchanged by substitution; only the classifying map moves.

Main results:

* `LuTy.code_lam_sub` — abstraction commutes with substitution;
* `LuTy.lam_sub` — the same equation written with the transport along `LuTy.piTy_sub`;
* `LuTy.code_app_sub`, `LuTy.code_app_tmSub` — application commutes with substitution;
* `LuTy.extend_sigGenMap` — the pairing of the dependent sum is natural in the context too;
* `Cwa.naturalPiStructOfLccc` — the resulting `Cwa.NaturalPiStruct` of the strictified model.
-/

import Start.CwaPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace LuTy

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ### Codes of terms -/

/-- The **code** of a term: the composite of its section with the generic element of the local
universe presenting its type.  A term is exactly a lift of the classifying map through the generic
family, and the code is that lift. -/
noncomputable def code {Γ : C} {A : LuTy Γ} (a : Sect Γ A) : Γ ⟶ A.total := a.1 ≫ gen A

theorem code_proj {Γ : C} {A : LuTy Γ} (a : Sect Γ A) : code a ≫ A.proj = A.cls :=
  calc code a ≫ A.proj = a.1 ≫ gen A ≫ A.proj := Category.assoc _ _ _
    _ = a.1 ≫ disp A ≫ A.cls := by rw [disp_cls]
    _ = (a.1 ≫ disp A) ≫ A.cls := (Category.assoc _ _ _).symm
    _ = A.cls := by rw [a.2, Category.id_comp]

/-- Maps into an extended context are determined by their two components. -/
theorem ext_hom_ext {X : C} {G : LuTy X} {W : C} {f g : W ⟶ ext X G}
    (h₁ : f ≫ disp G = g ≫ disp G) (h₂ : f ≫ gen G = g ≫ gen G) : f = g :=
  pullback.hom_ext h₁ h₂

/-- A term is determined by its code. -/
theorem code_injective {Γ : C} {A : LuTy Γ} {a b : Sect Γ A} (h : code a = code b) : a = b :=
  Subtype.ext (ext_hom_ext (by rw [a.2, b.2]) h)

/-- Substitution of sections, described directly by its code. -/
noncomputable def subSect {Γ Δ : C} (σ : Δ ⟶ Γ) {A : LuTy Γ} (a : Sect Γ A) : Sect Δ (sub σ A) :=
  ⟨pullback.lift (𝟙 Δ) (σ ≫ code a)
      ((Category.id_comp (σ ≫ A.cls)).trans
        (((Category.assoc σ (code a) A.proj).trans
          (congrArg (fun x => σ ≫ x) (code_proj a))).symm)),
    pullback.lift_fst _ _ _⟩

@[simp] theorem code_subSect {Γ Δ : C} (σ : Δ ⟶ Γ) {A : LuTy Γ} (a : Sect Γ A) :
    code (subSect σ a) = σ ≫ code a :=
  pullback.lift_snd _ _ _

/-- A map into the substituted extended context lying over the extension map has the substituted
code. -/
theorem code_of_lift {Γ Δ : C} (σ : Δ ⟶ Γ) {A : LuTy Γ} (a : Sect Γ A)
    (s : Δ ⟶ ext Δ (sub σ A)) (hs : s ≫ extend σ A = σ ≫ a.1) :
    s ≫ gen (sub σ A) = σ ≫ code a :=
  (congrArg (fun x => s ≫ x) (extend_gen σ A).symm).trans
    (((Category.assoc s (extend σ A) (gen A)).symm.trans
      (congrArg (fun x => x ≫ gen A) hs)).trans (Category.assoc σ a.1 (gen A)))

/-- The substitution of terms of `Start/Cwa.lean` is substitution of codes. -/
theorem tmSub_eq_subSect {Γ Δ : C} (σ : Δ ⟶ Γ) {A : LuTy Γ} (a : Sect Γ A) :
    (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a : Sect Δ (sub σ A)) = subSect σ a :=
  Subtype.ext (ext_hom_ext
    ((Cwa.tmSub (T := Cwa.ofPullbacks C) σ a).2.trans (subSect σ a).2.symm)
    ((code_of_lift σ a _ ((isPullback_extend σ A).lift_fst _ _ _)).trans
      (pullback.lift_snd _ _ _).symm))

/-- The code of a substituted term is the code precomposed with the substitution. -/
theorem code_tmSub {Γ Δ : C} (σ : Δ ⟶ Γ) {A : LuTy Γ} (a : Sect Γ A) :
    code (Cwa.tmSub (T := Cwa.ofPullbacks C) σ a : Sect Δ (sub σ A)) = σ ≫ code a :=
  (congrArg code (tmSub_eq_subSect σ a)).trans (code_subSect σ a)

/-- The code of a term written as a lift. -/
theorem code_sectEquivLift_symm {Γ : C} (A : LuTy Γ) (t : TmLift Γ A) :
    code ((sectEquivLift A).symm t) = t.1 :=
  pullback.lift_snd _ _ _

/-- Codes are unchanged by the transport along an equality of types. -/
theorem code_tmCast_heq {Γ : C} {X Y : LuTy Γ} (h : X = Y) (a : Sect Γ X) :
    HEq (code (Cwa.tmCast (T := Cwa.ofPullbacks C) h a)) (code a) := by
  cases h; rfl

/-! ### Naturality of the dependent product -/

variable [HasBinaryProducts C] [LcccPullbacks C]

/-- The comparison map into the generic extended context is natural in the context. -/
theorem extend_piGenMap {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    extend σ A ≫ piGenMap A B = piGenMap (sub σ A) (sub (extend σ A) B) :=
  ext_hom_ext
    ((Category.assoc (extend σ A) (piGenMap A B) (disp (piGenA A B))).trans
      ((congrArg (fun x => extend σ A ≫ x) (piGenMap_disp A B)).trans
        ((Category.assoc (extend σ A) (disp A) (piCls A B)).symm.trans
          ((congrArg (fun x => x ≫ piCls A B) (extend_disp σ A)).trans
            ((Category.assoc (disp (sub σ A)) σ (piCls A B)).trans
              ((congrArg (fun x => disp (sub σ A) ≫ x) (piCls_sub σ A B).symm).trans
                (piGenMap_disp (sub σ A) (sub (extend σ A) B)).symm))))))
    ((Category.assoc (extend σ A) (piGenMap A B) (gen (piGenA A B))).trans
      ((congrArg (fun x => extend σ A ≫ x) (piGenMap_gen A B)).trans
        ((extend_gen σ A).trans (piGenMap_gen (sub σ A) (sub (extend σ A) B)).symm)))

/-- A term of the body, read as a morphism into the generic dependent product over the extended
generic context. -/
noncomputable def piBodyMor {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) (b : TmLift (ext Γ A) B) :
    (Over.pullback (disp (piGenA A B))).obj (Over.mk (piCls A B)) ⟶
      Over.mk (disp (piGenB A B)) :=
  (overHomEquivLift (pullback.snd (piCls A B) (disp (piGenA A B)))
      (Over.mk (disp (piGenB A B)))).symm
    ((pullbackLiftEquiv (piGenCls A B) B.proj
        (pullback.snd (piCls A B) (disp (piGenA A B)))).symm ((piBodyEquiv A B).symm b))

theorem piBodyMor_left_disp {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) (b : TmLift (ext Γ A) B) :
    (piBodyMor A B b).left ≫ disp (piGenB A B) =
      pullback.snd (piCls A B) (disp (piGenA A B)) :=
  pullback.lift_fst _ _ _

theorem piBodyMor_left_gen {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) (b : TmLift (ext Γ A) B) :
    (piBodyMor A B b).left ≫ gen (piGenB A B) = (piCtxIso A B).inv ≫ b.1 :=
  pullback.lift_snd _ _ _

/-- The transpose of a term of the body, as a lift into the total space of the dependent
product. -/
noncomputable def piTranspose {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) (b : TmLift (ext Γ A) B) :
    TmLift Γ (piTy A B) :=
  overHomEquivLift (piCls A B) (piW A B)
    ((LcccPullbacks.adj (disp (piGenA A B))).homEquiv (Over.mk (piCls A B))
      (Over.mk (disp (piGenB A B))) (piBodyMor A B b))

theorem code_tmEquivPi {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) (b : Sect (ext Γ A) B) :
    code (tmEquivPi A B b) = (piTranspose A B (sectEquivLift B b)).1 :=
  code_sectEquivLift_symm (piTy A B) (piTranspose A B (sectEquivLift B b))

/-- The substitution morphism between the two generic extended contexts. -/
noncomputable def piSubMor {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (Over.mk (piCls (sub σ A) (sub (extend σ A) B)) : Over (piBase A B).left) ⟶
      Over.mk (piCls A B) :=
  Over.homMk σ (piCls_sub σ A B).symm

theorem piSubMor_left_fst {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫
        pullback.fst (piCls A B) (disp (piGenA A B)) =
      pullback.fst (piCls (sub σ A) (sub (extend σ A) B))
        (disp (piGenA (sub σ A) (sub (extend σ A) B))) ≫ σ := by
  simp only [piSubMor, Over.pullback_obj_left, Over.mk_left, Over.mk_hom, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem piSubMor_left_snd {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫
        pullback.snd (piCls A B) (disp (piGenA A B)) =
      pullback.snd (piCls (sub σ A) (sub (extend σ A) B))
        (disp (piGenA (sub σ A) (sub (extend σ A) B))) := by
  simp only [piSubMor, Over.pullback_obj_left, Over.mk_left, Over.mk_hom, Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

/-- The first component of the identification of the extended context with the pullback of the
generic extended context. -/
theorem piCtxIso_hom_fst {Γ : C} (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (piCtxIso A B).hom ≫ pullback.fst (piCls A B) (disp (piGenA A B)) = disp A :=
  IsPullback.isoPullback_hom_fst _

theorem piCtxIso_hom_subMor_fst {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ((piCtxIso (sub σ A) (sub (extend σ A) B)).hom ≫
        ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left) ≫
      pullback.fst (piCls A B) (disp (piGenA A B)) = disp (sub σ A) ≫ σ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun x => (piCtxIso (sub σ A) (sub (extend σ A) B)).hom ≫ x)
        (piSubMor_left_fst σ A B)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun x => x ≫ σ) (piCtxIso_hom_fst (sub σ A) (sub (extend σ A) B)))))

theorem piCtxIso_hom_subMor_snd {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ((piCtxIso (sub σ A) (sub (extend σ A) B)).hom ≫
        ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left) ≫
      pullback.snd (piCls A B) (disp (piGenA A B)) =
        piGenMap (sub σ A) (sub (extend σ A) B) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun x => (piCtxIso (sub σ A) (sub (extend σ A) B)).hom ≫ x)
        (piSubMor_left_snd σ A B)).trans
      (piCtxIso_hom_snd (sub σ A) (sub (extend σ A) B)))

/-- The identification of the extended context with the pullback of the generic one is natural. -/
theorem piCtxIso_hom_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    extend σ A ≫ (piCtxIso A B).hom =
      (piCtxIso (sub σ A) (sub (extend σ A) B)).hom ≫
        ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left :=
  pullback.hom_ext
    (((Category.assoc (extend σ A) (piCtxIso A B).hom
        (pullback.fst (piCls A B) (disp (piGenA A B)))).trans
      ((congrArg (fun x => extend σ A ≫ x) (piCtxIso_hom_fst A B)).trans
        (extend_disp σ A))).trans (piCtxIso_hom_subMor_fst σ A B).symm)
    (((Category.assoc (extend σ A) (piCtxIso A B).hom
        (pullback.snd (piCls A B) (disp (piGenA A B)))).trans
      ((congrArg (fun x => extend σ A ≫ x) (piCtxIso_hom_snd A B)).trans
        (extend_piGenMap σ A B))).trans (piCtxIso_hom_subMor_snd σ A B).symm)

theorem piCtxIso_hom_subMor {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    (piCtxIso (sub σ A) (sub (extend σ A) B)).hom ≫
        ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫
          (piCtxIso A B).inv = extend σ A :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ (piCtxIso A B).inv) (piCtxIso_hom_sub σ A B).symm).trans
      ((Category.assoc (extend σ A) (piCtxIso A B).hom (piCtxIso A B).inv).trans
        ((congrArg (fun x => extend σ A ≫ x) (piCtxIso A B).hom_inv_id).trans
          (Category.comp_id (extend σ A)))))

theorem piCtxIso_inv_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫ (piCtxIso A B).inv =
      (piCtxIso (sub σ A) (sub (extend σ A) B)).inv ≫ extend σ A :=
  ((piCtxIso (sub σ A) (sub (extend σ A) B)).inv_hom_id_assoc
      (((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫
        (piCtxIso A B).inv)).symm.trans
    (congrArg (fun x => (piCtxIso (sub σ A) (sub (extend σ A) B)).inv ≫ x)
      (piCtxIso_hom_subMor σ A B))

/-- The morphism attached to a term of the body is natural in the context. -/
theorem piBodyMor_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (b : TmLift (ext Γ A) B) (b' : TmLift (ext Δ (sub σ A)) (sub (extend σ A) B))
    (hb : b'.1 = extend σ A ≫ b.1) :
    piBodyMor (sub σ A) (sub (extend σ A) B) b' =
      (Over.pullback (disp (piGenA A B))).map (piSubMor σ A B) ≫ piBodyMor A B b :=
  Over.OverMorphism.ext (ext_hom_ext
    ((piBodyMor_left_disp (sub σ A) (sub (extend σ A) B) b').trans
      ((piSubMor_left_snd σ A B).symm.trans
        ((congrArg
            (fun x => ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫ x)
            (piBodyMor_left_disp A B b).symm).trans
          (Category.assoc _ _ _).symm)))
    ((piBodyMor_left_gen (sub σ A) (sub (extend σ A) B) b').trans
      ((congrArg (fun x => (piCtxIso (sub σ A) (sub (extend σ A) B)).inv ≫ x) hb).trans
        ((Category.assoc (piCtxIso (sub σ A) (sub (extend σ A) B)).inv (extend σ A) b.1).symm.trans
          ((congrArg (fun x => x ≫ b.1) (piCtxIso_inv_sub σ A B).symm).trans
            ((Category.assoc _ (piCtxIso A B).inv b.1).trans
              ((congrArg
                  (fun x => ((Over.pullback (disp (piGenA A B))).map (piSubMor σ A B)).left ≫ x)
                  (piBodyMor_left_gen A B b).symm).trans
                (Category.assoc _ _ _).symm)))))))

/-- **The transpose is natural in the context**: this is naturality of the adjunction
transposition on the left. -/
theorem piTranspose_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (b : TmLift (ext Γ A) B) (b' : TmLift (ext Δ (sub σ A)) (sub (extend σ A) B))
    (hb : b'.1 = extend σ A ≫ b.1) :
    (piTranspose (sub σ A) (sub (extend σ A) B) b').1 = σ ≫ (piTranspose A B b).1 := by
  have key := (LcccPullbacks.adj (disp (piGenA A B))).homEquiv_naturality_left
    (piSubMor σ A B) (piBodyMor A B b)
  rw [← piBodyMor_sub σ A B b b' hb] at key
  exact congrArg CategoryTheory.CommaMorphism.left key

/-! ### Naturality of the dependent sum -/

/-- **The pairing of the dependent sum is natural in the context**: the comparison map from the
two-step extension into the generic two-step extension commutes with substitution. -/
theorem extend_sigGenMap {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A)) :
    extend (extend σ A) B ≫ sigGenMap A B =
      sigGenMap (sub σ A) (sub (extend σ A) B) :=
  ext_hom_ext
    ((Category.assoc (extend (extend σ A) B) (sigGenMap A B) (disp (piGenB A B))).trans
      ((congrArg (fun x => extend (extend σ A) B ≫ x) (sigGenMap_disp A B)).trans
        ((Category.assoc (extend (extend σ A) B) (disp B) (piGenMap A B)).symm.trans
          ((congrArg (fun x => x ≫ piGenMap A B) (extend_disp (extend σ A) B)).trans
            ((Category.assoc (disp (sub (extend σ A) B)) (extend σ A) (piGenMap A B)).trans
              ((congrArg (fun x => disp (sub (extend σ A) B) ≫ x) (extend_piGenMap σ A B)).trans
                (sigGenMap_disp (sub σ A) (sub (extend σ A) B)).symm))))))
    ((Category.assoc (extend (extend σ A) B) (sigGenMap A B) (gen (piGenB A B))).trans
      ((congrArg (fun x => extend (extend σ A) B ≫ x) (sigGenMap_gen A B)).trans
        ((extend_gen (extend σ A) B).trans
          (sigGenMap_gen (sub σ A) (sub (extend σ A) B)).symm)))

/-! ### Abstraction and application commute with substitution -/

/-- **Abstraction commutes with substitution**, read on codes. -/
theorem code_tmEquivPi_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (b : Sect (ext Γ A) B) :
    code (tmEquivPi (sub σ A) (sub (extend σ A) B)
        (Cwa.tmSub (T := Cwa.ofPullbacks C) (extend σ A) b)) =
      σ ≫ code (tmEquivPi A B b) :=
  (code_tmEquivPi (sub σ A) (sub (extend σ A) B)
      (Cwa.tmSub (T := Cwa.ofPullbacks C) (extend σ A) b)).trans
    ((piTranspose_sub σ A B (sectEquivLift B b) _ (code_tmSub (extend σ A) b)).trans
      (congrArg (fun x => σ ≫ x) (code_tmEquivPi A B b).symm))

/-- **Abstraction commutes with substitution**: the `lam` of the Π-structure of a locally
cartesian closed category is natural in the context. -/
theorem code_lam_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (b : Sect (ext Γ A) B) :
    code ((piStruct (C := C)).lam (Cwa.tmSub (T := Cwa.ofPullbacks C) (extend σ A) b)) =
      code (Cwa.tmSub (T := Cwa.ofPullbacks C) σ ((piStruct (C := C)).lam b)) :=
  (code_tmEquivPi_sub σ A B b).trans (code_tmSub σ (tmEquivPi A B b)).symm

/-- **Abstraction commutes with substitution**, written with the transport along the stability of
the dependent product under substitution: `(λ b)[σ] = λ (b[σ⁺])`. -/
theorem lam_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (b : Sect (ext Γ A) B) :
    Cwa.tmCast (T := Cwa.ofPullbacks C) (piTy_sub σ A B)
        (Cwa.tmSub (T := Cwa.ofPullbacks C) σ ((piStruct (C := C)).lam b)) =
      (piStruct (C := C)).lam (Cwa.tmSub (T := Cwa.ofPullbacks C) (extend σ A) b) :=
  code_injective
    ((eq_of_heq (code_tmCast_heq (piTy_sub σ A B)
        (Cwa.tmSub (T := Cwa.ofPullbacks C) σ ((piStruct (C := C)).lam b)))).trans
      (code_lam_sub σ A B b).symm)

/-- **Application commutes with substitution**: if `f'` is the substitution of `f`, then the body
of `f'` is the substitution of the body of `f`. -/
theorem code_app_sub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (f : Sect Γ (piTy A B)) (f' : Sect Δ (piTy (sub σ A) (sub (extend σ A) B)))
    (hf : code f' = σ ≫ code f) :
    code ((piStruct (C := C)).app f') =
      extend σ A ≫ code ((piStruct (C := C)).app f) := by
  have hb : Cwa.tmSub (T := Cwa.ofPullbacks C) (extend σ A)
      ((tmEquivPi A B).symm f) = (tmEquivPi (sub σ A) (sub (extend σ A) B)).symm f' := by
    refine (tmEquivPi (sub σ A) (sub (extend σ A) B)).injective (code_injective ?_)
    exact (code_tmEquivPi_sub σ A B ((tmEquivPi A B).symm f)).trans
      ((congrArg (fun x => σ ≫ code x) ((tmEquivPi A B).apply_symm_apply f)).trans
        (hf.symm.trans (congrArg code
          ((tmEquivPi (sub σ A) (sub (extend σ A) B)).apply_symm_apply f').symm)))
  exact (congrArg code hb).symm.trans (code_tmSub (extend σ A) ((tmEquivPi A B).symm f))

/-- **Application commutes with substitution**, for the canonical substitution of a term of the
dependent product. -/
theorem code_app_tmSub {Γ Δ : C} (σ : Δ ⟶ Γ) (A : LuTy Γ) (B : LuTy (ext Γ A))
    (f : Sect Γ (piTy A B)) :
    code ((piStruct (C := C)).app (Cwa.tmCast (T := Cwa.ofPullbacks C) (piTy_sub σ A B)
        (Cwa.tmSub (T := Cwa.ofPullbacks C) σ f))) =
      extend σ A ≫ code ((piStruct (C := C)).app f) :=
  code_app_sub σ A B f _
    ((eq_of_heq (code_tmCast_heq (piTy_sub σ A B)
      (Cwa.tmSub (T := Cwa.ofPullbacks C) σ f))).trans (code_tmSub σ f))

/-- **The Π-structure of the local-universe model of a locally cartesian closed category is
natural**: on top of β and η, abstraction commutes with substitution. -/
noncomputable def naturalPiStruct : Cwa.NaturalPiStruct (Cwa.ofPullbacks C) where
  toPiStruct := piStruct
  lam_sub := by
    intro _ _ σ A B b
    exact LuTy.lam_sub σ A B b

end LuTy

/-- **A locally cartesian closed category models the dependent product, substitution included.**
The strictified model of `Start/CwaLocalUniverse.lean` carries a Π-structure with β and η whose
abstraction is moreover stable under substitution. -/
noncomputable def Cwa.naturalPiStructOfLccc (C : Type u) [Category.{v} C] [HasPullbacks C]
    [HasBinaryProducts C] [LcccPullbacks C] : Cwa.NaturalPiStruct (Cwa.ofPullbacks C) :=
  LuTy.naturalPiStruct
