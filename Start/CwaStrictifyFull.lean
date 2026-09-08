/-
**The strictification of the contexts of a full model maps onto the model.**

`Start/CwaDemocratic.lean` shows that the category of contexts `C` of a full model `T` has
pullbacks, so `C` carries the strictified model `Cwa.ofPullbacks C` of
`Start/CwaLocalUniverse.lean`.  This module compares the two: there is a **morphism of models**
`Cwa.fullStrictify : Cwa.ofPullbacks C ⟶ T` which is the identity on contexts, and every type of
`T` is in its image up to an isomorphism of extended contexts over the base
(`Cwa.fullStrictify_essSurj`).  So a full model is presented by its own category of contexts.

The construction is the reason local universes strictify: a local universe over `Γ` is a morphism
`proj` of `C` together with a classifying map `cls` into its base, and substitution acts on `cls`
alone.  Sending it to the presentation of `proj` given by fullness, substituted along `cls`,
therefore commutes with substitution **on the nose** — which is what a morphism of categories with
attributes demands.

Main definitions:

* `Cwa.luTyMap` — the type of the model presented by a local universe;
* `Cwa.fullStrictify` — the morphism of models.

Main results:

* `Cwa.luTyMap_sub` — the action on types commutes strictly with substitution;
* `Cwa.fullStrictify_essSurj` — **every type of a full model is presented by a local universe**,
  up to an isomorphism of extended contexts over the base.

What is *not* claimed is a morphism the other way.  Such a morphism `T ⟶ Cwa.ofPullbacks C`
would have to send a type over `Γ` to a local universe, whose base and generic family do not
depend on `Γ` and whose classifying map alone carries the substitution — that is, it would amount
to a universe for the model, which a model need not have.  No such morphism is constructed here,
and no equivalence of `T` with the strictification of its contexts is claimed.
-/

import Start.CwaDemocratic
import Start.CwaLcccOfFull
import Start.CwaSubFunctorial

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- The type of the model presented by a local universe: the presentation of the generic family
given by fullness, substituted along the classifying map. -/
def luTyMap (h : IsFull T) {Γ : C} (P : LuTy Γ) : T.Ty Γ := T.tySub P.cls (h.ty P.proj)

/-- **The action on types commutes strictly with substitution**, because substitution acts on the
classifying map alone. -/
theorem luTyMap_sub (h : IsFull T) {Γ Δ : C} (σ : Δ ⟶ Γ) (P : LuTy Γ) :
    luTyMap h (LuTy.sub σ P) = T.tySub σ (luTyMap h P) :=
  T.tySub_comp P.cls σ (h.ty P.proj)

section

variable [HasPullbacks C]

/-- The extended context of the type presented by a local universe *is* the extended context of
the local universe: both are the pullback of the generic family along the classifying map. -/
noncomputable def fullExtCompare (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    T.ext Γ (luTyMap h P) ≅ LuTy.ext Γ P :=
  (h.isPullback P.proj P.cls).flip.isoPullback

@[simp] theorem fullExtCompare_hom_disp (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    (fullExtCompare h P).hom ≫ LuTy.disp P = T.disp (luTyMap h P) :=
  IsPullback.isoPullback_hom_fst _

@[simp] theorem fullExtCompare_hom_gen (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    (fullExtCompare h P).hom ≫ LuTy.gen P
      = T.extend P.cls (h.ty P.proj) ≫ (h.iso P.proj).inv :=
  IsPullback.isoPullback_hom_snd _

/-- The comparison identifying the extended context of a local universe with the extended context
of the type it presents. -/
noncomputable def fullExtIso (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    LuTy.ext Γ P ≅ T.ext Γ (luTyMap h P) :=
  (fullExtCompare h P).symm

theorem fullExtIso_disp (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    (fullExtIso h P).hom ≫ T.disp (luTyMap h P) = LuTy.disp P := by
  rw [fullExtIso, Iso.symm_hom, ← fullExtCompare_hom_disp h P, Iso.inv_hom_id_assoc]

/-- The comparison is compatible with the action of a substitution on extended contexts, in the
form that compares the two maps out of the extended context of the substituted local universe. -/
theorem fullExtCompare_extend (co : ExtCoherent T) (h : IsFull T) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (P : LuTy Γ) :
    (fullExtCompare h (LuTy.sub σ P)).hom ≫ LuTy.extend σ P
      = eqToHom (congrArg (T.ext Δ) (luTyMap_sub h σ P)) ≫ T.extend σ (luTyMap h P)
          ≫ (fullExtCompare h P).hom := by
  have hext : ∀ {W : C} (a b : W ⟶ LuTy.ext Γ P), a ≫ LuTy.disp P = b ≫ LuTy.disp P →
      a ≫ LuTy.gen P = b ≫ LuTy.gen P → a = b := fun _ _ h₁ h₂ => pullback.hom_ext h₁ h₂
  refine hext _ _ ?_ ?_
  · rw [Category.assoc, LuTy.extend_disp, ← Category.assoc, fullExtCompare_hom_disp,
      Category.assoc, Category.assoc, fullExtCompare_hom_disp,
      (T.isPullback σ (luTyMap h P)).w, ← Category.assoc, eqToHom_ext_disp]
    exact luTyMap_sub h σ P
  · rw [Category.assoc, LuTy.extend_gen, fullExtCompare_hom_gen, Category.assoc, Category.assoc,
      fullExtCompare_hom_gen]
    simp only [LuTy.sub_cls, LuTy.sub_proj, luTyMap]
    slice_rhs 1 3 => rw [← co.extend_comp P.cls σ (h.ty P.proj)]

/-- The comparison is compatible with the action of a substitution on extended contexts. -/
theorem fullExtIso_extend (co : ExtCoherent T) (h : IsFull T) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (P : LuTy Γ) :
    LuTy.extend σ P ≫ (fullExtIso h P).hom
      = (fullExtIso h (LuTy.sub σ P)).hom
          ≫ eqToHom (congrArg (T.ext Δ) (luTyMap_sub h σ P)) ≫ T.extend σ (luTyMap h P) := by
  have key := fullExtCompare_extend co h σ P
  rw [fullExtIso, fullExtIso, Iso.symm_hom, Iso.symm_hom,
    ← Iso.inv_hom_id_assoc (fullExtCompare h (LuTy.sub σ P)) (LuTy.extend σ P), key]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The strictification of the contexts of a full model maps onto the model**: a local universe
is sent to the type it presents, and substitution is preserved on the nose. -/
@[reducible] noncomputable def fullStrictify (co : ExtCoherent T) (h : IsFull T) :
    Mor (Cwa.ofPullbacks C) T where
  fnc := 𝟭 C
  tyMap P := luTyMap h P
  tyMap_sub σ P := luTyMap_sub h σ P
  extIso P := fullExtIso h P
  extIso_disp P := fullExtIso_disp h P
  extIso_extend σ P := fullExtIso_extend co h σ P

theorem fullStrictify_fnc (co : ExtCoherent T) (h : IsFull T) :
    (fullStrictify co h).fnc = 𝟭 C := rfl

theorem fullStrictify_tyMap (co : ExtCoherent T) (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    (fullStrictify co h).tyMap P = luTyMap h P := rfl

/-- **The comparison is a bijection on terms**: a term of a local universe is the same thing as a
term of the type it presents, because the comparison of the extended contexts is an isomorphism
over the base. -/
theorem fullStrictify_tmMap_bijective (co : ExtCoherent T) (h : IsFull T) {Γ : C} (P : LuTy Γ) :
    Function.Bijective ((fullStrictify co h).tmMap (Γ := Γ) (A := P)) := by
  constructor
  · intro a b hab
    have h1 : a.1 ≫ (fullExtIso h P).hom = b.1 ≫ (fullExtIso h P).hom :=
      congrArg Subtype.val hab
    exact Tm.ext' ((Iso.cancel_iso_hom_right _ _ (fullExtIso h P)).1 h1)
  · intro t
    refine ⟨⟨t.1 ≫ (fullExtIso h P).inv, ?_⟩, Tm.ext' ?_⟩
    · rw [Category.assoc, fullExtIso, Iso.symm_inv, fullExtCompare_hom_disp, t.2]
      rfl
    · change (t.1 ≫ (fullExtIso h P).inv) ≫ (fullExtIso h P).hom = t.1
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Every type of a full model is presented by a local universe**, up to an isomorphism of
extended contexts over the base: the local universe of its own display map. -/
theorem fullStrictify_essSurj (co : ExtCoherent T) (h : IsFull T) {Γ : C} (A : T.Ty Γ) :
    ∃ (P : LuTy Γ) (e : T.ext Γ A ≅ T.ext Γ ((fullStrictify co h).tyMap P)),
      e.hom ≫ T.disp ((fullStrictify co h).tyMap P) = T.disp A := by
  have hty : (fullStrictify co h).tyMap (LuTy.ofHom (T.disp A)) = h.ty (T.disp A) :=
    T.tySub_id (h.ty (T.disp A))
  refine ⟨LuTy.ofHom (T.disp A), h.iso (T.disp A) ≪≫ eqToIso (congrArg (T.ext Γ) hty.symm), ?_⟩
  rw [Iso.trans_hom, Category.assoc, eqToIso.hom, eqToHom_ext_disp, h.iso_disp]
  exact hty.symm

end

/-! ### A full democratic model and the strictification of its contexts -/

/-- **The strictification of the contexts of a full democratic model with dependent products is
again a model with dependent products.**  The contexts have pullbacks by fullness and a terminal
object by democracy, hence binary products; they are locally cartesian closed by
`LcccPullbacks.ofIsFull`; and a locally cartesian closed category strictifies to a model with a
natural Π-structure. -/
theorem nonempty_naturalPiStruct_ofPullbacks_of_isFull (co : ExtCoherent T) (h : IsFull T)
    (d : IsDemocratic T) (P : NaturalPiStruct T) :
    @Nonempty (Cwa.NaturalPiStruct (@Cwa.ofPullbacks C _ (hasPullbacks_of_isFull h))) := by
  have := hasPullbacks_of_isFull h
  have := d.isTerminal.hasTerminal
  have := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  have := LcccPullbacks.ofIsFull co h P
  exact ⟨Cwa.naturalPiStructOfLccc C⟩

end Cwa
