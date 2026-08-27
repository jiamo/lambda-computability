/-
**Morphisms of models preserving a universe.**

`Start/CwaUniverse.lean` adds to a category with attributes the structure a model of `λΠ` needs:
a universe `U` of small types with a decoding `El`, dependent products over the small types, and
closure of the universe under them.  `Start/CwaMor.lean` defines a morphism of categories with
attributes.  Neither says what it means for a *comparison* of models to respect the universe —
and that is exactly the data an interpretation of the syntax must carry, since in the syntactic
model the types of the calculus are the terms of the universe.

This module supplies it.  A morphism `F : Mor T S` **preserves** universes `Un` on `T` and `Vn`
on `S` when it carries the universe to the universe and commutes with decoding.  The immediate
consequences are developed: the induced map on codes commutes with substitution
(`Mor.PreservesUniverse.codeMap_sub`), universe preservation is closed under identity and
composition, and a preserving morphism transports the extension square of a decoded type
(`Mor.PreservesUniverse.extElIso`).  On top of that, preservation of the dependent products over
the small types and of the closure of the universe under them are defined, again closed under
identity and composition.

Main definitions:

* `Cwa.Mor.PreservesUniverse` — a morphism preserving a universe;
* `Cwa.Mor.PreservesUniverse.codeMap` — the induced action on codes;
* `Cwa.Mor.PreservesUniverse.extElIso` — the induced comparison of contexts extended by a decoded
  type;
* `Cwa.Mor.PreservesSmallPi`, `Cwa.Mor.PreservesPiClosed` — preservation of the products over the
  small types and of the codes for them.

Main results:

* `Cwa.Mor.PreservesUniverse.codeMap_sub` — **the action on codes commutes with substitution**;
* `Cwa.Mor.PreservesUniverse.id`, `Cwa.Mor.PreservesUniverse.comp` — universe preservation is
  closed under identity and composition, and likewise for the products
  (`Cwa.Mor.PreservesSmallPi.id`, `.comp`) and their codes (`Cwa.Mor.PreservesPiClosed.id`,
  `.comp`).
-/

import Start.CwaSubFunctorial

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w' u'' v'' w''

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {T : Cwa.{u, v, w} C} {S : Cwa.{u', v', w'} D} {R : Cwa.{u'', v'', w''} E}

/-- The action of a morphism on terms commutes with transport along an equality of types. -/
theorem Mor.tmMap_tmCast (F : Mor T S) {Γ : C} {A B : T.Ty Γ} (h : A = B) (a : T.Tm Γ A) :
    F.tmMap (tmCast h a) = tmCast (congrArg F.tyMap h) (F.tmMap a) := by
  cases h; rfl

/-! ### Preservation of a universe -/

/-- A morphism of categories with attributes **preserves a universe** when it carries the type of
codes to the type of codes and commutes with decoding.  This is the compatibility an interpretation
of `λΠ` must have: the types of the calculus are the terms of its universe, so a comparison of
models is a comparison of the *types* of the calculus only if it respects `U` and `El`. -/
structure Mor.PreservesUniverse (F : Mor T S) (Un : Universe T) (Vn : Universe S) where
  /-- The universe is carried to the universe. -/
  U_map : ∀ Γ : C, F.tyMap (Un.U Γ) = Vn.U (F.fnc.obj Γ)
  /-- Decoding is preserved. -/
  El_map : ∀ {Γ : C} (a : T.Tm Γ (Un.U Γ)),
      F.tyMap (Un.El a) = Vn.El (tmCast (U_map Γ) (F.tmMap a))

namespace Mor.PreservesUniverse

variable {F : Mor T S} {Un : Universe T} {Vn : Universe S}

/-- The action of a preserving morphism on the codes of small types. -/
def codeMap (h : F.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    S.Tm (F.fnc.obj Γ) (Vn.U (F.fnc.obj Γ)) :=
  tmCast (h.U_map Γ) (F.tmMap a)

theorem El_map' (h : F.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    F.tyMap (Un.El a) = Vn.El (h.codeMap a) := h.El_map a

/-- **The action on codes commutes with substitution.**  Both sides are transports of the image
under `F` of the substituted term, and the transports agree because the equalities of types they
are taken along have the same endpoints. -/
theorem codeMap_sub (h : F.PreservesUniverse Un Vn) {Γ Δ : C} (σ : Δ ⟶ Γ)
    (a : T.Tm Γ (Un.U Γ)) :
    h.codeMap (Un.sub σ a) = Vn.sub (F.fnc.map σ) (h.codeMap a) := by
  have key : F.tmMap (T.tmSub σ a)
      = tmCast (F.tyMap_sub σ (Un.U Γ)).symm (S.tmSub (F.fnc.map σ) (F.tmMap a)) := by
    rw [← F.tmMap_tmSub σ a, tmCast_trans]
    simp
  simp only [codeMap, Universe.sub, F.tmMap_tmCast, tmSub_tmCast, key, tmCast_trans]

/-- The comparison of the image of a context extended by a decoded type with the corresponding
extended context in the target. -/
noncomputable def extElIso (h : F.PreservesUniverse Un Vn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    F.fnc.obj (T.ext Γ (Un.El a)) ≅ S.ext (F.fnc.obj Γ) (Vn.El (h.codeMap a)) :=
  F.extIso (Un.El a) ≪≫ eqToIso (congrArg (S.ext (F.fnc.obj Γ)) (h.El_map' a))

@[simp] theorem extElIso_hom_disp (h : F.PreservesUniverse Un Vn) {Γ : C}
    (a : T.Tm Γ (Un.U Γ)) :
    (h.extElIso a).hom ≫ S.disp (Vn.El (h.codeMap a)) = F.fnc.map (T.disp (Un.El a)) := by
  simp only [extElIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_ext_disp (h.El_map' a)]
  exact F.extIso_disp _

/-- Universe preservation is closed under the identity. -/
theorem id (Un : Universe T) : (Mor.id T).PreservesUniverse Un Un where
  U_map _ := rfl
  El_map a := by rw [Mor.tmMap_id]; rfl

/-- The action on codes of a composite. -/
theorem codeMap_comp' {G : Mor S R} {Wn : Universe R} (h : F.PreservesUniverse Un Vn)
    (h' : G.PreservesUniverse Vn Wn) (hU : ∀ Γ : C, (F.comp G).tyMap (Un.U Γ) = Wn.U _)
    {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    tmCast (hU Γ) ((F.comp G).tmMap a) = h'.codeMap (h.codeMap a) := by
  simp only [codeMap, G.tmMap_tmCast, tmCast_trans, Mor.tmMap_comp]

/-- Universe preservation is closed under composition. -/
theorem comp {G : Mor S R} {Wn : Universe R} (h : F.PreservesUniverse Un Vn)
    (h' : G.PreservesUniverse Vn Wn) : (F.comp G).PreservesUniverse Un Wn where
  U_map Γ := by
    change G.tyMap (F.tyMap (Un.U Γ)) = _
    rw [h.U_map Γ]
    exact h'.U_map _
  El_map {Γ} a := by
    change G.tyMap (F.tyMap (Un.El a)) = _
    rw [h.El_map' a, h'.El_map' (h.codeMap a)]
    congr 1
    simp only [codeMap, G.tmMap_tmCast, tmCast_trans, Mor.tmMap_comp]

theorem codeMap_comp {G : Mor S R} {Wn : Universe R} (h : F.PreservesUniverse Un Vn)
    (h' : G.PreservesUniverse Vn Wn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    (h.comp h').codeMap a = h'.codeMap (h.codeMap a) :=
  codeMap_comp' h h' _ a

/-- The comparison of extended contexts of a composite is the composite of the comparisons. -/
theorem extElIso_comp {G : Mor S R} {Wn : Universe R} (h : F.PreservesUniverse Un Vn)
    (h' : G.PreservesUniverse Vn Wn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    (h.comp h').extElIso a
      = G.fnc.mapIso (h.extElIso a) ≪≫ h'.extElIso (h.codeMap a)
          ≪≫ eqToIso (congrArg (R.ext _) (congrArg Wn.El (codeMap_comp h h' a).symm)) := by
  apply Iso.ext
  simp only [extElIso, Iso.trans_hom, eqToIso.hom, Mor.comp, Functor.mapIso_hom, Category.assoc,
    G.fnc.map_comp]
  rw [Mor.extIso_eqToHom_assoc G (h.El_map' a)]
  congr 2
  simp

/-- The comparison of extended contexts of a composite, in inverse form. -/
theorem extElIso_comp_inv {G : Mor S R} {Wn : Universe R} (h : F.PreservesUniverse Un Vn)
    (h' : G.PreservesUniverse Vn Wn) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    ((h.comp h').extElIso a).inv
      = eqToHom (congrArg (R.ext _) (congrArg Wn.El (codeMap_comp h h' a)))
          ≫ (h'.extElIso (h.codeMap a)).inv ≫ G.fnc.map (h.extElIso a).inv := by
  rw [extElIso_comp h h']
  simp only [Iso.trans_inv, eqToIso.inv, Functor.mapIso_inv, Category.assoc]

end Mor.PreservesUniverse

/-! ### Preservation of the dependent products over the small types -/

/-- A universe-preserving morphism **preserves the products over the small types** when the image
of a product is the product of the images, the body being transported along the comparison of
extended contexts. -/
structure Mor.PreservesSmallPi (F : Mor T S) {Un : Universe T} {Vn : Universe S}
    (h : F.PreservesUniverse Un Vn) (P : Universe.SmallPi Un) (Q : Universe.SmallPi Vn) where
  /-- The image of a small product is the small product of the images. -/
  Pi_map : ∀ {Γ : C} (a : T.Tm Γ (Un.U Γ)) (B : T.Ty (T.ext Γ (Un.El a))),
      F.tyMap (P.Pi a B) = Q.Pi (h.codeMap a) (S.tySub (h.extElIso a).inv (F.tyMap B))

/-- A universe-preserving morphism **preserves the codes for products** when the image of the code
of a product is the code of the product of the images. -/
structure Mor.PreservesPiClosed (F : Mor T S) {Un : Universe T} {Vn : Universe S}
    (h : F.PreservesUniverse Un Vn) {P : Universe.SmallPi Un} {Q : Universe.SmallPi Vn}
    (C₀ : Universe.PiClosed Un P) (C₁ : Universe.PiClosed Vn Q) where
  /-- Codes for products are carried to codes for products. -/
  code_map : ∀ {Γ : C} (a : T.Tm Γ (Un.U Γ)) (b : T.Tm (T.ext Γ (Un.El a)) (Un.U _)),
      h.codeMap (C₀.code a b)
        = C₁.code (h.codeMap a) (Vn.sub (h.extElIso a).inv (h.codeMap b))

namespace Mor.PreservesSmallPi

variable {F : Mor T S} {Un : Universe T} {Vn : Universe S}

/-- The dependent product over a small type does not change when the code of the domain is
replaced by an equal one, the body being transported along the induced equality of extended
contexts. -/
theorem _root_.Cwa.Universe.SmallPi.Pi_congr (P : Universe.SmallPi Un) {Γ : C}
    {a a' : T.Tm Γ (Un.U Γ)} (h : a = a') (B : T.Ty (T.ext Γ (Un.El a))) :
    P.Pi a' (T.tySub (eqToHom (congrArg (fun c => T.ext Γ (Un.El c)) h).symm) B) = P.Pi a B := by
  cases h
  simp only [congrArg, eqToHom_refl, T.tySub_id]

/-- The identity morphism preserves the small products. -/
theorem id (Un : Universe T) (P : Universe.SmallPi Un) :
    (Mor.id T).PreservesSmallPi (PreservesUniverse.id Un) P P where
  Pi_map a B := by
    have hc : a = (PreservesUniverse.id Un).codeMap a := (Mor.tmMap_id T a).symm
    have hiso : ((PreservesUniverse.id Un).extElIso a).inv
        = eqToHom (congrArg (fun c => T.ext _ (Un.El c)) hc).symm := by
      simp [PreservesUniverse.extElIso, Mor.id, eqToIso.inv]
    rw [hiso]
    exact (P.Pi_congr hc B).symm

/-- Preservation of the small products is closed under composition. -/
theorem comp {G : Mor S R} {Wn : Universe R} {h : F.PreservesUniverse Un Vn}
    {h' : G.PreservesUniverse Vn Wn} {P : Universe.SmallPi Un} {Q : Universe.SmallPi Vn}
    {O : Universe.SmallPi Wn} (hP : F.PreservesSmallPi h P Q) (hQ : G.PreservesSmallPi h' Q O) :
    (F.comp G).PreservesSmallPi (h.comp h') P O where
  Pi_map {Γ} a B := by
    have hcm := PreservesUniverse.codeMap_comp h h' a
    change G.tyMap (F.tyMap (P.Pi a B)) = _
    rw [hP.Pi_map a B, hQ.Pi_map (h.codeMap a) _, G.tyMap_sub,
      ← O.Pi_congr hcm (R.tySub ((h.comp h').extElIso a).inv ((F.comp G).tyMap B))]
    congr 1
    rw [← R.tySub_comp, ← R.tySub_comp, PreservesUniverse.extElIso_comp_inv h h']
    congr 1
    simp

end Mor.PreservesSmallPi

namespace Mor.PreservesPiClosed

variable {F : Mor T S} {Un : Universe T}

/-- The code of a product does not change when the code of the domain is replaced by an equal one,
the code of the body being transported along the induced equality of extended contexts.  The
coherence law of `Start/CwaSubFunctorial.lean` is what makes the transport along the identity
trivial. -/
theorem code_congr (co : ExtCoherent T) {P : Universe.SmallPi Un} (C₀ : Universe.PiClosed Un P)
    {Γ : C} {a a' : T.Tm Γ (Un.U Γ)} (hc : a = a') (b : T.Tm (T.ext Γ (Un.El a)) (Un.U _))
    (f : T.ext Γ (Un.El a') ⟶ T.ext Γ (Un.El a))
    (hf : f = eqToHom (congrArg (fun c => T.ext Γ (Un.El c)) hc).symm) :
    C₀.code a' (Un.sub f b) = C₀.code a b := by
  cases hc
  subst hf
  exact congrArg (C₀.code a) (co.tmSub_id b)

/-- The identity morphism preserves the codes for products. -/
theorem id (co : ExtCoherent T) (Un : Universe T) {P : Universe.SmallPi Un}
    (C₀ : Universe.PiClosed Un P) :
    (Mor.id T).PreservesPiClosed (PreservesUniverse.id Un) C₀ C₀ where
  code_map a b := by
    have hc : a = (PreservesUniverse.id Un).codeMap a := (Mor.tmMap_id T a).symm
    have hb : (PreservesUniverse.id Un).codeMap b = b := Mor.tmMap_id T b
    have hiso : ((PreservesUniverse.id Un).extElIso a).inv
        = eqToHom (congrArg (fun c => T.ext _ (Un.El c)) hc).symm := by
      simp [PreservesUniverse.extElIso, Mor.id, eqToIso.inv]
    rw [hb, hiso, code_congr co C₀ hc b _ rfl]
    exact Mor.tmMap_id T _

/-- Preservation of the codes for products is closed under composition. -/
theorem comp (co : ExtCoherent R) {G : Mor S R} {Vn : Universe S} {Wn : Universe R}
    {h : F.PreservesUniverse Un Vn} {h' : G.PreservesUniverse Vn Wn}
    {P : Universe.SmallPi Un} {Q : Universe.SmallPi Vn} {O : Universe.SmallPi Wn}
    {C₀ : Universe.PiClosed Un P} {C₁ : Universe.PiClosed Vn Q} {C₂ : Universe.PiClosed Wn O}
    (hC : F.PreservesPiClosed h C₀ C₁) (hC' : G.PreservesPiClosed h' C₁ C₂) :
    (F.comp G).PreservesPiClosed (h.comp h') C₀ C₂ where
  code_map {Γ} a b := by
    have hcm := PreservesUniverse.codeMap_comp h h' a
    have hcb := PreservesUniverse.codeMap_comp h h' b
    rw [PreservesUniverse.codeMap_comp h h' (C₀.code a b), hC.code_map a b, hC'.code_map _ _,
      PreservesUniverse.codeMap_sub h' (h.extElIso a).inv (h.codeMap b),
      Universe.sub_comp co Wn, PreservesUniverse.extElIso_comp_inv h h',
      ← Universe.sub_comp co Wn, hcb, ← code_congr co C₂ hcm.symm _ _ rfl,
      ← Universe.sub_comp co Wn, ← Universe.sub_comp co Wn]

end Mor.PreservesPiClosed

end Cwa
