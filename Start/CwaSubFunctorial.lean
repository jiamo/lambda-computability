/-
**Functoriality of the substitution of terms.**

A category with attributes as defined in `Start/Cwa.lean` asks substitution to be *strictly*
functorial on types (`tySub_id`, `tySub_comp`) but says nothing about the action on extended
contexts beyond the fact that the extension squares are pullbacks.  The substitution of terms is
defined from that pullback, so nothing yet forces it to be functorial: an automorphism of an
extended context over its base makes the extension square of the identity substitution a pullback
just as well, and the substitution of terms along the identity is then that automorphism, not the
identity.  What is missing is a coherence law relating `extend` for the identity and for a
composite to the (strict) equalities of types.

This module isolates that law as `Cwa.ExtCoherent` and derives from it what one expects:
substituting the identity does nothing, and substituting a composite is substituting twice
(`Cwa.ExtCoherent.tmSub_id`, `Cwa.ExtCoherent.tmSub_comp`).  The strictified model of
`Start/CwaLocalUniverse.lean` satisfies the law — there `extend` is a map into a pullback, and
both sides of each equation are computed by the two legs.

Main definitions:

* `Cwa.ExtCoherent` — the coherence law for the action of a substitution on extended contexts.

Main results:

* `Cwa.ExtCoherent.tmSub_id`, `Cwa.ExtCoherent.tmSub_comp` — **the substitution of terms is
  functorial**;
* `Cwa.extCoherent_ofPullbacks` — the strictified model of a category with pullbacks is coherent.
-/

import Start.CwaMor
import Start.CwaUniverse

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-! ### Transport of terms along equalities of types -/

theorem tmCast_trans {Γ : C} {A B B' : T.Ty Γ} (h : A = B) (h' : B = B') (a : T.Tm Γ A) :
    tmCast h' (tmCast h a) = tmCast (h.trans h') a := by
  cases h; cases h'; rfl

theorem tmCast_eq_iff {Γ : C} {A B : T.Ty Γ} (h : A = B) (a : T.Tm Γ A) (b : T.Tm Γ B) :
    tmCast h a = b ↔ a = tmCast h.symm b := by
  cases h; rfl

/-- Transporting an extended context along an equality of types lies over the base context. -/
@[reassoc] theorem eqToHom_ext_disp {Γ : C} {A B : T.Ty Γ} (e : A = B) :
    eqToHom (congrArg (T.ext Γ) e) ≫ T.disp B = T.disp A := by
  cases e; simp

/-- Substitution commutes with transport along an equality of types. -/
theorem tmSub_tmCast {Γ Δ : C} (σ : Δ ⟶ Γ) {A B : T.Ty Γ} (h : A = B) (a : T.Tm Γ A) :
    T.tmSub σ (tmCast h a) = tmCast (congrArg (T.tySub σ) h) (T.tmSub σ a) := by
  cases h; rfl

/-! ### The coherence law -/

/-- The **coherence law for the action of a substitution on extended contexts**: substituting the
identity acts by the transport along `tySub_id`, and substituting a composite acts by the composite
of the actions, up to the transport along `tySub_comp`.  These are the two equations the extension
squares of a category with attributes do not imply; with them, the substitution of terms is
functorial. -/
structure ExtCoherent (T : Cwa.{u, v, w} C) where
  /-- The identity substitution acts by the transport along `tySub_id`. -/
  extend_id : ∀ {Γ : C} (A : T.Ty Γ),
      T.extend (𝟙 Γ) A = eqToHom (congrArg (T.ext Γ) (T.tySub_id A))
  /-- A composite substitution acts by the composite of the actions. -/
  extend_comp : ∀ {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : T.Ty Γ),
      T.extend (τ ≫ σ) A
        = eqToHom (congrArg (T.ext Θ) (T.tySub_comp σ τ A)) ≫ T.extend τ (T.tySub σ A)
            ≫ T.extend σ A

namespace ExtCoherent

/-- **Substituting the identity does nothing.** -/
theorem tmSub_id (co : ExtCoherent T) {Γ : C} {A : T.Ty Γ} (a : T.Tm Γ A) :
    tmCast (T.tySub_id A) (T.tmSub (𝟙 Γ) a) = a := by
  rw [tmCast_eq_iff]
  refine (tmSub_eq_of (𝟙 Γ) a _ ?_).symm
  rw [tmCast_val, co.extend_id, Category.assoc]
  simp

/-- **Substituting a composite is substituting twice.** -/
theorem tmSub_comp (co : ExtCoherent T) {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) {A : T.Ty Γ}
    (a : T.Tm Γ A) :
    tmCast (T.tySub_comp σ τ A) (T.tmSub (τ ≫ σ) a) = T.tmSub τ (T.tmSub σ a) := by
  refine tmSub_eq_of τ (T.tmSub σ a) _ ?_
  refine (T.isPullback σ A).hom_ext ?_ ?_
  · have hcomp : (T.tmSub (τ ≫ σ) a).1 ≫ T.extend (τ ≫ σ) A = (τ ≫ σ) ≫ a.1 :=
      tmSub_extend (τ ≫ σ) a
    rw [Category.assoc]
    calc (tmCast (T.tySub_comp σ τ A) (T.tmSub (τ ≫ σ) a)).1 ≫ T.extend τ (T.tySub σ A)
            ≫ T.extend σ A
        = (T.tmSub (τ ≫ σ) a).1 ≫ T.extend (τ ≫ σ) A := by
          rw [tmCast_val, co.extend_comp σ τ A]
          simp
      _ = (τ ≫ σ) ≫ a.1 := hcomp
      _ = (τ ≫ (T.tmSub σ a).1) ≫ T.extend σ A := by
          rw [Category.assoc, Category.assoc, tmSub_extend σ a]
  · have h₁ : (tmCast (T.tySub_comp σ τ A) (T.tmSub (τ ≫ σ) a)).1
        ≫ T.extend τ (T.tySub σ A) ≫ T.disp (T.tySub σ A) = τ := by
      rw [(T.isPullback τ (T.tySub σ A)).w, ← Category.assoc,
        (tmCast (T.tySub_comp σ τ A) (T.tmSub (τ ≫ σ) a)).2, Category.id_comp]
    rw [Category.assoc, h₁, Category.assoc, (T.tmSub σ a).2, Category.comp_id]

end ExtCoherent

/-! ### Substitution of codes -/

namespace Universe

/-- Substituting the identity in a code does nothing. -/
theorem sub_id (co : ExtCoherent T) (Un : Universe T) {Γ : C} (a : T.Tm Γ (Un.U Γ)) :
    Un.sub (𝟙 Γ) a = a := by
  exact co.tmSub_id a

/-- Substituting a composite in a code is substituting twice. -/
theorem sub_comp (co : ExtCoherent T) (Un : Universe T) {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (a : T.Tm Γ (Un.U Γ)) : Un.sub τ (Un.sub σ a) = Un.sub (τ ≫ σ) a := by
  rw [Universe.sub, Universe.sub, Universe.sub, tmSub_tmCast, tmCast_trans,
    ← co.tmSub_comp σ τ a, tmCast_trans]

end Universe

/-! ### The strictified model is coherent -/

variable [HasPullbacks C]

/-- The identity substitution acts on local universes by the transport along `sub_id`. -/
theorem lu_extend_id {Γ : C} (A : LuTy Γ) :
    LuTy.extend (𝟙 Γ) A = eqToHom (congrArg (LuTy.ext Γ) (LuTy.sub_id A)) := by
  refine (LuTy.isPullback_gen A).hom_ext ?_ ?_
  · rw [LuTy.extend_gen, eqToHom_lu_gen (LuTy.sub_id A),
      Subsingleton.elim (congrArg LuTy.total (LuTy.sub_id A)) rfl, eqToHom_refl,
      Category.comp_id]
  · rw [LuTy.extend_disp, eqToHom_lu_disp (LuTy.sub_id A), Category.comp_id]

/-- A composite substitution acts on local universes by the composite of the actions. -/
theorem lu_extend_comp {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : LuTy Γ) :
    LuTy.extend (τ ≫ σ) A
      = eqToHom (congrArg (LuTy.ext Θ) (LuTy.sub_comp σ τ A)) ≫ LuTy.extend τ (LuTy.sub σ A)
          ≫ LuTy.extend σ A := by
  refine (LuTy.isPullback_gen A).hom_ext ?_ ?_
  · rw [LuTy.extend_gen, Category.assoc, Category.assoc, LuTy.extend_gen, LuTy.extend_gen,
      eqToHom_lu_gen (LuTy.sub_comp σ τ A),
      Subsingleton.elim (congrArg LuTy.total (LuTy.sub_comp σ τ A)) rfl, eqToHom_refl,
      Category.comp_id]
  · simp only [Category.assoc]
    rw [LuTy.extend_disp, LuTy.extend_disp, ← Category.assoc (LuTy.extend τ (LuTy.sub σ A)),
      LuTy.extend_disp]
    simp only [Category.assoc]
    rw [eqToHom_lu_disp_assoc (LuTy.sub_comp σ τ A)]

variable (C) in
/-- **The strictified model of a category with pullbacks satisfies the coherence law.**  Both
sides of each equation are maps into the pullback presenting an extended context, so it is enough
to compare them with the two legs. -/
theorem extCoherent_ofPullbacks : ExtCoherent (Cwa.ofPullbacks C) where
  extend_id A := lu_extend_id A
  extend_comp σ τ A := lu_extend_comp σ τ A

end Cwa
