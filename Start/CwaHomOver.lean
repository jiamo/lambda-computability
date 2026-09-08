/-
**Maps over a substitution into a display map, and the transports of a Π-structure.**

`Start/Cwa.lean` defines a term of `A` in context `Γ` as a section of the display map of `A`.  The
same universal property — the extension square is a pullback — identifies the maps `Δ ⟶ Γ.A`
*lying over* a substitution `σ : Δ ⟶ Γ` with the terms of the substituted type `A[σ]`.  This module
records that bijection for an arbitrary category with attributes, together with the way it behaves
under precomposition, and a small calculus of transports for a Π-structure.  Both are used by
`Start/CwaLcccOfFull.lean`, which builds the dependent product of a locally cartesian closed
structure out of the Π-structure of a full model; the special case of a strictified model, where a
term is presented by its code, is `Start/CwaLcccOfPi.lean`.

Main definitions:

* `Cwa.HomOver σ B` — the maps into the extended context `Γ.B` lying over `σ`;
* `Cwa.homOverEquivTm` — **they are the terms of the substituted type**.

Main results:

* `Cwa.homOverEquivTm_symm_precomp` — precomposing the map of a term is substituting the term;
* `Cwa.PiStruct.lam_tmCast`, `Cwa.Pi_congr`, `Cwa.NaturalPiStruct.lam_tmSub_eqToHom` — abstraction
  commutes with the transports along equalities of types.
-/

import Start.CwaSubFunctorial
import Start.CwaVar

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-! ### Transport of terms -/

/-- Transport of terms along an equality of types, as a bijection. -/
def tmCastEquiv {Γ : C} {A A' : T.Ty Γ} (h : A = A') : T.Tm Γ A ≃ T.Tm Γ A' where
  toFun := tmCast h
  invFun := tmCast h.symm
  left_inv _ := by cases h; rfl
  right_inv _ := by cases h; rfl

@[simp] theorem tmCastEquiv_apply {Γ : C} {A A' : T.Ty Γ} (h : A = A') (a : T.Tm Γ A) :
    tmCastEquiv (T := T) h a = tmCast h a := rfl

/-! ### Maps over a substitution -/

/-- A **map over `σ` into the display map of `B`**: a morphism into the extended context `Γ.B`
whose composite with the display map is `σ`. -/
def HomOver {Γ Δ : C} (σ : Δ ⟶ Γ) (B : T.Ty Γ) : Type v :=
  {k : Δ ⟶ T.ext Γ B // k ≫ T.disp B = σ}

namespace HomOver

@[ext] theorem ext' {Γ Δ : C} {σ : Δ ⟶ Γ} {B : T.Ty Γ} {k l : HomOver (T := T) σ B}
    (h : k.1 = l.1) : k = l := Subtype.ext h

end HomOver

/-- **A term of a substituted type is determined by the map over `σ` it induces**: both are
sections of the same display map, so the universal property of the extension square applies. -/
theorem tm_eq_of_extend_eq {Γ Δ : C} (σ : Δ ⟶ Γ) (B : T.Ty Γ) {x y : T.Tm Δ (T.tySub σ B)}
    (hxy : x.1 ≫ T.extend σ B = y.1 ≫ T.extend σ B) : x = y :=
  Tm.ext' ((T.isPullback σ B).hom_ext hxy (by rw [x.2, y.2]))

/-- **A map over `σ` into the display map of `B` is a term of `B[σ]`.**  Both are, by the universal
property of the extension square, the same datum. -/
noncomputable def homOverEquivTm {Γ Δ : C} (σ : Δ ⟶ Γ) (B : T.Ty Γ) :
    HomOver (T := T) σ B ≃ T.Tm Δ (T.tySub σ B) where
  toFun k := ⟨(T.isPullback σ B).lift k.1 (𝟙 Δ) (by rw [k.2, Category.id_comp]),
    (T.isPullback σ B).lift_snd _ _ _⟩
  invFun a := ⟨a.1 ≫ T.extend σ B, by
    rw [Category.assoc, (T.isPullback σ B).w, ← Category.assoc, a.2, Category.id_comp]⟩
  left_inv k := Subtype.ext ((T.isPullback σ B).lift_fst _ _ _)
  right_inv a := Tm.ext' ((T.isPullback σ B).hom_ext
    (((T.isPullback σ B).lift_fst _ _ _).trans rfl)
    (((T.isPullback σ B).lift_snd _ _ _).trans a.2.symm))

@[simp] theorem homOverEquivTm_symm_val {Γ Δ : C} (σ : Δ ⟶ Γ) (B : T.Ty Γ)
    (a : T.Tm Δ (T.tySub σ B)) :
    ((homOverEquivTm (T := T) σ B).symm a).1 = a.1 ≫ T.extend σ B := rfl

/-- The map of a term, read along an equality of substitutions. -/
theorem homOverEquivTm_symm_congr {Γ Δ : C} {σ σ' : Δ ⟶ Γ} (hσ : σ = σ') (B : T.Ty Γ)
    (a : T.Tm Δ (T.tySub σ B)) :
    ((homOverEquivTm (T := T) σ' B).symm
        (tmCast (congrArg (fun m => T.tySub m B) hσ) a)).1
      = ((homOverEquivTm (T := T) σ B).symm a).1 := by
  cases hσ; rfl

/-- **Precomposing the map of a term is substituting the term.** -/
theorem homOverEquivTm_symm_precomp (co : ExtCoherent T) {Γ Δ Δ' : C} (σ : Δ ⟶ Γ) (t : Δ' ⟶ Δ)
    (B : T.Ty Γ) (a : T.Tm Δ (T.tySub σ B)) :
    ((homOverEquivTm (T := T) (t ≫ σ) B).symm
        (tmCast (T.tySub_comp σ t B).symm (T.tmSub t a))).1
      = t ≫ ((homOverEquivTm (T := T) σ B).symm a).1 := by
  rw [homOverEquivTm_symm_val, homOverEquivTm_symm_val, tmCast_val, co.extend_comp σ t B,
    Category.assoc, ← Category.assoc (eqToHom _), eqToHom_trans, eqToHom_refl, Category.id_comp,
    ← Category.assoc, tmSub_extend t a, Category.assoc]

/-- **The map of a substituted term is the precomposed map**, in the form in which the composite
substitution and the substituted type are given by equalities. -/
theorem tmCast_tmSub_extend (co : ExtCoherent T) {Γ Δ Δ' : C} (σ : Δ ⟶ Γ) (s : Δ' ⟶ Δ)
    {σ' : Δ' ⟶ Γ} (hσ : s ≫ σ = σ') (B : T.Ty Γ) (a : T.Tm Δ (T.tySub σ B))
    (hB : T.tySub s (T.tySub σ B) = T.tySub σ' B) :
    (tmCast hB (T.tmSub s a)).1 ≫ T.extend σ' B = s ≫ a.1 ≫ T.extend σ B := by
  subst hσ
  exact homOverEquivTm_symm_precomp co σ s B a

/-! ### Transports and the Π-structure -/

/-- Abstraction commutes with the transport of the body along an equality of types. -/
theorem PiStruct.lam_tmCast (P : PiStruct T) {Γ : C} {A : T.Ty Γ} {B B' : T.Ty (T.ext Γ A)}
    (h : B = B') (b : T.Tm (T.ext Γ A) B) :
    P.lam (tmCast h b) = tmCast (congrArg (P.Pi A) h) (P.lam b) := by
  cases h; rfl

/-- The dependent product is congruent: equal domains and bodies give equal products. -/
theorem Pi_congr (P : PiStruct T) {Γ : C} {A A' : T.Ty Γ} (hA : A' = A) {B : T.Ty (T.ext Γ A)}
    {B' : T.Ty (T.ext Γ A')} (hB : T.tySub (eqToHom (congrArg (T.ext Γ) hA)) B = B') :
    P.Pi A B = P.Pi A' B' := by
  cases hA
  have hBB : B' = B := by
    refine hB.symm.trans ?_
    rw [eqToHom_refl, T.tySub_id]
  rw [hBB]

/-- Abstraction commutes with the transport of the domain along an equality of types. -/
theorem NaturalPiStruct.lam_tmSub_eqToHom (co : ExtCoherent T) (P : NaturalPiStruct T) {Γ : C}
    {A A' : T.Ty Γ} (hA : A' = A) {B : T.Ty (T.ext Γ A)} (x : T.Tm (T.ext Γ A) B)
    (hPi : P.Pi A' (T.tySub (eqToHom (congrArg (T.ext Γ) hA)) B) = P.Pi A B) :
    tmCast hPi (P.lam (T.tmSub (eqToHom (congrArg (T.ext Γ) hA)) x)) = P.lam x := by
  cases hA
  simp only [eqToHom_refl] at hPi ⊢
  have h3 : T.tmSub (𝟙 (T.ext Γ A)) x = tmCast (T.tySub_id B).symm x := by
    have h2 := co.tmSub_id (T := T) x
    rw [tmCast_eq_iff] at h2
    exact h2
  rw [h3, PiStruct.lam_tmCast P.toPiStruct (T.tySub_id B).symm x, tmCast_trans]
  rfl

end Cwa
