/-
**The generic term is natural in the context.**

In a category with attributes the term `Cwa.var A` of `Start/Cwa.lean` is the de Bruijn variable
`0`: the generic term of `A` in the extended context.  Substitution acts on terms by the universal
property of context extension, and the law an interpretation of a calculus with de Bruijn indices
needs is that the generic term is *preserved* by the action of a substitution on extended contexts,
`q[σ⁺] = q`.

* `Cwa.extend_congr` — the action of a substitution on extended contexts is transported along an
  equality of substitutions;
* `Cwa.tySub_extend_var_ty` — the two types involved are equal, by the commutativity of the
  extension square;
* `Cwa.ExtCoherent.tmSub_extend_var` — and the two terms are equal, in a model whose substitution
  of terms is functorial (`Cwa.ExtCoherent`).  Both sides are maps into a pullback and are compared
  with the two legs of the extension square of `Start/Cwa.lean`; the composite of the two actions
  is computed by the coherence law.

The dual law is the one that interprets the *instantiation* of the last variable of a context by a
term: a term of `A` is a section of the display map of `A`, and

* `Cwa.ExtCoherent.tmSub_sec_var` — substituting the generic term along that section returns the
  term itself, so that instantiation is substitution along the section.
-/

import Start.CwaSubFunctorial

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- The pair of a type and a term of it: the *value* of a term of the calculus. -/
abbrev Val (T : Cwa.{u, v, w} C) (Γ : C) : Type max v w := (A : T.Ty Γ) × T.Tm Γ A

/-- Substitution acting on a value. -/
noncomputable def Val.sub {Γ Δ : C} (σ : Δ ⟶ Γ) (p : Val T Γ) : Val T Δ :=
  ⟨T.tySub σ p.1, T.tmSub σ p.2⟩

/-- A value is unchanged when its type is replaced by an equal one and its term transported. -/
theorem Val.mk_tmCast {Γ : C} {A A' : T.Ty Γ} (h : A = A') (x : T.Tm Γ A) :
    (⟨A, x⟩ : Val T Γ) = ⟨A', tmCast h x⟩ := by
  cases h; rfl

/-- Substituting a composite in a value is substituting twice. -/
theorem ExtCoherent.val_sub_comp (co : ExtCoherent T) {Γ Δ Θ : C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (p : Val T Γ) : Val.sub τ (Val.sub σ p) = Val.sub (τ ≫ σ) p := by
  rw [Val.sub, Val.sub, Val.sub,
    Val.mk_tmCast (T.tySub_comp σ τ p.1) (T.tmSub (τ ≫ σ) p.2), co.tmSub_comp]

/-- The generic term, composed with the action of the display map on extended contexts, is the
identity: this is the first leg of the lift defining `Cwa.var`. -/
theorem var_extend {Γ : C} (A : T.Ty Γ) :
    (Cwa.var A).1 ≫ T.extend (T.disp A) A = 𝟙 (T.ext Γ A) :=
  (T.isPullback (T.disp A) A).lift_fst _ _ _

/-- The action on extended contexts, transported along an equality of substitutions. -/
theorem extend_congr {Γ Δ : C} {m m' : Δ ⟶ Γ} (h : m = m') (A : T.Ty Γ) :
    T.extend m A = eqToHom (congrArg (fun k => T.ext Δ (T.tySub k A)) h) ≫ T.extend m' A := by
  subst h; simp

/-- The type of the generic term is stable under the action of a substitution on extended
contexts. -/
theorem tySub_extend_var_ty {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) :
    T.tySub (T.extend σ A) (T.tySub (T.disp A) A)
      = T.tySub (T.disp (T.tySub σ A)) (T.tySub σ A) := by
  rw [← T.tySub_comp, ← T.tySub_comp, (T.isPullback σ A).w]

/-- The composite of the two actions on extended contexts, over the extension square: acting by
`σ⁺` and then weakening is weakening followed by acting by `σ`. -/
theorem ExtCoherent.extend_extend (co : ExtCoherent T) {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) :
    T.extend (T.extend σ A) (T.tySub (T.disp A) A) ≫ T.extend (T.disp A) A
      = eqToHom (congrArg (T.ext (T.ext Δ (T.tySub σ A))) (tySub_extend_var_ty σ A))
          ≫ T.extend (T.disp (T.tySub σ A)) (T.tySub σ A) ≫ T.extend σ A := by
  have h1 := co.extend_comp (T.disp A) (T.extend σ A) A
  have h2 := co.extend_comp σ (T.disp (T.tySub σ A)) A
  have hw : T.extend σ A ≫ T.disp A = T.disp (T.tySub σ A) ≫ σ := (T.isPullback σ A).w
  have h3 := extend_congr (T := T) hw A
  rw [h2] at h3
  rw [h1] at h3
  -- `h3` computes both composites; the transports along equalities of types collapse
  have h4 : T.extend (T.extend σ A) (T.tySub (T.disp A) A) ≫ T.extend (T.disp A) A
      = eqToHom (congrArg (T.ext (T.ext Δ (T.tySub σ A)))
            (T.tySub_comp (T.disp A) (T.extend σ A) A)).symm ≫
        (eqToHom (congrArg (fun k => T.ext (T.ext Δ (T.tySub σ A)) (T.tySub k A)) hw) ≫
          eqToHom (congrArg (T.ext (T.ext Δ (T.tySub σ A)))
            (T.tySub_comp σ (T.disp (T.tySub σ A)) A)) ≫
          T.extend (T.disp (T.tySub σ A)) (T.tySub σ A) ≫ T.extend σ A) := by
    rw [← h3]
    simp
  rw [h4]
  simp

/-- **The generic term is natural**: substituting the de Bruijn variable `0` along the action of a
substitution on extended contexts gives the de Bruijn variable `0` again. -/
theorem ExtCoherent.tmSub_extend_var (co : ExtCoherent T) {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) :
    tmCast (tySub_extend_var_ty σ A) (T.tmSub (T.extend σ A) (Cwa.var A))
      = Cwa.var (T.tySub σ A) := by
  rw [tmCast_eq_iff]
  refine (tmSub_eq_of (T.extend σ A) (Cwa.var A) _ ?_).symm
  refine (T.isPullback (T.disp A) A).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, var_extend, Category.comp_id, tmCast_val,
      Category.assoc, co.extend_extend σ A]
    slice_lhs 2 3 => rw [eqToHom_trans]
    simp only [eqToHom_refl, Category.id_comp, ← Category.assoc, var_extend]
  · rw [Category.assoc, Category.assoc, (Cwa.var A).2, Category.comp_id, tmCast_val,
      Category.assoc, (T.isPullback (T.extend σ A) (T.tySub (T.disp A) A)).w,
      eqToHom_ext_disp_assoc, ← Category.assoc, (Cwa.var (T.tySub σ A)).2, Category.id_comp]
    exact (tySub_extend_var_ty σ A).symm

/-- **The value of the generic term is stable** under the action of a substitution on extended
contexts. -/
theorem ExtCoherent.val_sub_var (co : ExtCoherent T) {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) :
    Val.sub (T.extend σ A) ⟨T.tySub (T.disp A) A, Cwa.var A⟩
      = ⟨T.tySub (T.disp (T.tySub σ A)) (T.tySub σ A), Cwa.var (T.tySub σ A)⟩ := by
  rw [Val.sub, Val.mk_tmCast (tySub_extend_var_ty σ A), co.tmSub_extend_var]

/-- The same, for the action written with a type *equal* to the substituted one — the form in
which the extension square of a decoded code appears (`Cwa.Universe.extHom`). -/
theorem ExtCoherent.val_sub_var_of_eq (co : ExtCoherent T) {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ)
    {A' : T.Ty Δ} (e : T.tySub σ A = A') :
    Val.sub (eqToHom (congrArg (T.ext Δ) e).symm ≫ T.extend σ A)
        ⟨T.tySub (T.disp A) A, Cwa.var A⟩
      = ⟨T.tySub (T.disp A') A', Cwa.var A'⟩ := by
  cases e
  simpa using co.val_sub_var σ A

/-! ### Substitution along the section defined by a term -/

/-- The type of the generic term, substituted along the section a term defines, is that type
again. -/
theorem tySub_sec_var_ty {Γ : C} {A : T.Ty Γ} (g : T.Tm Γ A) :
    T.tySub g.1 (T.tySub (T.disp A) A) = A := by
  rw [← T.tySub_comp, g.2, T.tySub_id]

/-- The action of a section on extended contexts, followed by weakening, is the transport along
the equality of types it induces. -/
theorem ExtCoherent.extend_sec (co : ExtCoherent T) {Γ : C} {A : T.Ty Γ} (g : T.Tm Γ A) :
    T.extend g.1 (T.tySub (T.disp A) A) ≫ T.extend (T.disp A) A
      = eqToHom (congrArg (T.ext Γ) (tySub_sec_var_ty g)) := by
  have hg : g.1 ≫ T.disp A = 𝟙 Γ := g.2
  have h := co.extend_comp (T.disp A) g.1 A
  rw [extend_congr hg A, co.extend_id] at h
  have h2 : T.extend g.1 (T.tySub (T.disp A) A) ≫ T.extend (T.disp A) A
      = eqToHom (congrArg (T.ext Γ) (T.tySub_comp (T.disp A) g.1 A)).symm ≫
        eqToHom (congrArg (fun k => T.ext Γ (T.tySub k A)) hg) ≫
          eqToHom (congrArg (T.ext Γ) (T.tySub_id A)) := by
    rw [h]
    simp
  rw [h2]
  simp

/-- **The generic term, substituted along the section a term defines, is that term.**  This is the
law that makes instantiating the last variable of a context by a term correspond to substituting
along the section. -/
theorem ExtCoherent.tmSub_sec_var (co : ExtCoherent T) {Γ : C} {A : T.Ty Γ} (g : T.Tm Γ A) :
    tmCast (tySub_sec_var_ty g) (T.tmSub g.1 (Cwa.var A)) = g := by
  rw [tmCast_eq_iff]
  refine (tmSub_eq_of g.1 (Cwa.var A) _ ?_).symm
  refine (T.isPullback (T.disp A) A).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, var_extend, Category.comp_id, co.extend_sec g,
      tmCast_val, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · rw [Category.assoc, Category.assoc, (Cwa.var A).2, Category.comp_id,
      (T.isPullback g.1 (T.tySub (T.disp A) A)).w, ← Category.assoc,
      (tmCast (tySub_sec_var_ty g).symm g).2, Category.id_comp]

/-- The value of the generic term, substituted along the section a term defines. -/
theorem ExtCoherent.val_sub_sec_var (co : ExtCoherent T) {Γ : C} {A : T.Ty Γ} (g : T.Tm Γ A) :
    Val.sub g.1 (⟨T.tySub (T.disp A) A, Cwa.var A⟩ : Val T (T.ext Γ A)) = ⟨A, g⟩ := by
  rw [Val.sub, Val.mk_tmCast (tySub_sec_var_ty g), co.tmSub_sec_var]

/-- Substituting the identity in a value does nothing. -/
theorem ExtCoherent.val_sub_id (co : ExtCoherent T) {Γ : C} (p : Val T Γ) :
    Val.sub (𝟙 Γ) p = p := by
  rw [Val.sub, Val.mk_tmCast (T.tySub_id p.1), co.tmSub_id]

end Cwa
