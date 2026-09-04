/-
**Application is preserved by the interpretation.**

`Start/LambdaPiInitialUniv.lean` proves that the comparison morphism out of the syntactic model of
`λΠ` preserves the universe, the products over the small types, their codes and abstraction.  The
one clause a *morphism of models* (`LambdaPi.ModelHom`) still asks for is that **application** be
preserved, and that is what this module supplies.

The syntactic application is taken in the generic-argument form: the representative of
`smallPi.app f` is `f` weakened past the new variable and applied to the variable `0`.  So the
semantic fact needed is the "weaken, then instantiate at the generic argument" law:

* `LambdaPi.tmCast_extHom_var` — the section defined by the generic argument undoes the action of
  the display map on extended contexts;
* `LambdaPi.val_app_weaken` — applying the weakening of `f` to the generic argument returns the
  generic application of `f`;
* `LambdaPi.TmI.app_shift_var` — hence the raw term `(shift t) (var 0)` denotes the generic
  application of whatever `t` denotes, and
* `LambdaPiInitial.tmMap_appQ` — **application is preserved** by the comparison morphism.
-/

import Start.LambdaPiInitialUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### Weakening, undone by the generic argument -/

/-- **The section defined by the generic argument undoes weakening**: composing it with the action
of the display map on extended contexts gives the identity. -/
theorem tmCast_extHom_var {Γ : C} (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a) (Cwa.var (M.Un.El a))).1
        ≫ M.Un.extHom (M.T.disp (M.Un.El a)) a
      = 𝟙 (M.T.ext Γ (M.Un.El a)) := by
  rw [Cwa.tmCast_val, Cwa.Universe.extHom, Category.assoc, ← Category.assoc (eqToHom _),
    eqToHom_trans, eqToHom_refl, Category.id_comp, Cwa.var_extend]

/-- **Applying the weakening of `f` to the generic argument returns the generic application of
`f`.**  Both the type and the term are compared, as a value. -/
theorem val_app_weaken {Γ : C} (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) (f : Cwa.Tm M.T Γ (M.SP.Pi a B)) :
    (⟨M.T.tySub (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a)
            (Cwa.var (M.Un.El a))).1
          (M.T.tySub (M.Un.extHom (M.T.disp (M.Un.El a)) a) B),
        M.T.tmSub (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a)
            (Cwa.var (M.Un.El a))).1
          (M.SP.app (Cwa.tmCast (M.SP.Pi_sub (M.T.disp (M.Un.El a)) a B)
            (M.T.tmSub (M.T.disp (M.Un.El a)) f)))⟩ : TmVal M (M.T.ext Γ (M.Un.El a)))
      = ⟨B, M.SP.app f⟩ := by
  rw [← M.app_sub (M.T.disp (M.Un.El a)) a B f]
  have hval : (⟨M.T.tySub (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a)
            (Cwa.var (M.Un.El a))).1
          (M.T.tySub (M.Un.extHom (M.T.disp (M.Un.El a)) a) B),
        M.T.tmSub (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a)
            (Cwa.var (M.Un.El a))).1
          (M.T.tmSub (M.Un.extHom (M.T.disp (M.Un.El a)) a)
            (M.SP.app f))⟩ : TmVal M (M.T.ext Γ (M.Un.El a)))
      = Cwa.Val.sub (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a)
            (Cwa.var (M.Un.El a))).1
          (Cwa.Val.sub (M.Un.extHom (M.T.disp (M.Un.El a)) a) ⟨B, M.SP.app f⟩) := rfl
  rw [hval, M.co.val_sub_comp, tmCast_extHom_var a, M.co.val_sub_id]

/-- **The raw term `(shift t) (var 0)` denotes the generic application** of whatever `t` denotes:
this is the semantic reading of the generic-argument form of application. -/
theorem TmI.app_shift_var {Γ : C} {s : SemCtx M Γ} {t : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
    {B : M.T.Ty (M.T.ext Γ (M.Un.El a))} {f : Cwa.Tm M.T Γ (M.SP.Pi a B)}
    (h : TmI s t (M.SP.Pi a B) f) :
    TmI (s.cons (M.Un.El a)) (Tm.app (shift t) (Tm.var 0)) B (M.SP.app f) := by
  have hw := (h.weaken (M.Un.El a)).cast (M.SP.Pi_sub (M.T.disp (M.Un.El a)) a B)
  have hvar : TmI (s.cons (M.Un.El a)) (Tm.var 0)
      (M.Un.El (M.Un.sub (M.T.disp (M.Un.El a)) a))
      (Cwa.tmCast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a) (Cwa.var (M.Un.El a))) :=
    (TmI.var rfl).cast (M.Un.El_sub' (M.T.disp (M.Un.El a)) a)
  exact (TmI.app hw hvar).cast_val (val_app_weaken a B f)

end LambdaPi

namespace LambdaPiInitial

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

variable (hinj : M.PiInj)

/-- **Application is preserved by the comparison morphism**: the image of the generic application
of `f`, read in the compared extended context, is the generic application of the image of `f`. -/
theorem tmMap_appQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (f : Cwa.Tm syntactic Γ (smallPi.Pi a B)) :
    M.T.tmSub ((mor_preservesUniverse hinj).extElIso a).inv
        ((mor hinj).tmMap (smallPi.app f))
      = M.SP.app (Cwa.tmCast (tyMap_piQ hinj a B) ((mor hinj).tmMap f)) := by
  have hbody := TmI.congr_ctx (ctxI_ext_elQ hinj a) (tmMap_spec hinj B (smallPi.app f))
  rw [← extElIso_inv_eq hinj a] at hbody
  have happ := TmI.app_shift_var ((tmMap_spec hinj (piQ a B) f).cast (tyMap_piQ hinj a B))
  exact eq_of_heq (Sigma.mk.inj_iff.mp (TmI.conv_eq hinj (rep_appQ f) hbody happ)).2

end LambdaPiInitial
