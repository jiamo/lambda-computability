/-
**The syntax of `λΠ` is a model of `λΠ`.**

`Start/LambdaPiInterp.lean` interprets the calculus in an arbitrary `LambdaPi.Model`, and
`Start/LambdaPiInterpTotal.lean` shows the interpretation is total on derivations, in a model whose
product former is injective.  This file exhibits such a model: the syntactic one, so that those
theorems are not vacuous.

* `LambdaPiUniv.rep` — the raw term representing a term of the syntactic model, and
  `LambdaPiUniv.eq_of_rep_conv` — two terms with convertible representatives are equal;
* `LambdaPiUniv.rep_lamQ`, `LambdaPiUniv.rep_appQ` — the representatives of abstraction and
  application are the abstraction and the application of the calculus;
* `LambdaPiUniv.lamQ_sub`, `LambdaPiUniv.appQ_sub` — **abstraction and application are natural in
  the context**, which is the law an interpretation of a calculus with substitution needs;
* `LambdaPiUniv.piQ_inj` — **the product former of the syntax is injective**, by injectivity of `Π`
  for conversion (`LambdaPi.pi_inj_left`, `LambdaPi.pi_inj_right`);
* `LambdaPiUniv.syntacticModel` — **the syntax of `λΠ` is a model of `λΠ`**, and
  `LambdaPiUniv.syntacticModel_piInj` — one with injective products.
-/

import Start.CwaSmall
import Start.LambdaPiInterpTotal

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory Limits

namespace LambdaPiUniv

open LambdaPi LambdaPiCat LambdaPiFull

/-! ### Representatives of terms -/

/-- The raw term representing a term of the syntactic model. -/
noncomputable def rep {Γ : Ob} {A : TyQ Γ} (x : Cwa.Tm syntactic Γ A) : Tm :=
  (tmEquiv A x).out.tm

/-- The representative of a term is a term of the represented type. -/
theorem rep_ok {Γ : Ob} {A : TyQ Γ} (x : Cwa.Tm syntactic Γ A) :
    Typing Γ.ctx (rep x) A.rep.ty := (tmEquiv A x).out.ok

/-- **A term of the syntactic model is determined by its representative**, up to conversion. -/
theorem eq_of_rep_conv {Γ : Ob} {A : TyQ Γ} {x y : Cwa.Tm syntactic Γ A}
    (h : Conv (rep x) (rep y)) : x = y := by
  have hx : tmMk (tmEquiv A x).out = tmEquiv A x := Quotient.out_eq _
  have hy : tmMk (tmEquiv A y).out = tmEquiv A y := Quotient.out_eq _
  have hxy : tmEquiv A x = tmEquiv A y := by
    rw [← hx, ← hy]
    exact Quotient.sound h
  exact (tmEquiv A).injective hxy

/-- The representative of a term whose class is known. -/
theorem rep_conv_of_eq {Γ : Ob} {A : TyQ Γ} {x : Cwa.Tm syntactic Γ A} {t : TmOf Γ A.rep.ty}
    (h : tmEquiv A x = tmMk t) : Conv (rep x) t.tm := by
  rw [rep, h]
  exact Quotient.exact (Quotient.out_eq (tmMk t))

/-- Transporting a term along an equality of types does not change its representative. -/
theorem rep_tmCast {Γ : Ob} {A B : TyQ Γ} (h : A = B) (x : Cwa.Tm syntactic Γ A) :
    rep (Cwa.tmCast h x) = rep x := by
  cases h
  rfl

/-- **The representative of a substituted term is the substituted representative.** -/
theorem rep_tmSub {Γ Δ : Ob} (σ : Δ ⟶ Γ) {A : TyQ Γ} (x : Cwa.Tm syntactic Γ A) :
    Conv (rep (Cwa.tmSub (T := syntactic) σ x)) (subst σ.out.sub (rep x)) :=
  tmEquiv_tmSub_conv σ A x

/-- A type of the syntactic model is determined by its representative. -/
theorem tyQ_eq_of_rep {Γ : Ob} {A B : TyQ Γ} (hs : A.rep.srt = B.rep.srt)
    (h : Conv A.rep.ty B.rep.ty) : A = B := by
  conv_lhs => rw [← Quotient.out_eq A]
  conv_rhs => rw [← Quotient.out_eq B]
  exact tyMk_eq hs h

/-- The representative of an abstraction is an abstraction. -/
theorem rep_lamQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (b : Cwa.Tm syntactic (extOb Γ (elQ a)) B) :
    Conv (rep (smallPi.lam b)) (Tm.lam (elQ a).rep.ty (rep b)) := by
  refine rep_conv_of_eq (t := ⟨Tm.lam (elQ a).rep.ty (rep b),
    (Typing.lam (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (rep_ok b)).conv (piQ a B).rep.ok
      (piQ_rep_conv a B).symm⟩) ?_
  have h1 : tmEquiv (piQ a B) (smallPi.lam b)
      = tmConvEquiv (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (piQ a B).rep.ok
          (piQ_rep_conv a B).symm
          (lamTm (elQ a).rep.ok (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (tmEquiv B b)) :=
    Equiv.apply_symm_apply _ _
  rw [h1]
  conv_lhs => rw [show tmEquiv B b = tmMk (tmEquiv B b).out from (Quotient.out_eq _).symm]
  rfl

/-- The representative of an application is an application to the generic argument. -/
theorem rep_appQ {Γ : Ob} {a : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    (f : Cwa.Tm syntactic Γ (smallPi.Pi a B)) :
    Conv (rep (smallPi.app f)) (Tm.app (shift (rep f)) (Tm.var 0)) := by
  have hf0 : Typing Γ.ctx (rep f) (Tm.pi (elQ a).rep.ty B.rep.ty) :=
    (rep_ok f).conv (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (piQ_rep_conv a B)
  have hap : Typing (extOb Γ (elQ a)).ctx (Tm.app (shift (rep f)) (Tm.var 0)) B.rep.ty := by
    have hw := hf0.weaken (elQ a).rep.ty
    have h0 : Typing ((elQ a).rep.ty :: Γ.ctx) (Tm.var 0) (shift (elQ a).rep.ty) :=
      Typing.var (Lookup.zero _ _)
    have hres := Typing.app hw h0
    rwa [inst_upr_shift] at hres
  refine rep_conv_of_eq (t := ⟨Tm.app (shift (rep f)) (Tm.var 0), hap⟩) ?_
  have h1 : tmEquiv B (smallPi.app f)
      = appTm (elQ a).rep.ok
          ((tmConvEquiv (Typing.pi rfl (elQ_rep_ok a) B.rep.ok) (piQ a B).rep.ok
            (piQ_rep_conv a B).symm).symm (tmEquiv (piQ a B) f)) :=
    Equiv.apply_symm_apply _ _
  rw [h1]
  conv_lhs =>
    rw [show tmEquiv (piQ a B) f = tmMk (tmEquiv (piQ a B) f).out from (Quotient.out_eq _).symm]
  rfl

/-! ### Naturality of abstraction and application -/

/-- **Abstraction is natural in the context.** -/
theorem lamQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ))
    (B : TyQ (extOb Γ (elQ a))) (b : Cwa.Tm syntactic (extOb Γ (elQ a)) B) :
    Cwa.tmCast (smallPi.Pi_sub σ a B) (Cwa.tmSub (T := syntactic) σ (smallPi.lam b))
      = smallPi.lam (Cwa.tmSub (T := syntactic) (univ.extHom σ a) b) := by
  refine eq_of_rep_conv ?_
  rw [rep_tmCast]
  refine (rep_tmSub σ (smallPi.lam b)).trans ?_
  refine Conv.trans ((rep_lamQ b).subst σ.out.sub) ?_
  refine Conv.trans ?_ (rep_lamQ (Cwa.tmSub (T := syntactic) (univ.extHom σ a) b)).symm
  rw [subst_lam]
  refine Conv.lam ?_ ?_
  · have hc := tySubQ_rep_conv σ (elQ a)
    rw [elQ_sub σ a] at hc
    exact hc.symm
  · refine Conv.trans (conv_subst_congr ((rep_ok b).bnd_of_wf (extOb Γ (elQ a)).wf).1
      (fun n hn => (extHom_out_conv σ a hn).symm)) ?_
    exact (rep_tmSub (univ.extHom σ a) b).symm

/-- **Application is natural in the context.** -/
theorem appQ_sub {Γ Δ : Ob} (σ : Δ ⟶ Γ) (a : Cwa.Tm syntactic Γ (uQ Γ))
    (B : TyQ (extOb Γ (elQ a))) (f : Cwa.Tm syntactic Γ (smallPi.Pi a B)) :
    Cwa.tmSub (T := syntactic) (univ.extHom σ a) (smallPi.app f)
      = smallPi.app (Cwa.tmCast (smallPi.Pi_sub σ a B) (Cwa.tmSub (T := syntactic) σ f)) := by
  have hlen : (extOb Γ (elQ a)).ctx.length = Γ.ctx.length + 1 := rfl
  refine eq_of_rep_conv ?_
  refine (rep_tmSub (univ.extHom σ a) (smallPi.app f)).trans ?_
  refine Conv.trans ((rep_appQ f).subst (univ.extHom σ a).out.sub) ?_
  refine Conv.trans ?_
    (rep_appQ (Cwa.tmCast (smallPi.Pi_sub σ a B) (Cwa.tmSub (T := syntactic) σ f))).symm
  rw [rep_tmCast, subst_app]
  refine Conv.app ?_ ?_
  · rw [subst_shift', shift]
    refine Conv.trans ?_ (((rep_tmSub σ f).rename Nat.succ).symm)
    rw [rename_subst]
    refine conv_subst_congr ((rep_ok f).bnd_of_wf Γ.wf).1 (fun n hn => ?_)
    exact extHom_out_conv σ a (by rw [hlen]; omega)
  · exact extHom_out_conv σ a (by rw [hlen]; omega)

/-! ### Injectivity of the product -/

/-- **The product former of the syntax is injective**: a product determines the code of its domain
and its body. -/
theorem piQ_inj {Γ : Ob} {a a' : Cwa.Tm syntactic Γ (uQ Γ)} {B : TyQ (extOb Γ (elQ a))}
    {B' : TyQ (extOb Γ (elQ a'))} (h : piQ a B = piQ a' B') :
    (⟨a, B⟩ : (c : Cwa.Tm syntactic Γ (uQ Γ)) × TyQ (extOb Γ (elQ c))) = ⟨a', B'⟩ := by
  have hmid : Conv (piQ a B).rep.ty (piQ a' B').rep.ty := by rw [h]; exact Conv.refl _
  have hconv : Conv (Tm.pi (elQ a).rep.ty B.rep.ty) (Tm.pi (elQ a').rep.ty B'.rep.ty) :=
    ((piQ_rep_conv a B).symm.trans hmid).trans (piQ_rep_conv a' B')
  have hel : elQ a = elQ a' :=
    tyQ_eq_of_rep (by rw [elQ_rep_srt, elQ_rep_srt]) (pi_inj_left hconv)
  have haa : a = a' := elQ_injective hel
  subst haa
  have hsrt : B.rep.srt = B'.rep.srt := by
    have h1 := piQ_rep_srt a B
    rw [h, piQ_rep_srt a B'] at h1
    exact h1.symm
  have hBB : B = B' := tyQ_eq_of_rep hsrt (pi_inj_right hconv)
  subst hBB
  rfl

/-! ### The syntactic model -/

/-- **The syntax of `λΠ` is a model of `λΠ`**: the category of contexts and substitutions, with the
sort `∗` as its universe of small types, the product rules as its dependent product, the codes of
the rule `(∗,∗)`, and the empty context as its terminal object. -/
noncomputable def syntacticModel : LambdaPi.Model.{0, 0, 0} Ob where
  T := syntactic
  co := extCoherent_syntactic
  Un := univ
  SP := smallPi
  PC := naturalPiClosed
  emp := empty
  empIsTerminal := emptyIsTerminal
  lam_sub := lamQ_sub
  app_sub := appQ_sub

/-- **The syntactic model has injective products**, so the interpretation into it is functional and
total on derivations. -/
theorem syntacticModel_piInj : syntacticModel.PiInj := fun h => piQ_inj h

/-- **The interpretation of `λΠ` in a model is not vacuous**: in the syntactic model every
well-formed context is interpreted, and every derivable term denotes exactly one term of it. -/
theorem syntactic_interp_exists_unique {Γ : Ctx} {t A : Tm} (h : Typing Γ t A)
    (hA : A ≠ Tm.sort Srt.box) {Γ' : Ob} {sc : LambdaPi.SemCtx syntacticModel Γ'}
    (hc : LambdaPi.CtxI Γ sc) :
    ∃! p : LambdaPi.TmVal syntacticModel Γ', LambdaPi.TmI sc t p.1 p.2 :=
  LambdaPi.interp_exists_unique syntacticModel_piInj h hA hc

/-- Every well-formed context of `λΠ` is interpreted in the syntactic model. -/
theorem syntactic_ctxI_total {Γ : Ctx} (h : Wf Γ) :
    ∃ (Γ' : Ob) (sc : LambdaPi.SemCtx syntacticModel Γ'), LambdaPi.CtxI Γ sc :=
  LambdaPi.CtxI.total syntacticModel_piInj h

end LambdaPiUniv
